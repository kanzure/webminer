// Copyright (c) 2022 Mark Friedenbach
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#include "wallet.h"

#include "random.h"

#include <fstream>
#include <iostream>
#include <string>

#include <stdint.h>

#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"

#include "boost/filesystem.hpp"
#include "boost/filesystem/fstream.hpp"
#include "boost/interprocess/sync/file_lock.hpp"

#include "sqlite3.h"

static std::string webcash_string(int64_t amount, const absl::string_view& type, const uint256& hash)
{
    if (amount < 0) {
        amount = 0;
    }
    return absl::StrCat("e", std::to_string(amount), ":", type, ":", absl::BytesToHexString(absl::string_view((const char*)hash.data(), hash.size())));
}

std::string to_string(const SecretWebcash& esk)
{
    return webcash_string(esk.amount, "secret", esk.sk);
}

std::string to_string(const PublicWebcash& epk)
{
    return webcash_string(epk.amount, "public", epk.pk);
}

// We group outputs based on their use.  There are currently four categories of
// webcash recognized by the wallet:
enum HashType : int {
    // Pre-generated key that hasn't yet been used for any purpose.  To make
    // backups possible and to minimize the chance of losing funds if/when
    // wallet corruption occurs, the wallet maintains a pool of pre-generated
    // secrets.  These are allocated and used, as needed, in FIFO order.
    UNUSED = -1,

    // Internal webcash generated either to redeem payments or mined webcash,
    // change from a payment, or the consolidation of such outputs.  These
    // outputs count towards the current balance of the wallet, but aren't shown
    // explicitly.
    CHANGE = 0,

    // Outputs added via explicit import.  These are shown as visible, discrete
    // inputs to the wallet.  The wallet always redeems received webcash upon
    // import under the assumption that the imported secret value is still known
    // to others or otherwise not secure.
    RECEIVE = 1,

    // Outputs generated via a mining report.  These are seen as visible inputs
    // to a wallet, aggregated as "mining income."  The wallet always redeems
    // mining inputs for change immediately after generation, in case the mining
    // reports (which contain the secret) are made public.
    MINING = 2,

    // Outputs generated as payments to others.  These are intended to be
    // immediately claimed by the other party, but we keep the key in this
    // wallet in case there are problems completing the transaction.
    PAYMENT = 3,
};

struct WalletOutput {
    int id;
    uint256 hash;
    int64_t amount;
    bool spent;
};

struct WalletSecret {
    int id;
    uint256 secret;
    std::unique_ptr<int> output_id; // foreign key to WalletOutput
    bool mine;
    bool sweep;
};

void Wallet::UpgradeDatabase()
{
    std::array<std::string, 2> tables = {
        "CREATE TABLE IF NOT EXISTS 'output' ("
            "'id' INTEGER PRIMARY KEY NOT NULL,"
            "'hash' BLOB UNIQUE NOT NULL,"
            "'amount' INTEGER NOT NULL,"
            "'spent' INTEGER NOT NULL);",
        "CREATE TABLE IF NOT EXISTS 'secret' ("
            "'id' INTEGER PRIMARY KEY NOT NULL,"
            "'secret' BLOB UNIQUE NOT NULL,"
            "'output_id' INTEGER,"
            "'mine' INTEGER NOT NULL,"
            "'sweep' INTEGER NOT NULL,"
            "FOREIGN KEY('output_id') REFERENCES 'output'('id'));",
    };

    for (const std::string& stmt : tables) {
        sqlite3_stmt* create_table;
        int res = sqlite3_prepare_v2(m_db, stmt.c_str(), stmt.size(), &create_table, nullptr);
        if (res != SQLITE_OK) {
            std::string msg(absl::StrCat("Unable to prepare SQL statement [\"", stmt, "\"]: ", sqlite3_errstr(res), " (", std::to_string(res), ")"));
            std::cerr << msg << std::endl;
            throw std::runtime_error(msg);
        }
        res = sqlite3_step(create_table);
        if (res != SQLITE_DONE) {
            std::string msg(absl::StrCat("Running SQL statement [\"", stmt, "\"] returned unexpected status code: ", sqlite3_errstr(res), " (", std::to_string(res), ")"));
            std::cerr << msg << std::endl;
            sqlite3_finalize(create_table);
            throw std::runtime_error(msg);
        }
        // Returns the same success/error code as the last invocation, so we can
        // ignore the return value here.
        sqlite3_finalize(create_table);
    }
}

Wallet::Wallet(const boost::filesystem::path& path)
    : m_logfile(path)
{
    // The caller can either give the path to one of the wallet files (the
    // recovery log or the sqlite3 database file), or to the shared basename of
    // these files.
    m_logfile.replace_extension(".bak");

    boost::filesystem::path dbfile(path);
    dbfile.replace_extension(".db");
    // Create the database file if it doesn't exist already, so that we can use
    // inter-process file locking primitives on it.  Note that an empty file is
    // a valid, albeit empty sqlite3 database.
    {
        boost::filesystem::ofstream db(dbfile.string(), boost::filesystem::ofstream::app);
        db.flush();
    }
    m_db_lock = boost::interprocess::file_lock(dbfile.c_str());
    if (!m_db_lock.try_lock()) {
        std::string msg("Unable to lock wallet database; wallet is in use by another process.");
        std::cerr << msg << std::endl;
        throw std::runtime_error(msg);
    }

    int error = sqlite3_open_v2(dbfile.c_str(), &m_db, SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE | SQLITE_OPEN_FULLMUTEX | SQLITE_OPEN_EXRESCODE, nullptr);
    if (error != SQLITE_OK) {
        m_db_lock.unlock();
        std::string msg(absl::StrCat("Unable to open/create wallet database file: ", sqlite3_errstr(error), " (", std::to_string(error), ")"));
        std::cerr << msg << std::endl;
        throw std::runtime_error(msg);
    }
    UpgradeDatabase();

    // Touch the wallet file, which will create it if it doesn't already exist.
    // The file locking primitives assume that the file exists, so we need to
    // create here first.  It also allows the user to see the file even before
    // any wallet operations have been performed.
    {
        // This operation isn't protected by a filesystem lock, but that
        // shouldn't be an issue because it doesn't do anything else the file
        // didn't exist in the first place.
        boost::filesystem::ofstream bak(m_logfile.string(), boost::filesystem::ofstream::app);
        if (!bak) {
            sqlite3_close_v2(m_db); m_db = nullptr;
            m_db_lock.unlock();
            std::string msg(absl::StrCat("Unable to open/create wallet recovery file"));
            std::cerr << msg << std::endl;
            throw std::runtime_error(msg);
        }
        bak.flush();
    }
}

Wallet::~Wallet()
{
    // Wait for other threads using the wallet to finish up.
    const std::lock_guard<std::mutex> lock(m_mut);
    // No errors are expected when closing the database file, but if there is
    // then that might be an indication of a serious bug or data loss the user
    // should know about.
    int error = sqlite3_close_v2(m_db); m_db = nullptr;
    if (error != SQLITE_OK) {
        std::cerr << "WARNING: sqlite3 returned error code " << sqlite3_errstr(error) << " (" << std::to_string(error) << ") when attempting to close database file of wallet.  Data loss may have occured." << std::endl;
    }
    // Release our filesystem lock on the wallet.
    m_db_lock.unlock();
}

bool Wallet::Insert(const SecretWebcash& sk, bool mine)
{
    using std::to_string;
    const std::lock_guard<std::mutex> lock(m_mut);
    bool result = true;

    // First write the key to the wallet recovery file
    {
        std::string line = absl::StrCat(mine ? "mining" : "receive", " ", to_string(sk));
        boost::filesystem::ofstream bak(m_logfile.string(), boost::filesystem::ofstream::app);
        if (!bak) {
            std::cerr << "WARNING: Unable to open/create wallet recovery file to save key prior to insertion: \"" << line << "\".  BACKUP THIS KEY NOW TO AVOID DATA LOSS!" << std::endl;
            // We do not return false here even though there was an error writing to
            // the recovery log, because we can still attempt to save the key to the
            // wallet.
            result = false;
        } else {
            bak << line << std::endl;
            bak.flush();
        }
    }

    std::string stmt = absl::StrCat(
        "INSERT INTO 'secret' ('secret', 'output_id', 'mine', 'sweep')",
        "VALUES(x'", absl::BytesToHexString(absl::string_view((const char*)sk.sk.begin(), 32)), "', NULL, ", mine ? "TRUE" : "FALSE", ", TRUE);");
    sqlite3_stmt* insert;
    int res = sqlite3_prepare_v2(m_db, stmt.c_str(), stmt.size(), &insert, nullptr);
    if (res != SQLITE_OK) {
        std::cerr << "Unable to prepare SQL statement [\"" << stmt << "\"]: " << sqlite3_errstr(res) << " (" << std::to_string(res) << ")" << std::endl;
        return false;
    }
    res = sqlite3_step(insert);
    if (res != SQLITE_DONE) {
        std::cerr << "Running SQL statement [\"" << stmt << "\"] returned unexpected status code: " << sqlite3_errstr(res) << " (" << std::to_string(res) << ")" << std::endl;
        result = false;
    }
    sqlite3_finalize(insert);

    return result;
}

// End of File
