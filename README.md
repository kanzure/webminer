# Webminer

An experimental vector-accelerated CPU miner for the Webcash electronic payment network.

Webminer is tested and known to work on recent versions of macOS and Linux.  It is written in a platform-independent style and is likely to work on other operating systems as well.  If you need to make modifications to get it to run in your environment, please consider submitting a pull request on the GitHub repo: https://github.com/maaku/webminer

# Performance

Unlike the official Webcash miner which is written in unoptimized Python, webminer is written in hand-tuned C++ and uses x86 vector SIMD extensions to accelerate SHA256 calculations.  On this author's Intel CPU the official Python miner is able to achieve approximately 31.67 khps.  A single-threaded webminer instance on the same machine is able to mine approximately 416.28 khps, for a total speedup of over 13x.

Further optimizations are possible, and will be implemented in time.

# Compiling

To compile webminer, you need Google's bazel build tool.  Instructions for installing bazel are available at the official bazel website: https://bazel.build

To build webminer, open a shell and navigate to directory containing the source code and execute this command:

```
bazel build -c opt webminer
```

Bazel will handle the details of fetching and compiling all the necessary dependencies.

# Running

The final built executable will be available at `bazel-bin/webminer`.  Simply run this executable and it will begin mining webcash.

The claim codes for mined webcash will be logged both to the stdout (along with lots of other info), and to a dedicated file named 'webcash.log' in the current directory.  If webcash is successfully generated but there is an error communicating to the server, the relevant information (including both the proof-of-work solution and the claim code) are output to a file named 'orphans.log' in the current directory.  The names of both files can be changed with the `--webcashlog=filename` and `--orphanlog=filename` command line options.

Webminer will automatically spawn mining threads equal to the number of execution units on the machine in which it is running.  To control precisely the number of mining threads, use the `--workers=N` option.

WARNING: Do *NOT* execute webminer with with `bazel run`!  Webminer will generate files to store the claim codes for any webcash generated, which will be destroyed along with the temporary sandbox created by `bazel run`.

# Wallet

Webcash claim codes generated by mining need to be inserted into a wallet and replaced quickly, in case the mining submissions are ever released as part of an audit.  Mined webcash can be inserted into any webcash wallet using the official `walletclient.py` tool:

```
cat webcash.log | xargs python path/to/walletclient.py insert
```

Or something similar along those lines.  Note that if *any* of the claim codes are invalid or already used, this will fail.  In that case you will have to resort to making individual requests to the server:

```
cat webcash.log | xargs -n 1 python path/to/walletclient.py insert
```

WARNING: You *must* claim the generated webcash in a wallet quickly after generating them, or else you risk forfeiting the funds if/when your mining report is released.  Mining reports are not treated as sensitive data, so this can happen at any time!

# License

This repository and its source code is distributed under the terms of the Mozilla Public License 2.0.  See MPL-2.0.txt.