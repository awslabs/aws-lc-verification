#!/bin/sh
set -e

mkdir -p build/llvm
cd build/llvm
export LLVM_COMPILER=clang
export CC=wllvm
export CXX=clang++
cmake ../../src
make
extract-bc crypto/crypto_test
