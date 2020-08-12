#!/bin/sh
set -e

mkdir -p build_src/llvm
cd build_src/llvm
export LLVM_COMPILER=clang
export CC=wllvm
export CXX=clang++
cmake ../../../src
make
