#!/bin/sh
set -e

mkdir -p build_src/x86
cd build_src/x86
export CC=clang
export CXX=clang++
cmake ../../../src
make
