#!/bin/sh
set -e

mkdir -p build/x86
cd build/x86
export CC=clang
export CXX=clang++
cmake ../../src
make
