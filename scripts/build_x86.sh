#!/bin/sh
set -e

mkdir -p build/x86
cd build/x86
export CC=gcc
cmake ../../src
make
