#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

BUILD_TYPE=$1

mkdir -p build_src/aarch64
cd build_src/aarch64
export LDFLAGS="-fuse-ld=lld"
cmake -DCMAKE_BUILD_TYPE=$BUILD_TYPE \
      -DKEEP_LOCAL_SYMBOLS=1 \
      -DBUILD_LIBSSL=OFF \
      -DCMAKE_TOOLCHAIN_FILE=../../scripts/build_aarch64.cmake \
      -DCMAKE_C_FLAGS="-mcpu=neoverse-n1 -I/usr/aarch64-linux-gnu/include/c++/9/aarch64-linux-gnu" \
      -DCMAKE_CXX_FLAGS="-mcpu=neoverse-n1 -I/usr/aarch64-linux-gnu/include/c++/9/aarch64-linux-gnu" \
      -DCMAKE_ASM_FLAGS="-mcpu=neoverse-n1 -I/usr/aarch64-linux-gnu/include/c++/9/aarch64-linux-gnu" \
      -DCMAKE_C_COMPILER_TARGET="aarch64-none-linux-gnu" \
      -DCMAKE_CXX_COMPILER_TARGET="aarch64-none-linux-gnu" \
      -DCMAKE_ASM_COMPILER_TARGET="aarch64-none-linux-gnu" \
      ../../../src

NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS