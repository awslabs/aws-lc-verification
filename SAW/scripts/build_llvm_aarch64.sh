#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

BUILD_TYPE=$1
TARGET="aarch64-unknown-linux-gnu"

mkdir -p build_src/llvm_aarch64
cd build_src/llvm_aarch64
export LDFLAGS="-fuse-ld=lld"

export LLVM_COMPILER=clang
export BINUTILS_TARGET_PREFIX=aarch64-linux-gnu

cmake -DCMAKE_BUILD_TYPE=$BUILD_TYPE \
      -DBUILD_LIBSSL=OFF \
      -DCMAKE_TOOLCHAIN_FILE=../../scripts/build_llvm_aarch64.cmake \
      -DCMAKE_C_COMPILER_TARGET=$TARGET \
      -DCMAKE_CXX_COMPILER_TARGET=$TARGET \
      -DCMAKE_ASM_COMPILER_TARGET=$TARGET \
      -DCMAKE_CXX_LINK_FLAGS="-Wl,--unresolved-symbols=ignore-in-object-files"  \
      ../../../src

# -DKEEP_ASM_LOCAL_SYMBOLS=1 \
# -DCMAKE_C_FLAGS="-L/usr/lib/gcc-cross/aarch64-linux-gnu/11" \
# -DCMAKE_CXX_FLAGS="-L/usr/lib/gcc-cross/aarch64-linux-gnu/11" \
# -DCMAKE_ASM_FLAGS="-L/usr/lib/gcc-cross/aarch64-linux-gnu/11" \

NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
make -j $NUM_CPU_THREADS VERBOSE=1
