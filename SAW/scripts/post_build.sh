#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


set -ex

# export BINUTILS_TARGET_PREFIX=aarch64-linux-gnu

mkdir -p build/llvm_x86/crypto build/x86/crypto # build/llvm_aarch64/crypto
cp build_src/llvm_x86/crypto/crypto_test build/llvm_x86/crypto/crypto_test
cp build_src/x86/crypto/crypto_test build/x86/crypto/crypto_test
# cp build_src/llvm_aarch64/crypto/crypto_test build/llvm_aarch64/crypto/crypto_test
extract-bc build/llvm_x86/crypto/crypto_test
# extract-bc build/llvm_aarch64/crypto/crypto_test
