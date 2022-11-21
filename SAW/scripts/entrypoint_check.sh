#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

PATH=/lc/bin:/go/bin:$PATH
PATCH=$(realpath ./patch)

apply_patch() {
  PATCH_NAME=$1

  (cd ../src; patch -p1 -r - --forward < "$PATCH"/"$PATCH_NAME".patch || true)
}

# First, apply some patches (TODO: remove them)...

apply_patch "rsa-encrypt"
apply_patch "nomuxrsp"
apply_patch "noinline-aes_gcm_from_cipher_ctx"
apply_patch "noinline-bn_mod_add_words"
apply_patch "noinline-bn_reduce_once_in_place"
apply_patch "noinline-bn_sub_words"
apply_patch "noinline-ec_scalar_is_zero"
apply_patch "noinline-ec_point_mul_scalar"
apply_patch "noinline-ec_point_mul_scalar_base"
apply_patch "noinline-ec_get_x_coordinate_as_bytes"
apply_patch "noinline-ec_get_x_coordinate_as_scalar"
apply_patch "noinline-value_barrier_w"
apply_patch "noinline-value_barrier_u64"
apply_patch "noinline-GetInPlaceMethods"
apply_patch "noinline-fiat_p384_sub"
apply_patch "noinline-p384_get_bit"


# ...next, check the proofs using CMake's Release settings...

./scripts/build_x86.sh  "Release"
./scripts/build_llvm.sh "Release"
./scripts/post_build.sh
./scripts/run_checks_release.sh

# The P-384 proof assumes correctness of fiat-crypto field arithmetic functions, so they need to be enabled in the build

rm -rf build/
rm -rf build_src/

./scripts/build_llvm.sh  "Release" "-DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX=ON"
./scripts/post_build.sh
./scripts/run_checks_noasm.sh

# ...finally, check the proofs using CMake's Debug settings.

rm -rf build/
rm -rf build_src/

./scripts/build_x86.sh  "Debug"
./scripts/build_llvm.sh "Debug"
./scripts/post_build.sh
./scripts/run_checks_debug.sh
