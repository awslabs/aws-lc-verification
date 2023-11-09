#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

PATCH=$(realpath ./patch)

apply_patch() {
    PATCH_NAME=$1

    (cd ../src; patch -p1 -r - --forward < "$PATCH"/"$PATCH_NAME".patch || true)
}

# Apply some patches
apply_patch "sha512-armv8"

# ./scripts/build_aarch64.sh "Release" "neoverse-n1"
# ./scripts/build_llvm.sh "Release"
# ./scripts/post_build.sh

# cp -r ./build ./proof/

# # TODO: run proofs for graviton2
# INFILE=./spec/SHA512rec.icry
# OUTFILE=./proof/autospecs/SHA512/SHA512rec.ml
# ASTFILE=./spec/SHA512rec.ast
# cryptol-to-air -i $INFILE -o $OUTFILE -a $ASTFILE -u S0,S1,s0,s1,Ch,Maj,messageSchedule_Word,compress_Common_t1,compress_Common_t2,compress_Common_e,compress_Common_a,processBlock_Common_rec,processBlocks_rec
# # make -C ./proof sha512_grav2

# INFILE=./spec/SHA384rec.icry
# OUTFILE=./proof/autospecs/SHA512/SHA384rec.ml
# ASTFILE=./spec/SHA384rec.ast
# cryptol-to-air -i $INFILE -o $OUTFILE -a $ASTFILE -u S0,S1,s0,s1,Ch,Maj,messageSchedule_Word,compress_Common_t1,compress_Common_t2,compress_Common_e,compress_Common_a,processBlock_Common_rec,processBlocks_rec

rm -rf build/
rm -rf build_src/

./scripts/build_aarch64.sh "Release" "neoverse-512tvb"
./scripts/post_build.sh

cp -r ./build ./proof/

# TODO: run proofs for graviton3
INFILE=./spec/SHA512rec.icry
OUTFILE=./proof/autospecs/SHA512/SHA512rec.ml
ASTFILE=./spec/SHA512rec.ast
cryptol-to-air -i $INFILE -o $OUTFILE -a $ASTFILE -u S0,S1,s0,s1,Ch,Maj,messageSchedule_Word,compress_Common_t1,compress_Common_t2,compress_Common_e,compress_Common_a,processBlock_Common_rec,processBlocks_rec

INFILE=./spec/SHA384rec.icry
OUTFILE=./proof/autospecs/SHA512/SHA384rec.ml
ASTFILE=./spec/SHA384rec.ast
cryptol-to-air -i $INFILE -o $OUTFILE -a $ASTFILE -u S0,S1,s0,s1,Ch,Maj,messageSchedule_Word,compress_Common_t1,compress_Common_t2,compress_Common_e,compress_Common_a,processBlock_Common_rec,processBlocks_rec

make -C ./proof sha512_grav3
