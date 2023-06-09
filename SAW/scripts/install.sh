#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

SAW_URL='https://saw-builds.s3.us-west-2.amazonaws.com/saw-0.9.0.99-2023-06-08-ab46c76e0-Linux-x86_64.tar.gz'

mkdir -p $HOME/bin $HOME/deps

# fetch SAW
# This will override the current SAW in the docker in AWS-LC's CI
rm -rf $HOME/deps/saw
mkdir -p $HOME/deps/saw
wget $SAW_URL -O ~/deps/saw.tar.gz
tar -xzf $HOME/deps/saw.tar.gz --one-top-level="$HOME/deps/saw"
cp $HOME/deps/saw/*/bin/saw $HOME/bin/saw
cp $HOME/deps/saw/*/bin/cryptol $HOME/bin/cryptol
