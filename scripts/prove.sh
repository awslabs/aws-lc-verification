#!/bin/sh
set -e

saw proof/SHA256/SHA256.saw
saw proof/SHA512/verify-SHA512-384.saw
saw proof/SHA512/verify-SHA512-512.saw
