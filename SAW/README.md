# AWS libcrypto Verification using SAW
This repository contains specifications and correctness proofs for some cryptographic operations functions in [AWS libcrypto](https://github.com/awslabs/aws-lc). All proofs are carried out in [SAW](https://saw.galois.com/) using [Cryptol](https://cryptol.net/) specifications stored in the [Galois Cryptol spec repository](https://github.com/GaloisInc/cryptol-specs). 

## Building and Running
The easiest way to build the library and run the proofs is to use [Docker](https://docs.docker.com/get-docker/). To check the proofs, execute the following steps in the top-level directory of the repository.

1. Clone the submodules: `git submodule update --init`
2. Build a Docker image: `docker build -t awslc-saw .`
3. Run the proofs inside the Docker container: ``docker run -v `pwd`:`pwd` -w `pwd` awslc-saw``

Running ``docker run -it -v `pwd`:`pwd` -w `pwd` --entrypoint bash awslc-saw`` will enter an interactive shell within the container, which is often useful for debugging.

## Specification

The following table describes the implementations that are verified using SAW. See the [top-level README](../README.md) for general information and definitions related to this table.

| Algorithm | Variants |  API Operations | Platform   | Caveats
| ----------| -------------| --------------- | -----------| ------------
| SHA-2     | 384, 512     | EVP_DigestInit, EVP_DigestUpdate, EVP_DigestFinal, EVP_Digest     | SandyBridge+ | InputLength, NoEngine, MemCorrect
| HMAC      | with <nobr>SHA-384</nobr> | HMAC_CTX_init, HMAC_Init_ex, HMAC_Update, HMAC_Final, HMAC | SandyBridge+ | InputLength, NoEngine, MemCorrect, InitZero

The verification ensures that each verified function has the following general properties:
* The function does not write to or read from memory outside of the allocated space pointed to by its parameters. Though an exception to this rule exists in cases where a function frees memory. In these cases, the verification would not fail if the function writes to memory after it is freed.
* The function does not write to memory within the allocated space pointed to by parameters that are intended to be read only.
* The function does not read from memory that has not been initialized with a value.
* If the function is written in C, then it is free from all other undefined behavior.

### SHA-2

The EVP_Digest* functions are verified to have the following properties related to SHA-2. For more detailed specifications, see [evp-function-specs.saw](proof/SHA512/evp-function-specs.saw). BLOCK_LENGTH is the block length of the hash function, in bytes. For example, BLOCK_LENGTH for SHA-384 is 48.

| Function  | Preconditions |  Postconditions |
| ---------------| -------------| --------------- | 
| EVP_DigestInit | <ul><li>The parameters are an allocated EVP_MD_CTX and a valid EVP_MD such as the value returned by EVP_sha384()</li></ul> | <ul><li>The context is valid and initialized for the desired algorithm.</li></ul> |
| EVP_DigestUpdate | <ul><li>The context is valid and the internal buffer offset is n.</li><li>The input length is k, and the input buffer has at least k allocated bytes.</li></ul> | <ul><li>The hash state in the context has been correctly updated for each complete block as defined by the SHA-2 specification.</li><li>The first (n+k)%BLOCK_LENGTH bytes of the internal buffer are equal to the remaining input bytes, and the internal buffer offset has been updated to (n+k)%BLOCK_LENGTH.</li></ul> |
| EVP_DigestFinal | <ul><li>The context is valid and the internal buffer offset is n.</li><li> The output buffer has at least BLOCK_LENGTH allocated bytes.</li><li> The length output pointer is either null or it points to an integer.</li></ul> | <ul><li>The output buffer holds the correct hash value as defined by the SHA-2 specification. This hash value is produced from the hash state and the remaining BLOCK_LENGTH-n bytes in the internal buffer.</li><li> If the output length pointer is non-null, it points to the value BLOCK_LENGTH.</li></ul> |
| EVP_DigestSpec | <ul><li>The input length is k, and the input buffer has at least k allocated bytes.</li><li> The output buffer has at least BLOCK_LENGTH allocated bytes.</li><li> The length output pointer is either null or it points to an integer.</li></ul> | <ul><li>The output buffer holds the correct hash value as defined by the SHA-2 specification.</li><li> If the output length pointer is non-null, it points to the value BLOCK_LENGTH.</li></ul>

### HMAC with SHA-384

The HMAC_* functions are verified to have the following properties related to HMAC with SHA-384. For more detailed specifications, see [HMAC.saw](proof/HMAC/HMAC.saw). BLOCK_LENGTH is the block length of the hash function, in bytes. BLOCK_LENGTH for SHA-384 is 48.

| Function  | Preconditions |  Postconditions |
| ---------------| -------------| --------------- | 
| HMAC_CTX_init | <ul><li>The parameter is an allocated context.</li></ul> | <ul><li>The context is returned to its zeroized state.</li></ul> |
| HMAC_Init_ex | <ul><li>The context is in its zeroized state.</li><li>The digest type points to a correct EVP_MD, such as the value returned by EVP_sha384().</li><li>The key length parameter is n and the key array contains at least n bytes.</li></ul> | <ul><li>The context is valid and initialized for HMAC with the desired hash function.</li></ul>  |
| HMAC_Update |  <ul><li>The context is valid and the internal buffer offset is n.</li><li> The input length is k, and the input buffer has at least k allocated bytes.</li></ul> | <ul><li>The HMAC state in the context has been correctly updated for each complete block as defined by the HMAC specification.</li><li> The first (n+k)%BLOCK_LENGTH bytes of the internal buffer are equal to the remaining input bytes, and the internal buffer offset has been updated to (n+k)%BLOCK_LENGTH.</li></ul> |
| HMAC_Final | <ul><li>The context is valid and the internal buffer offset is n.</li><li> The output buffer has at least BLOCK_LENGTH allocated bytes.</li><li> The length output pointer is either null or it points to an integer.</li></ul> | <ul><li>The output buffer holds the correct value as defined by the HMAC specification. This value is produced from the HMAC state and the remaining BLOCK_LENGTH-n bytes in the internal buffer.</li><li> If the output length pointer is non-null, it points to the value BLOCK_LENGTH.</li></ul> |
| HMAC | <ul><li>The digest type points to a correct EVP_MD, such as the value returned by EVP_sha384().</li><li> The key length parameter is n and the key array contains at least n bytes.</li><li>  The input length is k, and the input buffer has at least k allocated bytes.</li><li> The output buffer has at least BLOCK_LENGTH allocated bytes. </li><li>The length output pointer is either null or it points to an integer.</li></ul> | <ul><li>The output buffer holds the correct  value as defined by the HMAC specification.</li><li> If the output length pointer is non-null, it points to the value BLOCK_LENGTH.</li></ul> |
