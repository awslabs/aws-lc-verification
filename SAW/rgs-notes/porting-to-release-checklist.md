Small tasks:
* [X] When LLVM optimizes `bn_select_words`, it produces code that compares pointers. This is permissible in Crucible only when a specific flag is enabled, but SAW does not yet offer a way to enable that flag. I've added support for this in https://github.com/GaloisInc/saw-script/pull/1309, which is still pending review. (**Estimate**: however long it takes to land the MR. Probably no more than 1 hour.)

Medium tasks:
* [ ] The proofs for `RSA_sign_pss_mgf1` and `RSA_verify_pss_mgf1` will require more complicated tactics since they feature many more vectorized instructions that before. I've figured out how to do this before in a much more limited setting (`bn_reduce_once_in_place`). (**Estimate**: 8–16 hours)
* [ ] Write a specification for `ec_GFp_simple_is_on_curve`, which currently has an extremely simplistic unsafe override. (**Estimate**: 8–16 hours)

Difficult tasks:
* [ ] The `value_barrier_w` function implements the identity function using inline assembly. It would be bad for performance to mark this function as `noinline`, but at the same time, having inline assembly inlined everywhere in the bitcode is troublesome for SAW. Two possible solutions:
  - Add a special case in Crucible for the kinds of inline assembly that `value_barrier_w` uses. This is extremely unprincipled, but it would unblock this. (**Estimate**: 4–8 hours)
  - Add more support for inline assembly in Crucible. (**Estimate**: unknown)
* Besides `value_barrier_w`, there are other inline-assembly–using functions (e.g., `bn_reduce_once_in_place`) that cause similar issues. Their uses of inline assembly are much more complicated, however, so it's unlikely that we could easily add special cases for them in Crucible. This means that we can either:
  - Add more support for inline assembly in Crucible. (**Estimate**: unknown)
  - Mark certain functions as `noinline` (e.g., `bn_sub_words`, which invokes `bn_reduce_once_in_place`). I've went with this approach for now.

Unknown-difficulty tasks:
* [ ] The proofs of `ECDSA_do_sign`, `EVP_PKEY_keygen`, and `RSA_verify_PKCS1_PSS_mgf1` currently go into an infinite loop for reasons I haven't yet figured out. (**Estimate**: 2-4 hours to triage, unknown hours to fix)
* [ ] The proof of `ECDSA_do_verify` triggers `Run-time error: encountered call to the Cryptol 'error' function` for reasons I haven't yet figured out. (https://github.com/GaloisInc/saw-script/issues/1326 _might_ make this easier to debug, but that's not a guarantee.) (**Estimate**: 2–4 hours to triage, unknown hours to fix)

"Tasks" that I'm not sure if there's much we can do about:
* [ ] I had to mark `aes_gcm_from_cipher_ctx` as `noinline` for two reasons:
  - Its unsafe specification basically assumes that it doesn't get inlined. (See the top-level `README` for more details.)
  - Without it, `%struct.EVP_AES_GCM_CTX` gets completely optimized away as a consequence of `aes_gcm_from_cipher_ctx` being optimized away. As a result, `llvm_sizeof "struct.EVP_AES_GCM_CTX"` no longer works. This is a non-issue if `aes_gcm_from_cipher_ctx` is marked as `noinline`, but without it, we'd have to be more clever in order to make `llvm_sizeof` work. (We'd likely need to fix https://github.com/GaloisInc/saw-script/issues/1291.)
* [ ] By similar reasoning, I had to mark `rsa_blinding_get` and `rsa_blinding_release` and `noinline`. (See the `README` under `SAW/proof/RSA` for more details.)
