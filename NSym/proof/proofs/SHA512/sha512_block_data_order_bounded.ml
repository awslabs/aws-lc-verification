(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0*)

open Air;;
module Cryptol = Cryptol;;

(* ---------------------------------------------------------------------- *)

let w0 = (sb 64 "w0");;
let w1 = (sb 64 "w1");;
let w2 = (sb 64 "w2");;
let w3 = (sb 64 "w3");;
let w4 = (sb 64 "w4");;
let w5 = (sb 64 "w5");;
let w6 = (sb 64 "w6");;
let w7 = (sb 64 "w7");;
let w8 = (sb 64 "w8");;
let w9 = (sb 64 "w9");;
let w10 = (sb 64 "w10");;
let w11 = (sb 64 "w11");;
let w12 = (sb 64 "w12");;
let w13 = (sb 64 "w13");;
let w14 = (sb 64 "w14");;
let w15 = (sb 64 "w15");;
let input_list = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15];;
let asm_input = input_list;;

(* Specification *)

air_fn_set_uninterpreted_status
  true
  ["arm.inst_sfp_crypto_two_reg_sha512.sigma_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_1";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1";
   "arm.inst_sfp_crypto_three_reg_sha512.ch";
   "arm.inst_sfp_crypto_three_reg_sha512.maj";
   "spec.SHA512rec.air_s0";
   "spec.SHA512rec.air_s1";
   "spec.SHA512rec.air_S0";
   "spec.SHA512rec.air_S1";
   "spec.SHA512rec.air_Ch";
   "specs.common.bv_revbytes64"];;

let spec_message = 
  let input = List.map Specs.Common.bv_revbytes64 input_list in
  Cryptol.array_from_seq "0x40" "0x40"
    (Cryptol.toCry2Dim input)
    (Cryptol.symbolic_malloc "input" 64 64);;

air_fn_set_beta_reduce_status true
  ["spec.SHA512rec.air_compress_Common_t1";
   "spec.SHA512rec.air_compress_Common_e";
   "spec.SHA512rec.air_compress_Common_a";
   "spec.SHA512rec.air_compress_Common_t2";
   "spec.SHA512rec.air_messageSchedule_Word";
  ];;


air_fn_set_uninterpreted_status false ["spec.SHA512rec.air_processBlock_Common_rec"];
air_fn_set_beta_reduce_status true ["spec.SHA512rec.air_processBlock_Common_rec"];;
air_fn_set_uninterpreted_status false ["spec.SHA512rec.air_processBlocks_rec"];
air_fn_set_beta_reduce_status true ["spec.SHA512rec.air_processBlocks_rec"];;

let expected_message_digest =
  let n = Cryptol.CryBV(s_cb 64 "0x1") in
  (Cryptol.rev_digest_blocks
    (Autospecs.SHA512rec.lowercase_processBlocks_rec n spec_message));;

(* air_fn_set_beta_reduce_status false
  ["spec.SHA512rec.air_compress_Common_t1";
  "spec.SHA512rec.air_compress_Common_e";
  "spec.SHA512rec.air_compress_Common_a";
  "spec.SHA512rec.air_compress_Common_t2";
  "spec.SHA512rec.air_messageSchedule_Word";
  ];; *)

air_fn_set_uninterpreted_status
  true
  ["arm.inst_sfp_crypto_two_reg_sha512.sigma_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_1";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_0";
   "arm.inst_sfp_crypto_three_reg_sha512.sigma_big_1";
   "arm.inst_sfp_crypto_three_reg_sha512.ch";
   "arm.inst_sfp_crypto_three_reg_sha512.maj";
   "spec.SHA512rec.air_s0";
   "spec.SHA512rec.air_s1";
   "spec.SHA512rec.air_S0";
   "spec.SHA512rec.air_S1";
   "spec.SHA512rec.air_Ch";
   "specs.common.bv_revbytes64";

   "arm.inst_dpr_logical_shifted_reg.eor64";
   "arm.inst_dpr_logical_shifted_reg.orr64";
   "arm.inst_dpr_logical_shifted_reg.and64";
   "arm.inst_dpr_logical_shifted_reg.bic64";
   "arm.inst_dpi_extract.ror64";
   "arm.inst_dpr_one_src.rev64";
  ];;

(* ---------------------------------------------------------------------- *)

(* Implementation *)

open Arm;;

let state =
  Sha512_block_data_order_init.sha512_block_data_order_init_state
    ~num_blocks:(cb 64 1)
    ~ctx_base:(sb 64 "ctx_base")
    ~input_base:(sb 64 "input_base")
    ~input:(Some asm_input)
    "State initialized for sha512_block_data_order.";;

(*
open State.Assertions;;

(* We don't really need these assertion-based rewrites anymore because we *)
(* chose to model the input memory as 64-bit addressable, but I'm leaving *)
(* these in this file as documentation. *)

add_assertion
  ~pc:(cb 64 0x1256d4)
  (Rewrite "x3_contents")
  (Rewrite((Gpr 3), w0));;
add_assertion
  ~pc:(cb 64 0x1256d4)
  (Rewrite "x4_contents")
  (Rewrite((Gpr 4), w1));;
add_assertion
  ~pc:(cb 64 0x125738)
  (Rewrite "x5_contents")
  (Rewrite((Gpr 5), w2));;
add_assertion
  ~pc:(cb 64 0x125738)
  (Rewrite "x6_contents")
  (Rewrite((Gpr 6), w3));;
add_assertion
  ~pc:(cb 64 0x1257e4)
  (Rewrite "x7_contents")
  (Rewrite((Gpr 7), w4));;
add_assertion
  ~pc:(cb 64 0x1257e4)
  (Rewrite "x8_contents")
  (Rewrite((Gpr 8), w5));;
add_assertion
  ~pc:(cb 64 0x125890)
  (Rewrite "x9_contents")
  (Rewrite((Gpr 9), w6));;
add_assertion
  ~pc:(cb 64 0x125890)
  (Rewrite "x10_contents")
  (Rewrite((Gpr 10), w7));;
add_assertion
  ~pc:(cb 64 0x12593c)
  (Rewrite "x11_contents")
  (Rewrite((Gpr 11), w8));;
add_assertion
  ~pc:(cb 64 0x12593c)
  (Rewrite "x12_contents")
  (Rewrite((Gpr 12), w9));;
add_assertion
  ~pc:(cb 64 0x1259e8)
  (Rewrite "x13_contents")
  (Rewrite((Gpr 13), w10));;
add_assertion
  ~pc:(cb 64 0x1259e8)
  (Rewrite "x14_contents")
  (Rewrite((Gpr 14), w11));;
add_assertion
  ~pc:(cb 64 0x125a94)
  (Rewrite "x15_contents")
  (Rewrite((Gpr 15), w12));;
add_assertion
  ~pc:(cb 64 0x125a94)
  (Rewrite "x0_contents")
  (Rewrite((Gpr 0), w13));;
add_assertion
  ~pc:(cb 64 0x125b48)
  (Rewrite "x1_contents")
  (Rewrite((Gpr 1), w14));;
add_assertion
  ~pc:(cb 64 0x125b48)
  (Rewrite "x2_contents")
  (Rewrite((Gpr 2), w15));;
*)

(* Nsym_config.quiet_disasm true;; *)
let final_ss = run ~ignore_assertions:true state;;

let message_digest = read_mem_data 64 (State.make_pointer (sb 64 "ctx_base")) final_ss;;

let expected_message_digest' =
  let _ = print_string "spec before:" in
  let _ = print_airexp_let expected_message_digest in
  uncond_rewrite
  expected_message_digest
    Sha512_block_data_order_rules.[
      rev64_of_rev64_rule;
      (* Note: the following rewrites are necessary for cvc5 only *)
      commutativity_and_associativity_of_bvadd_1;
      commutativity_and_associativity_of_bvadd_2;
      commutativity_and_associativity_of_bvadd_3;
    ];;

print_string "spec:";;
print_airexp_let expected_message_digest';;

let message_digest' =
  uncond_rewrite message_digest Sha512_block_data_order_rules.[
      ch_rule;
      maj_rule;
      sigma_big_1_rule1;
      sigma_big_1_rule2;
      sigma_big_0_rule1;
      sigma_big_0_rule2;
      sigma_0_rule;
      sigma_1_rule;
      rev_rule;
      (* Note: the rewrites bvchop_bvadd_rule and bvchop_bvadd_rule2 are necessary for cvc5 only *)
      bvchop_bvadd_rule;
      bvchop_bvadd_rule2;
      crock1;
      crock2;
      crock3; (* crock3: needed for cvc5, not z3 *)
      rev64_of_rev64_rule;
      sigma0_equiv_rule;
      sigma1_equiv_rule;
      sigma0_big_equiv_rule;
      sigma1_big_equiv_rule;
      ch_equiv_rule;
      maj_equiv_rule;
    ];;

print_string "impl:";;
print_airexp_let message_digest';;

(* ---------------------------------------------------------------------- *)

(* Interestingly, if we don't wrap the impl. and spec. formulas in a
   function call, we need NSym to beta-reduce the following functions
   in order to get the proof obligation go through.

   "specs.sha2.compression_update_t1_512";
   "specs.sha2.compression_update_e_512";
   "specs.sha2.compression_update_a_512";
   "specs.sha2.compression_update_t2_512";
   "specs.sha2.message_schedule_word_512";
*)

Smtverify.air_prove ~lhs:message_digest' ~rhs:expected_message_digest'
  ~solver_options:{ main_check =
                      { Smtverify.SmtSolve.solver_defaults with
                        (* Can be solved by Z3, CVC5, as well as Bitwuzla. *)
                        solvers = [CVC5];
                        (* solvers = [CVC5; Z3]; *)
                        (* ats = Portfolio; *)
                        (* ats_account = "shilgoel+ats" *)};
                    vacuity_check =
                      Prove { Smtverify.SmtSolve.solver_defaults with
                              (* Can be solved by Z3, CVC5, as well as Bitwuzla. *)
                              solvers = [CVC5];
                              (* solvers = [CVC5; Z3]; *)
                              (* ats = Portfolio; *)
                              (* ats_account = "shilgoel+ats" *)}}
  "sha512_block_data_order_one_block_correct";;

(* ---------------------------------------------------------------------- *)
