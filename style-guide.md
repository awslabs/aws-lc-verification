# SAW Script Style Guide #

This document details best practices for organizing proofs in SAW script.

## Naming Conventions ##

* Constant definitions should be in all caps.
* Pointers should be suffixed with `_ptr`.
* Function specifications should be named `<function_name>_spec`.
* Overrides should be named `<function_name>_ov`.
* Theorem lists should be name `<function_name>_thms`
* In the case of multiple specifications or overrides of the same function,
  some meaningful name should be between the function name and the suffix.  For
  example, `OPENSSL_free_nonnull_spec` and `OPENSSL_free_null_spec` provide
  specifications for `OPENSSL_free` in the non-null and null cases
  respectively.

## Proof Organization ##

SAW scripts should be organized in the following order:

1. Imports
2. Constant definitions
3. Helpers
4. Specifications
5. Proofs

Splitting proofs across multiple files is recommended to enable code reuse and
increase readability.  If a proof is split across multiple files, then each
file should be organized in the above order.  This document provides more
details on best practices for splitting up proofs in the Splitting Proofs Apart
section.

### Example ###

This simple example SAW script verifying a dot product implementation has
comments added to demonstrate the various sections of the proof:

```
///////////////////////////////////////////////////////////////////////////////
// Imports
///////////////////////////////////////////////////////////////////////////////

import "dotprod.cry";

m <- llvm_load_module "dotprod_struct.bc";

///////////////////////////////////////////////////////////////////////////////
// Constant definitions
///////////////////////////////////////////////////////////////////////////////

let INT_SIZE = 32;

///////////////////////////////////////////////////////////////////////////////
// Helpers
///////////////////////////////////////////////////////////////////////////////

let alloc_init ty v = do {
    p <- crucible_alloc ty;
    crucible_points_to p v;
    return p;
};

let ptr_to_fresh n ty = do {
    x <- crucible_fresh_var n ty;
    p <- alloc_init ty (crucible_term x);
    return (x, p);
};

///////////////////////////////////////////////////////////////////////////////
// Specifications
///////////////////////////////////////////////////////////////////////////////

let dotprod_struct_spec n = do {
    let nt = crucible_term {{ `n : [INT_SIZE] }};
    (xs, xs_ptr) <- ptr_to_fresh "xs" (llvm_array n (llvm_int INT_SIZE));
    (ys, ys_ptr) <- ptr_to_fresh "ys" (llvm_array n (llvm_int INT_SIZE));
    let xval = crucible_struct [ xs_ptr, nt ];
    let yval = crucible_struct [ ys_ptr, nt ];
    x_ptr <- alloc_init (llvm_struct "struct.vec_t") xval;
    y_ptr <- alloc_init (llvm_struct "struct.vec_t") yval;
    crucible_execute_func [x_ptr, y_ptr];
    crucible_return (crucible_term {{ dotprod xs ys }});
};

///////////////////////////////////////////////////////////////////////////////
// Proofs
///////////////////////////////////////////////////////////////////////////////

dotprod_struct_ov <- crucible_llvm_verify m "dotprod_struct" [] true (dotprod_struct_spec 2) z3;
crucible_llvm_verify m "dotprod_wrap" [dotprod_struct_ov] true (dotprod_struct_spec 2) z3;
```

### Splitting Proofs Apart ###

Proofs should be split into multiple files when multiple proofs are present
and, for example, share helpers or specifications.  Proofs should also be split
once the proof becomes long enough that readability is negatively impacted.
Components that you may wish to group in separate files include:

* Helper functions
* Specifications
* Rewrite rules
* Lists of theorems used in `crucible_llvm_verify` commands

The contents of these separate files should be organized according to the list
at the at the top of the Proof Organization section.

## Parameterized Proofs ##

Parameterized proofs should be broken into three files (or three groups of
files): proof, definitions, and top-level.  In the proof, use
undefined variables in places you would like to enable parametrization.  Then,
for each instance of the proof, create files defining the undefined variables
from the proof.  Finally, for each instance of the proof, create a top level
file that includes the definition files followed by the proof files.

### Example ###

This example converts the previous dot product example to a parametrized proof
with a configurable integer size.  First, we provide the proof in
`dotprod_struct.saw`:

```
///////////////////////////////////////////////////////////////////////////////
// Imports
///////////////////////////////////////////////////////////////////////////////

import "dotprod.cry";

m <- llvm_load_module LLVM_BYTECODE;

///////////////////////////////////////////////////////////////////////////////
// Helpers
///////////////////////////////////////////////////////////////////////////////

let alloc_init ty v = do {
    p <- crucible_alloc ty;
    crucible_points_to p v;
    return p;
};

let ptr_to_fresh n ty = do {
    x <- crucible_fresh_var n ty;
    p <- alloc_init ty (crucible_term x);
    return (x, p);
};

///////////////////////////////////////////////////////////////////////////////
// Specifications
///////////////////////////////////////////////////////////////////////////////

let dotprod_struct_spec n = do {
    let nt = crucible_term {{ `n : [INT_SIZE] }};
    (xs, xs_ptr) <- ptr_to_fresh "xs" (llvm_array n (llvm_int INT_SIZE));
    (ys, ys_ptr) <- ptr_to_fresh "ys" (llvm_array n (llvm_int INT_SIZE));
    let xval = crucible_struct [ xs_ptr, nt ];
    let yval = crucible_struct [ ys_ptr, nt ];
    x_ptr <- alloc_init (llvm_struct "struct.vec_t") xval;
    y_ptr <- alloc_init (llvm_struct "struct.vec_t") yval;
    crucible_execute_func [x_ptr, y_ptr];
    crucible_return (crucible_term {{ dotprod xs ys }});
};

///////////////////////////////////////////////////////////////////////////////
// Proofs
///////////////////////////////////////////////////////////////////////////////

dotprod_struct_ov <- crucible_llvm_verify m "dotprod_struct" [] true (dotprod_struct_spec 2) z3;
crucible_llvm_verify m "dotprod_wrap" [dotprod_struct_ov] true (dotprod_struct_spec 2) z3;
```

This differs from the previous proof in that it does not define
`INT_SIZE`, and the argument to `llvm_load_module` in the Imports section is
now an undefined variable `LLVM_BYTECODE`.

Next, we provide the definitions to these variables in
`dotprod_struct_32_defs.saw`:

```
let INT_SIZE = 32;
let LLVM_BYTECODE = "dotprod_struct.bc";
```

Lastly, we provide the top-level file `dotprod_struct_32.saw` that includes
both of these files:

```
include "dotprod_struct_32_defs.saw";
include "dotprod_struct.saw";
```

Running `saw` on `dotprod_struct_32.saw` checks the proof.  If we then wish to
check a 64-bit version of the same program, we only need to provide a new
definitions file `dotprod_struct_64_defs.saw`:

```
let INT_SIZE = 64;
let LLVM_BYTECODE = "dotprod_struct_64.bc";
```

As well as a new top-level file including `dotprod_struct_64_defs.saw` rather
than `dotprod_struct_32_defs.saw`:

```
include "dotprod_struct_64_defs.saw";
include "dotprod_struct.saw";
```

