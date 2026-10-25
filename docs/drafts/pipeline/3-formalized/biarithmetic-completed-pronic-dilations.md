# Exact dilations on the completed pronic space

- **ID:** biarithmetic-completed-pronic-dilations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; universal ordinary-energy action)
- **Parent:** [Payment graph norm](../2-fully-proven/biarithmetic-payment-graph-norm.md)
- **Statement:** Completed floor dilations have exact contraction factor `j^(-1/2)`, compose multiplicatively, and integrate to a contractive unital representation of the actual critical Wiener algebra.

## Proof

Normalize a positive arithmetic row by dividing its `n`th coordinate by
`r_n=sqrt(n(n+1))`. Floor dilation becomes the existing positive-integer
division-block operator with weight `r_(floor(n/j))/r_n`.
For a positive input cell `m`, its squared block mass is

`m(m+1) sum_(n=jm)^(jm+j-1) 1/[n(n+1)] = 1/j`.

The exact pronic fibre identity therefore gives
`||D_j f||^2=||f||^2/j`, hence `||D_j f||=||f||/sqrt(j)`.
Intermediate coordinate roots cancel when two block operators compose;
floor division composes as well, so `D_j D_k=D_(jk)`. The unit scale acts
as the identity and the unused zero coefficient is extended by zero.

AOT's existing synthesis theorem now integrates
`pi(a)=sum_j a(j)D_j` in operator norm. It is a unital complex algebra
representation, sends every point mass to its exact dilation operator,
and satisfies `||pi(a)||<=||a||_W`.

## Scope and verification

This is the ordinary completed pronic module, with no escape normalization
and no assumption on an arithmetic source. Coordinate agreement with the
formal cofactor action and invariance of each source graph remain separate
formal statements. Existing block operators and Wiener synthesis are reused.

Lean: `BiarithmeticGeometry/PronicDilationOperators.lean`.
Main declarations: `pronicDilationWeight_blockMass`, `norm_pronicDilationOp`,
`pronicDilationOp_comp`, `pronicDilationOp_one`, `pronicWienerRepresentation`,
`norm_pronicWienerRepresentation_le`.

- [x] Dependency-closed paper proof.
- [x] Direct repository source check; umbrella import wired.
- [x] Six transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
