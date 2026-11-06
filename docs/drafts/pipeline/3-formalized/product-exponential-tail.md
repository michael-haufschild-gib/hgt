# Exponential mass beyond a product cutoff

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6

For `q>0` and real cutoff `L`, the positive ordered-pair tail

`E(q,L)=Σ_(n,m≥1,nm≥L)exp(−qnm)`

converges absolutely and satisfies

`E(q,L)≤exp(−qL/2)/(1−exp(−q/4))²`.

For `0<q≤4`,

`E(q,L)≤64 q^(−2)exp(−qL/2)`.

## Proof

Split the exponential into two equal factors. On `nm≥L`, one factor
is at most `exp(−qL/2)`. Writing `n=i+1,m=j+1`, the inequality
`2nm≥i+j` bounds the other factor by
`exp(−q/4)^i exp(−q/4)^j`. The two geometric series give absolute
summability and the first bound.

The inequality `exp(q/4)≥1+q/4` implies
`1−exp(−q/4)≥q/(4+q)≥q/8` when `q≤4`. Squaring this denominator
bound gives the second estimate.

This controls a product tail; it asserts no sign for a signed theta series.

## Lean

`CompletedArithmeticForms/ProductExponentialTail.lean` proves
`summable_productExponentialTail`, `productExponentialTail_le`, and
`productExponentialTail_le_inverseSquare`.
Final file check passed; all three dependency audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
