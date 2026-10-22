# TG complete mixed first-order collision counterterm

- **ID:** TG-C7-MIXED-FIRST-ORDER
- **Stage:** 1-in-progress
- **Route:** TG
- **Parents:** `tg-mixed-reflection-collision-counterterm.md`, `tg-confluent-cofinal-counterterm.md`

## Hard target and corpus basis

The actual mixed source's second-order coefficient and uncompensated cofinal operator
divergence are checked. Gamma comparison still lacks the complete mixed first-order pole.
This is the next source identity to solve, retaining every cross-prime and inverse-Gram term.

`PrimeBurnolMixedReflectedCollision` supplies `c(k)=T(k) J(k) T(k)*`, `J(0)=2H`, and
invertible confluent H. Its explicit entries are rational functions of k squared.
`PrimeBurnolMixedCubicPrincipal` supplies actual idempotent p,q, the single-inverse cubic
identity, and exact source conjugation. `PrimeBurnolReflectedCubicCollision` gives only the
one-cell imaginary pole.

The first broad Gamma search completed with full inventory but mostly irrelevant radial-jet
hits. The Sonin follow-up was partial (reranking deadline), returning the already closed
bounded-clock commutators. The Gamma-cyclic defect in `RoutePFourthDepthGammaCyclicJuliaIntertwiner`
is a scalar multiple of identity, not the missing noncentral compensation. The broad mixed-pole
search was partial (semantic deadline); the focused PrimeBurnol follow-up also returned partial
with worker/deadline errors and no hits. Those empty partial results are not evidence of absence.
The literal source formulas above ground the conjecture; generated search suggestions do not.

## Conjecture and paper mechanism

Write `G=M_0`, `M=M_1`, `K=M_2-M G^-1 M`. Define

```
C0 = [[2G,0],[0,0]],
C1 = [[0,-2iM],[2iM,0]],
R  = [[0,0],[0,K^-1/2]],
S  = [[0,(i/2)G^-1 M K^-1],[-(i/2)K^-1 M G^-1,0]],
r  = p-q,
L1 = Tr(C1 p R q C0 r + C0 p S q C0 r + C0 p R q C1 r).
```

For actual reflected source trace tau and checked second-order coefficient L2, conjecture:

```
lim_(k->0,k!=0) k (tau(k)-L2/k²) = L1.
```

Factor J through k squared to prove `J'(0)=0`. Its inverse also has zero derivative; finite
determinant/adjugate formulas provide the proof if a matrix-calculus API is missing.
The rescaled inverse `R(k)=diag(k,i) J(k)^-1 diag(k,-i)` then has `R(0)=R`, `R'(0)=S`.
Multiplying the single-inverse cubic identity by k squared gives a differentiable extension
whose derivative is L1. The polynomial trace term has zero derivative after multiplication.
The derivative's slope limit gives the endpoint.

For one prime's depth packet, scalar U=uI and V=vI should reduce this to
`L1=2i v² Tr(G K^-1 M)`, agreeing with the checked one-cell pole. The sign and cofinal
behavior of this mixed trace are not assumed. No numerical experiment is used.

## Gates and scope

- [x] Scratch checked: literal desingularized Gram and inverse have zero derivative at collision.
- [x] Scratch checked: first derivatives of actual Gram and rescaled inverse, and exact rescaled inverse identity.
- [x] Scratch checked: complete source Laurent coefficient and source identification.
- [ ] Single-prime simplification; rigorous sign/cofinal audit.
- [ ] Actual Gamma matching; bounded relative operator and Hardy-index passage.

No bounded finite part, Gamma cancellation, or RH conclusion is asserted. Missing matrix-calculus
lemmas will be constructed as part of this proof, not treated as an obstruction.

## Current proof attempt

`/tmp/tg-c7-first-01a0.lean` constructs a rational square-parameter matrix, identifies it with
the literal J(k), and proves entrywise differentiability through finite sums/products and the
determinant/adjugate inverse formula. The first two gates passed scratch Lean without warnings.
The complete regularized-cubic derivative and source Laurent endpoint also passed scratch
Lean without warnings. Production leaf `PrimeBurnolMixedCubicLaurent.lean` also passes without
warnings, and all six public theorem dependency audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. Full result: `../../../3-formalized/tg-mixed-reflected-cubic-first-coefficient.md`.
The formal coefficient currently uses the exact J(0)-inverse block expression below; the
displayed Schur simplification and the one-prime reduction remain separate proof gates.

Let `E=diag(I,0)`, `F+=diag(0,iI)`, `F-=diag(0,-iI)`, `J0=J(0)`, and `A=J0^-1`. The
formal coefficient uses

```
c = c(0),       d = F+ J0 E + E J0 F-,
r = F+ A F-,   s = E A F- + F+ A E,
L1 = Tr(d p r q c(p-q) + c p s q c(p-q) + c p r q d(p-q)).
```

This is a fully explicit finite matrix expression in the source data, with no derivative or
convergence premise. Its source theorem is the stated two-sided limit after subtracting L2.

The owned scratch files were removed after the audit. Continue in the production leaf;
the remaining Schur simplification, one-prime sign/cofinal analysis and Gamma matching are open.
