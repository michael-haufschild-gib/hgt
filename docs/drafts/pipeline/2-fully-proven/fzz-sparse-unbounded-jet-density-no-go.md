# FZZ sparse unbounded-jet density no-go

- **ID:** FZZ-SUJD-NG
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FALSIFIED route premise
- **Source:** `rh-current-frontier-map.md` FZZ-P route (read-only ledger)
- **Statement:** One completed FZZ response can match Xi to unbounded node-dependent complex-order jet depth on a sparse subsequence of physical response orders, preserve the full completed analytic/real-axis package, and still carry an interior off-critical zero.

## Goal

Kill the strongest still-local repair of the FZZ-P source-selection chain

`unbounded pointwise-finite physical response jets -> unique Xi continuation / zero control -> completed Ward bound -> RH`.

Bounded uniform depth is already killed.  This candidate asks the harder boundary question: whether
`sup_m depth(m)=infinity` can restore uniqueness under order-one growth.  The target survivor is a
density law: depth must be distributed densely enough to form a uniqueness set; unbounded depth by
itself is not RH-bearing.

## Frozen proof-chain candidate

Use response coordinate `z=s-2`, center `u=z+3/2`, canonical completed response `X(z)=xi(z+2)`,
and prior anchored reciprocal-Gamma null generator `B(z)`.  Put

`m_k=(k+1)^3`, `lambda_k=m_k+3/2`, and `I=Sigma k, Fin(k+1)`.

Let `C(u)` be the genus-one canonical product whose indexed zero family sends every `(k,j)` to
`lambda_k`.  Set

`R(z)=C(z+3/2) C(-z-3/2)`

and apply the corpus entire-sharp symmetrizer:

`Q(z)=R(z) R#(z)`, where `R#(z)=conj(R(conj z))`.

Then `Q` is entire, response-reflection-even, Schwarz-real, and of exponential type (hence in the
order-one envelope).  It has order exactly `2(k+1)` at response node `m_k` and at its reflected node.
Choose a real-coefficient centered quadratic `P_Q` so that

`P_Q(a) B(a) Q(a)=i`, where `a=-5/4+i`.

Finally define

`G(z)=1+(P_Q(z) B(z) Q(z))^2`, `F(z)=X(z)G(z)`.

Candidate conclusion: `F` has the full prior completed response package, is noncanonical, vanishes
at `a`, and for every `k` and `j<=k`,

`iteratedDeriv j F (m_k) = iteratedDeriv j X (m_k)`.

This is one fixed countermodel, not a family chosen after the requested depth.

## Corpus basis and collision audit

- `canonicalProductE1Indexed`: arbitrary index type, explicitly intended for multiplicity copies.
- `analyticOrderAt_canonicalProductE1Indexed`: exact order equals fiber `ncard`.
- `canonicalProductE1Indexed_analytic` and `canonicalProductE1Indexed_ne_zero`: entire carrier and no accidental zeros.
- `norm_canonicalProductE1Indexed_le_exp_of_summable_inv`: first reciprocal summability gives exponential type.
- `eventually_norm_ge_of_summable_inv_sq`: reciprocal-square summability gives local finiteness.
- `le_analyticOrderAt_iff_iteratedDeriv_eq_zero`: contact order implies exact jet invisibility.
- `completedResponsePositiveSquareGauge_package`: preserves samples, anchors, FE, Schwarz, order one, and positive real-axis phase.
- `completed_response_boundedJet_route_noGo`: kills every fixed uniform depth but does not produce one witness with unbounded depth.
- Corpus searches found arbitrary Hermite passports without growth control and order-one canonical products with fixed/simple multiplicity, but no sparse unbounded-multiplicity order-one divisor joined to the completed FZZ package.

## Gates

- [x] 0 -> 1 in-progress: source-pure frozen falsifier, explicit RH proof chain, corpus collision audit
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem, direct check, targeted `lake build`, axiom audit
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, Lean certificate, novelty audit

## Approach

1. Prove reciprocal and reciprocal-square summability for the repeated cubic divisor:
   `(k+1)/lambda_k <= 1/(k+1)^2`.
2. Prove local finiteness and exact fiber cardinality `k+1`; obtain exact analytic order of `C`.
3. Symmetrize about response center and then by the corpus entire-sharp involution to get FE-even, Schwarz-real `Q`; transport exact order to `m_k`.
4. Prove exponential-type growth from first reciprocal summability and promote it to the corpus order-one envelope.
5. Interpolate one nonreal target with the prior real centered quadratic scheme; apply the positive-square gauge package.
6. Use the order `4(k+1)` carried by `Q^2` in `F-X` to obtain all jet equalities through depth `k`.
7. Implant the same off-critical quartet and prove noncanonicity without assuming an unknown Xi value.

## Hostile audit targets

- One fixed witness must realize all unbounded depths simultaneously.
- Jet depth is in the complex response-order variable and includes order zero.
- Nodes are actual natural physical response orders.
- Preserve the strongest prior FE/Schwarz/order-one/anchor/full-real-axis package.
- Prove growth after multiplicities are counted; do not infer it from support sparsity alone.
- State non-kill: full germ at one node and sufficiently dense cumulative multiplicity remain possible uniqueness mechanisms.

## Paper proof `[PROVED HERE]`

Write `c=3/2`, `m_k=(k+1)^3`, and `lambda_k=m_k+c`.  For
`I=Sigma k, Fin(k+1)`, let `Lambda(k,j)=lambda_k`.  Every `lambda_k` is positive and the sequence
is strictly increasing.  Counting every multiplicity copy,

`sum_(j<k+1) 1/lambda_k = (k+1)/lambda_k <= 1/(k+1)^2`.

The right side is summable.  Hence `sum_I 1/|Lambda|` converges, and so does
`sum_I 1/|Lambda|^2`.  Local finiteness is also explicit: `lambda_k<=r` implies
`k<=(k+1)^3<=r`, leaving finitely many first coordinates and a finite `Fin(k+1)` fiber over each.
The genus-one product

`C(u)=product_(q:I) E_1(u/Lambda(q))`

therefore converges locally uniformly and is entire.  First-reciprocal summability gives

`|C(u)| <= exp(2 S |u|)`, where `S=sum_I 1/|Lambda|<infinity`,

so `C` is of exponential type.  No accidental zero occurs away from the prescribed positive real
points.  Strict increase of `lambda_k` identifies the fiber over `lambda_k` with `Fin(k+1)`;
therefore the exact canonical-product divisor theorem gives

`ord_(lambda_k) C = k+1`.

Define

`R(z)=C(z+c) C(-z-c)`.

The response reflection `z |-> -3-z` sends `z+c` to `-(z+c)`, so it swaps the two factors: `R` is
reflection-even.  Translation and finite products preserve entireness and exponential type.  At
`z=m_k`, the first factor has order `k+1`, while the second is evaluated at `-lambda_k`, outside
the positive prescribed divisor and hence nonzero.  Thus

`ord_(m_k) R = k+1`.

Now use the corpus entire-sharp involution `R#(z)=conj(R(conj z))` and put

`Q(z)=R(z)R#(z)`.

The product with its sharp is Schwarz-real.  Since response reflection commutes with conjugation
and `R` is reflection-even, `R#` and then `Q` are reflection-even.  Sharp preserves entireness and
the order-one envelope.  Each `m_k` is real, so sharp preserves the order there; hence

`ord_(m_k) Q = 2(k+1)`.

Let `a=-5/4+i`.  At both `a` and `conj(a)`, the two centered arguments have nonzero imaginary
part and therefore avoid the prescribed real divisor.  Thus `R(a)`, `R(conj(a))`, and `Q(a)` are
nonzero.  The prior anchored Gamma-null function also has `B(a)!=0`.  Put

`t=i/(B(a)Q(a))`

and use the centered real interpolation polynomial

`P_Q(z)=Re(t)+2 Im(t) ((z+c)^2+15/16)`.

Because `(a+c)^2+15/16=i/2`, one has `P_Q(a)=t`.  This polynomial is reflection-even,
Schwarz-real, entire, and order one.  Consequently the multiplier `P=P_Q Q` satisfies every
hypothesis of the already-proved completed positive-square gauge package.  With

`W=P_Q B Q`, `G=1+W^2`, and `F=XG`,

that package gives: `F` is entire and order one; it has the completed functional equation and
Schwarz symmetry; it matches `X` at every natural physical response order and at all three
completed anchors; and on the whole real response axis it is a strictly positive real multiple of
`X`, hence introduces no real zero.

At the target, `W(a)=t B(a)Q(a)=i`, so `G(a)=1+i^2=0` and `F(a)=0`.  This is the completed point
`a+2=3/4+i`, inside the critical strip and off the critical line.  No value or nonvanishing claim
for Xi at that point is assumed.  As in the prior square-gauge theorem, `G-1` is not identically
zero (its value at `a` is `-1`), while `X` is not identically zero; entire-function no-zero-divisors
therefore shows `F!=X`.

It remains to prove the unbounded simultaneous jet statement.  At `m_k`, `Q` has order `2(k+1)`,
so `Q^2` has order `4(k+1)`.  Since

`F-X = X (P_Q B)^2 Q^2`,

all other factors are analytic and multiplication cannot reduce vanishing order.  Thus `F-X` has
order at least `4(k+1)` at `m_k`.  Every derivative of order `j<4(k+1)` vanishes there, in
particular every `j<=k`.  The function `F` is fixed once and for all and the conclusion holds for
every `k`, so the realized pointwise-finite jet depths are unbounded.  Moreover `B^2` still gives
a common positive contact floor at every natural node; sparsity concerns only the additional
unbounded depth.

Finally, among centered nodes of modulus at most about `R`, only `k=O(R^(1/3))` occur and their
cumulative multiplicity is `sum_(j<=k)(j+1)=O(R^(2/3))`.  This explains exactly why unbounded
depth coexists with exponential type and identifies cumulative multiplicity density as the
surviving local uniqueness invariant.

## Hostile audit

- **Single-witness quantifiers:** `C`, `Q`, `P_Q`, `G`, and `F` are defined once; `k` is quantified only in the conclusion.
- **Multiplicity counted in growth:** first reciprocal sum includes all `k+1` copies and is dominated by the convergent square-reciprocal series.
- **Exact contact:** strict cubic-node injectivity makes raw fiber cardinality exactly `k+1`; centered reflection leaves it unchanged and sharp symmetrization doubles it.
- **Physical nodes:** every `m_k=(k+1)^3` is a natural response order.
- **Jet convention:** order zero and every complex derivative through `k` are included.
- **Package regression:** same FE, Schwarz, order-one, completed-anchor, full-real-axis zero-free, and positive-phase properties survive.
- **Unknown Xi value:** unused; a gauge zero forces the countermodel zero.
- **Identity theorem:** no conflict.  Each node carries only finitely many prescribed derivatives and the weighted divisor has sublinear cumulative multiplicity.
- **Sharp non-kill:** full analytic germ at one node remains unique by the identity theorem; sufficiently dense weighted Hermite data may also be a uniqueness set.

## Novelty audit

Literature through 2026-08-30 treats multiple/Hermite sampling with unbounded multiplicities via
geometric density and separation conditions, including Borichev--Hartmann--Kellay--Massaneda and
Cruz--Massaneda--Ortega-Cerda.  Black-hole response literature treats complex angular momentum,
highest-weight truncation, Gamma/hypergeometric continuation, and dynamical zeta-value towers.
No audited source contains this cross-model theorem: a completed FE--Schwarz positive real-axis
FZZ response with cubic-spaced unbounded Hermite contact and an implanted off-critical quartet.
Novelty claim is the exact route kill and its cumulative-density boundary, not Weierstrass product
existence alone.

## No-go closure (pending proof)

- **Exact killing theorem/mechanism:** sparse multiplicity consumes only summable reciprocal mass, so one order-one positive-square Gamma-null gauge hides linearly increasing jets at cubic-spaced physical orders.
- **Strongest positive survivor:** cumulative jet multiplicity density, rather than boundedness of the depth function, is the necessary local uniqueness invariant.
- **New insight:** any surviving FZZ-P local source selector must prove a quantitative uniqueness-density condition; merely producing arbitrarily high finite jets at selected orders cannot control the completed divisor.
- **Status:** Dependency-closed paper theorem with hostile and novelty audits; Lean formalization pending.

## Log

- 2026-08-30 — frozen as Stage 1 falsifier after corpus and literature audits.
- 2026-08-30 — `[PROVED HERE]`; repeated-divisor growth, exact contact, completed gauge, and hostile audit closed; promoted to Stage 2.
