# The cone count has an Abel completion

- **ID:** the-cone-count-has-an-abel-completion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0111/walls-ledger.md`, Π11f
- **Statement:** The literal cone count has a positive Abel completion satisfying logarithmic Riemann–Roch at every scale.

## Statement
For `C(t)=Σ_{m,n≥1}exp(−2πtmn)` and `t>0`, put
`A(t)=4∫₀∞ C(t cosh v)dv` and
`Ĉ(t)=A(t)+log t+2/√t+c`, where `c=boostLogConstant`.
Explicitly, with `f(v)=θ(e^{2v})−1`,
`c=2∫₀∞(1+e^v)f(v)dv−2`; this constant converges absolutely.
Then the integral converges absolutely,
`Ĉ(t)>0`, `Ĉ(1/t)=tĈ(t)` and `log Ĉ(1/t)−log Ĉ(t)=log t`.
The exact bridge is `A(t)=B(t)=∫ℝ(θ(te^{2u})−1)(θ(te^{−2u})−1)du`.
Consequently `A(1/t)=tA(t)+(1+t)log t+c(t−1)`.
This concerns the pole plane only.

## Proof [PROVED HERE]
Write `t=e^{2x}` and `H_k(u)=exp(−k cosh(2u))`.
For `m,n≥1`, translation by `(log m−log n)/2` gives
`exp(−πt[m²e^{2u}+n²e^{−2u}])=H_{2πtmn}(u+(log m−log n)/2)`.
Each Gaussian pair therefore has integral `∫H_{2πtmn}`.

The bound `cosh(2u)≥|u|` proves integrability of `H_k` for `k>0`.
Put `a=πt`. Since `2πtmn≥2a` and `cosh(2u)≥1`,
`H_{2πtmn}(u)≤exp(−πtmn)H_a(u)`.
The coefficients `exp(−πtmn)` are summable by `summable_coneCount`.
Thus both translated and untranslated kernel families have summable integral norms,
justifying the two exchanges of integral and sum.

The two one-dimensional Gaussian sums give
`(θ(te^{2u})−1)(θ(te^{−2u})−1)=4Σ_{m,n≥1}exp(−πt[m²e^{2u}+n²e^{−2u}])`.
After integration and translation this is `4∫ℝC(t cosh(2u))du`.
Evenness and `v=2u` give `A(t)=B(t)`.
The completed cone count is consequently the already proved positive regularized
boost count. Its reflection and logarithmic laws follow from that exact equality.

## Gates
- [x] Literal source identified; all exchanges have absolute majorants.
- [x] Complete paper proof, with existing theta duality as its only analytic input.
- [x] Lean bridge, convergence and completed-count laws; individual audit and axiom check.

## Lean
Module: `GaloisForLFunctions/LatticeSectionTheory/TheConeCountHasAnAbelCompletion.lean`.
- `integrable_coneCount_cosh`: absolute convergence on the entire boost line.
- `coneAbelCount_eq_gaussianBoostCount`: exact literal cone/boost bridge.
- `coneAbelCount_inv`: explicit logarithmic reflection defect.
- `completedConeCount_pos`, `completedConeCount_inv`, `log_completedConeCount_inv`:
  positivity, reciprocal duality and logarithmic Riemann–Roch.

Individual audit: `lake --old env lean GaloisForLFunctions/LatticeSectionTheory/TheConeCountHasAnAbelCompletion.lean` passed.
Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
Together with the regularized boost count, this closes Π11f. Primitive effectivity remains separate.

## Novelty boundary
The scalar duality is classical Koshliakov duality; see Dixit,
*Character analogues of Ramanujan-type integrals*, Theorem 1.4
([primary source](https://msp.org/pjm/2012/255-2/pjm-v255-n2-s.pdf), printed p. 319).
The new corpus result identifies
the required completion directly on the literal cone count, rather than only its
Mellin value or an unrelated definite lattice.
