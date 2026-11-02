# Logarithmic duality of the boost count

- **ID:** logarithmic-duality-of-the-boost-count
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0111/walls-ledger.md`, Π11f
- **Statement:** The Gaussian boost average of the positive split cone has an explicit logarithmic reflection defect; subtracting that defect gives a self-dual regularized count.

## Goal
Supply the missing physical logarithmic duality for the split surface. This concerns the pole plane; it supplies no sign for primitive classes.

## Count
Write `θ(t) = Σ_{n∈ℤ} exp(−πtn²)` and
`B(t) = ∫ℝ (θ(te^{2u})−1)(θ(te^{−2u})−1) du`, `t>0`.
The completed boost integral is
`R(t) = ∫ℝ [θ(te^{2u})θ(te^{−2u}) − t^{−1/2}e^{|u|}] du`.
Poisson summation gives `R(1/t)=t R(t)`. The regularized axis contributions produce `log t`.

## Gates
- [x] Well-posed source: the existing Gaussian count and its Poisson identity.
- [x] Absolute convergence and complete paper derivation of the logarithmic term.
- [ ] Lean formalization, individual-file check and transitive axiom audit.

## Existing boundary
`TheIsotropicConeCountsDivisors.lean` proves the Mellin value and double-pole obstruction, but no physical completion. `TheBoostTransformRestoresTheEulerProduct.lean` gives the spectral boost factorization. The new claim must identify an actual convergent count and its correction, not merely square the functional equation of ζ.

## Proof [PROVED HERE]
Set `f(v)=θ(e^{2v})−1`. Poisson gives
`f(−v)=e^v f(v)+e^v−1`, and the existing Gaussian tail bound gives
`0≤f(v)≤4e^{−4v}` for `v≥0`.
Consequently all tails of `f(v)` and `e^v f(v)` are integrable.
For fixed `x`, `f(x+u)f(x−u)≤20e^{−5x−3u}` for `u≥|x|`.

Put `b(x)=B(e^{2x})` and
`r(x)=2∫₀∞[θ(e^{2(x+u)})θ(e^{2(x−u)})−e^{u−x}]du`.
The integrand of `r/2` is exactly
`f(x+u)f(x−u)+f(x+u)+e^{u−x}f(u−x)`.
Thus both integrals converge absolutely. Pointwise Poisson gives
`r(−x)=e^{2x}r(x)`.

Let `I(x)=∫_x∞f(v)dv`, `J(x)=∫_x∞e^v f(v)dv` and
`c=2(I(0)+J(0))−2`.
Splitting tails at zero, then substituting `v↦−v`, gives
`I(x)+J(−x)=I(0)+J(0)+∫₀ˣ(1−e^{−v})dv`.
Hence `r(x)=b(x)+2x+2e^{−x}+c`, and therefore

`b(−x)=e^{2x}b(x)+2x(1+e^{2x})+c(e^{2x}−1)`.

Equivalently,
`B(1/t)=tB(t)+(1+t)log t+c(t−1)` for every `t>0`.
The logarithmic defect is explicit and its constant is an absolutely convergent theta integral.
This proves the Gaussian boost-average face of Π11f. The literal exponential cone count's
dual transform remains to be identified; no primitive effectivity follows.

## Novelty boundary
The scalar transformation is classical Koshliakov duality; see Dixit,
*Character analogues of Ramanujan-type integrals*, Theorem 1.4
([primary source](https://msp.org/pjm/2012/255-2/pjm-v255-n2-s.pdf), printed p. 319).
No novelty is claimed for that identity. The corpus gap is its convergent physical realization
by the split-plane count and the explicit subtraction of the two axes.
