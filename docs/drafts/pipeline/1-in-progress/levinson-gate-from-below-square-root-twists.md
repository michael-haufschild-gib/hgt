# Levinson's gate from the two-main-term twisted moment

- **ID:** A111
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Produce an unconditional positive critical-zero proportion through the
Levinson detector, using mollifier length `T^θ`, `θ<1/2`.

## Proved inputs

`exists_twistedMoment_power_saving` gives the actual mollified zeta moment
with both gcd main terms, uniformly in bounded real coefficients and real
displacement. Its error has arbitrary power saving.
`RHTower.levinsonReciprocalLogMeanSquareGate_of_dyadicLaw` converts an actual
dyadic detector bound into the positive-weight Levinson gate. Gate-to-count
arguments and scalar optimization are already proved.

Four modules in `MultiscaleMollifiedZetaField` now close derivative transfer:

- `RealParameterErrorsKeepTheirDerivatives`: the local Landau estimates
  `|f′|≤2E/h+M₂h/2` and `|f″|≤4E/(hk)+M₂k/h+M₃h/2`.
- `TheTwistedMomentHasPolynomialDerivatives`: the opposite-height product
  continues the actual squared moment holomorphically. Every displacement
  jet is bounded by `n!·8^n (q−p+2η)[(2+8(q+η+1))N]²`.
- `TheTwistedMainTermsHavePolynomialDerivatives`: the finite gcd polynomials,
  entire zeta residue factor, and chi-modulus bound give main-term norm
  `≤ C N²(q−p+2η)(1+e²(q+η+2)²)/d` on `|z−d|≤d/2`.
  Cauchy's estimate controls every main-term jet.
- `TheTwistedMomentErrorKeepsItsDerivatives`:
  `exists_twistedMoment_first_three_jet_power_saving` proves, for each
  `B≥0`, some `0<a<1` and `C≥0`, eventually uniformly in
  `q∈[T,2T]`, `1/T≤d≤1/40`, `N≤T^θ`, and `|w_n|≤1`,
  `|∂d^j(moment−Re main)|≤C T^(−B)` for `j=0,1,2`, with one common taper `η=T^a`.
  The jets are literal real derivatives. Curvature and third derivatives
  are `O(T^10)`; steps `h=T^(−B−12)`, `k=T^(−2B−24)` transfer the
  undifferentiated error of order `T^(−4B−40)`.

All four passed direct Lean checks and are imported by the umbrella.
No detector gate from these inputs is yet claimed.

## Three-moment detector identity

For a smooth compact taper `W`, set `F=ζΨ`, `G=λζΨ′`, `H=F−G`,
and `q_J(d)=∫W|J(1/2−d+it)|²`. Polarization and integration by parts give

`∫W|(ζ+λζ′)Ψ|² = q_H − (λ/2)(q_F′−q_G′+q_H′) + (λ²/4)q_F″`
`+ λ∫W′ Im(F conj G) + (λ²/4)∫W″|F|²`.

The three coefficient sequences are `w_n`, `−λ log(n)w_n`, and
`(1+λ log(n))w_n`; fixed rescaling puts each within the coefficient bound.
Derivatives of `q` are in displacement, those of `W` in height, and
those of zeta and the mollifier are complex derivatives.

## Remaining proofs

1. Identify moment jets with their kernel integrals and formalize the exact
   three-moment identity. `CauchyJetsOfTheTwistedMoment.lean` now proves
   exact differentiation under the moment integral at every order; Lean
   check passed and umbrella import added.
   `TheDetectorEnergyComesFromThreeMoments.lean` proves the weighted
   holomorphic-field identity, with both taper terms; Lean check passed
   and umbrella import added. The literal zeta-detector specialization
   `TheMollifiedDetectorHasTheThreeMomentIdentity.lean` also passed
   its Lean check and is imported by the umbrella.
2. Bound taper terms. The existing thin-strip Weyl theorem gives
   `|ζ|≪t^(3/16)` near the critical line. The normalized linear mollifier
   has norm `≤2 sqrt(N)`, so squared-product envelopes are `O(T^(7/8))`
   for `N≤sqrt(T)`. `TheDetectorTaperTermsAreSmall.lean` proves exact
   edge-supported derivative bounds and their actual mollified-field
   specialization; its direct Lean check passed. The linear-mollifier
   coefficient specialization `TheLinearDetectorHasSmallTaperError.lean`
   passed its Lean check: both literal edge terms together are `O(T^(7/8))`.
   `TheDetectorMomentErrorsAreSmall.lean` passed its direct check.
   `exists_linearDetector_main_remainder_bound` proves that the literal
   detector integral differs from `detectorThreeMomentMain` by at most
   `C T^(7/8)`, uniformly for `q∈[T,2T]`, `1/T≤d≤min(r,1/40)`,
   `1<N≤T^θ`, `0≤λ≤1`, and `λ log N≤1`, with one taper `T^a`.
   Quadratic homogeneity supplies the residual coefficient bound two.
3. Prove the differentiated gcd main-term limits for the chosen mollifier,
   and feed the resulting actual detector bound into the gate.
   Existing short coefficient energies omit the full analytic contribution.

## Shifted arithmetic limits

For `L=log N`, the required polynomial-profile limit is

`L Σ μ(h)μ(k) (hk)^(v/L) gcd(h,k)^(1+c/L)/(hk)`
`  ·P(log(N/h)/L)P(log(N/k)/L)`
`→ ∫₀¹ exp((c+2v)t)[P′(1−t)−vP(1−t)]² dt`.

This limit and its first two parameter derivatives remain unproved here.
For the linear detector, `P` has degree at most two. At the evaluation
point, direct and reflected terms have `(v,c)=(u,−2u)` and `(−u,2u)`,
where `u=dL`; both diagonal exponentials cancel. The linear-profile
constants predicted by the limit are `1−u+u²/3` and `1+u+u²/3`.
Main-term jets must hold mollifier coefficients fixed while differentiating.

A direct route uses the bounded smoothed Möbius kernel
`F(y)=Σ_{n≤exp y} μ(n)(y−log n)/n`, which tends to one.
Twice-integrated finite-sum identities transfer this to power shifts
`n^(v/L)`. The remaining arithmetic input is uniform summability of the
shifted Euler correction: its local factor, with
`a=p^(−1+v/L)` and `b=p^(−1+(c+2v)/L)`, is
`1−xy(a−bx)(a−by)/((1−ax)(1−ay))`.

The direct kernel step is proved in `TheSmoothedMobiusKernelTestsDerivatives.lean`:
for each twice continuously differentiable `f` with `f(0)=0` and fixed `u>0`,
`L Σ_{n≤exp(Lu)} μ(n) f(u−log(n)/L)/n → f′(u)`.
The finite identity uses `f′(0)F(Lu)+∫₀ᵘ f″(u−x)F(Lx)dx`.
Taking `f(x)=x exp(−vx)` gives the power-shifted linear limit `1−vu`.
The module passed its direct Lean check and is imported by the umbrella.
