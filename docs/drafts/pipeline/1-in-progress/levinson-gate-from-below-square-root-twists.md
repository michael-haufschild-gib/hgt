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
  `exists_twistedMoment_first_two_derivative_power_saving` proves, for each
  `B≥0`, some `0<a<1` and `C≥0`, eventually uniformly in
  `q∈[T,2T]`, `1/T≤d≤1/40`, `N≤T^θ`, and `|w_n|≤1`,
  `|∂d^j(moment−Re main)|≤C T^(−B)` for `j=1,2`, with taper `η=T^a`.
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
   coefficient specialization is drafted in `TheLinearDetectorHasSmallTaperError.lean`.
3. Prove the differentiated gcd main-term limits for the chosen mollifier,
   and feed the resulting actual detector bound into the gate.
   Existing short coefficient energies omit the full analytic contribution.

## Shifted arithmetic limits

Fixed log-monomial limits do not by themselves justify exponential profiles.
A sufficient uniform estimate is `Q_N(P) ≪ ‖P‖²_{C²}/log N` for `P(0)=0`,
where `Q_N` is the positive gcd form with coefficients
`μ(n)P(log(N/n)/log N)`. The linear-cutoff energy has the unconditional
bound `Q_linear(exp u) ≤ C(1+u)`; its Lean proof is drafted in
`TheLinearSelbergEnergyIsUniformlyBounded.lean`.

The exact representation
`P(x)=P′(0)x+∫₀ˣ(x−v)P″(v)dv` reduces the uniform estimate to linear
cutoffs and the positive totient diagonalization. This transfer and the
mixed higher gcd-log moment limits remain to be formalized. Main-term
jets must differentiate displacement with the mollifier coefficients fixed.
