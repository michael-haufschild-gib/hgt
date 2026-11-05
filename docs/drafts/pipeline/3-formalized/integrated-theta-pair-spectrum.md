# Exact theta-pair signs and full-source remainder

- **Stage:** 3-formalized
- **Type:** THEOREM (unconditional, Lean)
- **Wall:** Σ6

For positive integers `n,m`, `r≥0`, and real `b`, put `q=πnm exp r`.
Let `F(τ,q)` be the positive first-atom Bessel-tail density already formalized.
The literal ordered-pair Wigner tail satisfies

`∫_(s>r) Re W_(n,m)(s/2,b) ds`
`=4(πnm)^(-1/2) cos(b(log n−log m)) F(b/2,q)`.

The exact product/ratio identity gives
`W_(n,m)(s/2,b)=exp(s/2) exp(-ib(log n−log m)) Rhat(2πnm exp s,b)`.
The radial transform is real. Substitution `u=πnm exp s` changes its
center integral to `(πnm)^(-1/2)∫_(u>q)u^(-1/2)Rhat(2u,b)du`.
The established radial Fourier-tail identity evaluates this as
`4(πnm)^(-1/2)F(b/2,q)`. Since `q≥π>1+√2`, this factor is strictly positive.

Thus the tail has exactly the cosine's sign. Diagonal pairs are strictly
positive at every frequency; every pair is strictly positive at frequency
zero. For `n≠m`, the frequency `b=π/(log n−log m)` gives a strictly
negative pair tail. This excludes termwise positivity, not positivity of
the complete theta sum.

The positive survivor is the exact all-frequency sign classification and
strict positivity of every diagonal tail, with no frequency cutoff.

## Absolute pair-series remainder

Let `C(τ)=4 Cost(7/2,τ)+6 Cost(3/2,τ)+6 Cost(5/2,τ)`, using
`besselPowerTailCost`. The established power-tail and endpoint bounds give
`|F(τ,u)|≤C(τ)exp(-u)` for `u≥1`.
Writing `q=πexp r`, the absolute pair-tail contribution is at most
`4C(b/2)exp(-qnm)`: `(πnm)^(-1/2)≤1` and the ratio cosine has absolute
value at most one.

For `n,m≥1`, `nm≥n+m−1`. Hence the pair-tail series is absolutely
convergent. Omitting all pairs with `n>M` or `m>M` leaves absolute error
at most

`8C(0) exp(-q(M+1))/(1-exp(-q))²`, uniformly in real `b`.

This follows by covering the omitted set by two geometric half-strips.
For imaginary order, the Schläfli integrand contains `cos(2τt)`, whose
absolute value is at most one. Hence `Cost(p,τ)≤Cost(p,0)` and `C(τ)≤C(0)`.
This gives uniform absolute error. A positive lower bound for the signed
aperture-weighted complete sum remains unproved.

## Ordinary-source reassembly

For `A_n(x)=exp(3x/2)|φ_(n+1)(x)|`, atom translation gives
`∫A_n=(n+1)^(-2)∫A_0`. Each `A_n` is integrable, so `H=∑A_n` is integrable
by the summable `n^(-2)` majorant. The map
`(s,t)↦(s/2+t,s/2−t)` preserves planar Lebesgue measure. Consequently
`H(s/2+t)H(s/2−t)` is integrable on the plane.

On `s>r`, the sum of absolute ordinary-pair Fourier integrands equals
`exp(-3s/2)H(s/2+t)H(s/2−t)`, bounded by the same integrable product times
`exp(-3r/2)`. Dominated summation and Fubini therefore identify the literal
complete-source tail integral with the ordinary-pair tail series. The
uniform rectangular error above then applies to that complete-source tail.

## Formalization

- [ThetaPairCenterTailSpectrum.lean](../../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ThetaPairCenterTailSpectrum.lean):
  `thetaPairCenterTailSpectrum_eq`, `thetaPairCenterTailSpectrum_diagonal_pos`,
  `thetaPairCenterTailSpectrum_unequal_neg`, `abs_thetaPairCenterTailSpectrum_uniform_le`.
- [ThetaPairCenterTailSeries.lean](../../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ThetaPairCenterTailSeries.lean):
  `summable_abs_thetaPairCenterTailSpectrum`, `thetaPairCenterTailSum_remainder_le`.
- [ThetaPairCenterTailReassembly.lean](../../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ThetaPairCenterTailReassembly.lean):
  `thetaPairCenterTailSum_eq_fullSource`, `thetaFullCenterTail_remainder_le`.

All three modules pass direct Lean checks. Transitive capstone axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
