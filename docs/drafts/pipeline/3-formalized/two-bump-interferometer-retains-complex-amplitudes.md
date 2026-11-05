# The two-bump interferometer retains complex amplitudes

- **ID:** two-bump-interferometer-retains-complex-amplitudes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A36, interferometer obligation.
- **Lean:** `SquareRootThreshold/EvenAndOddTwoBumpTestsDecideTheCriticalLine.lean`.

## Exact statement and proof

For a tempered configuration, a `C²` bump supported in `[-w,w]`, and
`0≤v`, `v/2+w≤a`, positivity on the aperture `[-a,a]` gives
`‖S(v)‖≤Re S(0)` (`norm_lagStructure_le_re_zero_of_weil_nonneg`).
The existing two-bump minor bound and reflection identity
`conj S(-v)=S(v)` prove this directly.

For `z=δ+iγ` and arbitrary complex coefficient `c`, the reflected pair is

`c exp(zv)+conj(c) exp(-conj(z)v)
 =2 exp(iγv)(Re(c) cosh(δv)+i Im(c) sinh(δv))`.

Splitting the exponentials and real and imaginary parts proves
`reflectedLagPair_eq_cosh_sinh`. Reflection conjugates the actual lag
coefficient, giving `lagCoeff_reflected_pair_eq`. A cosh-only expression
requires a real coefficient.

## Verification

Direct source check and six transitive axiom audits passed, including the
existing `W_twoBump`, `norm_lagStructure_le_of_weil_nonneg`, and
`conj_lagStructure_neg`. Dependencies use only `propext`, `Classical.choice`,
and `Quot.sound`. The owning umbrella already imports this module.
The other A36 obligations remain open on their separate card.
