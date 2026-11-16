# Angular compensation does not preserve the free sixth-power pole

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Obstacle:** O3; no contribution counted.
- **Rejected claim:** Cancelling the completed-column character with a weight-`6k`
  physical test preserves the untwisted free sixth-power pole at `z=1/6` for `k≥1`.

## Exact obstruction

`compensated_angular_physical_row_poisson` transfers `elemPsiSix(A)^k` to the dual
frequency as `elemPsiSix(H)^k`, with a separate fixed-row phase. The actual decomposition
`H=u·generator(P)^6` then contributes `idealPsiSix(P)^(6k) N(P)^(-6z)`.
Consequently the free Euler factor is `grossenEulerProductModS(ψ,6k,S,6z)`.
Its continuation is holomorphic and nonzero at `1/6`; its residue there is zero.

This refutes preservation of that free pole. No factorization of the entire compensated
principal series, or exclusion of every angular detector, is claimed.

## Positive survivor and proof

Exact angular transfer and Mellin normalization survive. Harmonic-Gaussian pairing gives
`M H_(2n)(z)=C^(1−2z) Γ(z+n)/Γ(1−z+n) M W(1−z)`, `C=2π/√3`, for annular Schwartz
sources. For a nonzero nonnegative real source, its sextic-weight value at `1/6` is strictly
positive. Thus the loss of the free pole is arithmetic, despite a nonzero archimedean value.

The arithmetic replacement is exact: multiplicativity and the actual sixth-power
parametrization give weight `6k` on the free ideal. Existing Grössencharacter continuation
and line-one nonvanishing then prove regularity and nonvanishing at `6z=1`.

All dependency-closed statements are formalized and passed final plain Lean checks:

- `AngularPhysicalPoisson.compensated_angular_physical_row_poisson`.
- `AngularMellinTransform.angular_mellin_one_sixth_pos` and `AngularMellinBounds`.
- `AngularSixthPowerFactor.angular_sixthFrequencyWeight`, `angularSixthEulerProduct_eq`,
  `continuedAngularSixthFactor_differentiable`, `continuedAngularSixthFactor_one_sixth_ne_zero`,
  `continuedAngularSixthFactor_zero_residue`.

Umbrellas wired. No external novelty search or axiom checks. The broader rung seed remains open.
