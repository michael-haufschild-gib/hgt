# Elliptic additive Haar periodizes over the actual function field

- **Stage:** 2-fully-proven
- **Parent:** [Arithmetic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** For every measurable nonnegative function `f` on the actual
  elliptic adeles, `∫_A f = ∫_D Σ_(z∈K) f(z+d)`, with the audited Haar
  probability on the simple-pole domain `D`.

## Proof

The audited unique simple-pole representative gives exactly one translate
of every adele in `D`. Thus `D` is an additive fundamental domain for the
actual diagonal field. Rational reduction identifies the diagonal subgroup
with the countable function field. The fundamental-domain integral identity
partitions ambient Haar into its diagonal translates of `D`.

The domain measure is the actual subtype pullback of ambient Haar. Its
pushforward is ambient Haar restricted to `D`, so each translated set integral
is exactly an integral against the audited domain probability. Reindexing by
the function field and Tonelli give the claimed identity. The sum of translated
integrals holds even without measurability of `f`.

This is scalar additive unfolding. Relative Bruhat-cell disintegration is
not part of this statement.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticAdditivePeriodization.lean`:
`ellipticAdditiveDomain_isAddFundamentalDomain`,
`lintegral_adeleHaar_eq_tsum_domain`, `lintegral_adeleHaar_periodization`.
Direct audit pending.
