# Graded self-recurrence from zero density

- **Stage:** 3-formalized
- **Source:** `docs/reports/review-0911/fable.md`, §11.6.

## Target

Fix `1/2≤σ≤5/6` and `c>(30/13)(1−σ)`. If `ζ(ρ)=0` and
`σ<Re ρ<1`, some disc `D` about `ρ` and tolerance `ε>0` have the following
property: for all sufficiently large `T`, every one-separated finite set
of `ε`-self-returns on `D` inside `[0,T]` has cardinality less than `T^c`.
Thus sufficiently frequent separated returns exclude a zero at the centre.

## Proof mechanism

Choose an isolating disc of radius below `1/2`, contained in `σ<Re s<1`.
Rouché transports its central zero to every return disc. One-separated
returns give distinct transported zeros. A fixed low-height range contains
only finitely many zero copies. Above that range, sum the Guth–Maynard
dyadic density bound; its extra logarithm and the original polylogarithmic
factor are absorbed by the strict exponent margin `c>(30/13)(1−σ)`.

## Existing inputs

- `exists_zero_of_mem_zetaReturnSet`: Rouché transport.
- `exists_sphere_norm_ge_of_analyticAt_of_not_eventually_zero`: arbitrarily
  small isolating circles with positive boundary floor.
- `zeroCopyRange_subset_iUnion`: dyadic cover of a cumulative zero range.
- `exists_zeroHeightBox_ncard_le_fixed_thirty_thirteenths` with
  `GuthMaynard.guthMaynardLargeValuesBound_holds`: unconditional density.

The known power-saving return-measure theorem uses Ingham–Huxley and does
not supply this explicit exponent or the separated finite-set statement.

## Lean

`ZeroConfigurationGeometry/Recurrence/GradedZeroCounts.lean` and
`GradedSelfRecurrence.lean`:

- `exists_zeroCopyRange_le_rpow_guthMaynard`.
- `exists_eventually_card_zeta_returns_lt_rpow`.
- `zeta_ne_zero_of_graded_disc_returns`.

Both modules passed direct `lake --old env lean` audits. Transitive axioms:
`propext`, `Classical.choice`, `Quot.sound`. Imported by
`ZeroConfigurationGeometry.lean`.
