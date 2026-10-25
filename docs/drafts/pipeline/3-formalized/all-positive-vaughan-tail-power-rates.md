# Vaughan tail powers at every positive damping

- **ID:** all-positive-vaughan-tail-power-rates
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Verification:** All five targets passed producing and final direct Lean checks, with standard axioms only and no warnings. The module is wired and its owned scratch removed.
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** For every `ε>0`, a fixed power gain in the signed reciprocal tail or normalized square empty-leg energy is equivalent to `zetaZeroAbscissa<1`.

## Source argument

The restriction `ε≤1` in the checked inverse Abel proof enters only through
`rpow_one_add_increment_le`. The source theorem
`RHTower.abs_rpow_sub_rpow_le_of_le` in `PolynomialFockLocalBregman.lean` gives

`|(n+1)^(1+ε)-n^(1+ε)| ≤ (1+ε)(2n)^ε`

for `ε≥0`, `n≥1`. Its proof uses the tangent inequality for real powers.
Thus the finite Abel inverse works with `(1+ε)2^ε` in place of `1+2ε`, without
an upper restriction on the damping. All remaining factors and the subcritical
power sum depend on the saving `0<η<1`, not on an upper bound for `ε`.

The forward Mertens-to-tail theorem and both directions of the quartic
empty-leg comparison already hold at every positive damping. Consequently the
fixed-strip equivalences, and the exact decay-index proof using them, extend to
all `ε>0`. When `ε>1/2`, the normalizing power `N^(2-4ε)` decreases;
the algebraic quartic comparison remains valid in that range.

## Audit

The increment source and existing inverse, forward, and quartic proofs have been
read. The corpus search found the existing restricted Vaughan equivalence and
general Abel-tail results, without this all-positive-damping specialization.
All five declarations in `VaughanTailPowerGainsAtEveryPositiveDamping.lean`
passed direct Lean checks. Their transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`:

- `rpow_one_add_increment_le_of_nonneg`
- `abs_sum_moebiusReal_le_of_reciprocalTail_bound_all_dampings`
- `zetaZeroAbscissa_lt_one_of_vaughan_reciprocalTail_power_all_dampings`
- `zetaZeroAbscissa_lt_one_iff_vaughan_reciprocalTail_power_all_dampings`
- `zetaZeroAbscissa_lt_one_iff_vaughan_square_energy_power_all_dampings`

The module is imported by the programme umbrella. Its exact missing dependency
`TheEmptyVaughanLegDetectsAFixedStrip.lean` was produced separately; its prior
final audit remains valid. No power saving or positive zero-free width is asserted.
