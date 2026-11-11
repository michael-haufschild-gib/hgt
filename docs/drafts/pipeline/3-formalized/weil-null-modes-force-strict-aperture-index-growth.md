# Null modes force strict aperture index growth

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Targets:** A94; fixed-aperture spectral stability.
- **Statement:** At every real energy `E` and apertures `a<b`, the negative
  index at `b` is at least the negative index plus nullity at `a`.
  On a sufficiently short interval immediately right of `a`, equality holds.

## Connection

`PaperRestrictedWeilInertia` supplies the literal finite-rank positive
repair at every energy. `TheApertureFlowNeverStalls` excludes every
nonzero eigenvector supported in a strictly smaller aperture.

For a nonpositive subspace supported at `a`, the repair at `b` is
injective: a vector killed by the repair has zero energy in the repaired
positive form, hence belongs to the kernel of the original shifted form.
The exclusion theorem forces that vector to vanish. Its dimension is
therefore at most the negative rank at `b`.

Apply this to the negative space plus kernel at `a`. These spaces are
disjoint, their cross form vanishes, and their sum is nonpositive.

## Consequences

Resonant apertures at a fixed energy are finite below every fixed upper
aperture: their negative ranks are distinct natural numbers smaller than
the upper negative rank. More precisely, total null multiplicity on every
finite collection below `b` is at most the negative rank at `b`, by
telescoping the index increments in increasing aperture order.
This controls all null crossings, beyond strict decrease of ground energy alone.

## Exact right-hand jump

If extra negative directions persisted as apertures decreased to `a`,
choose unit vectors orthogonal to the negative space plus kernel at `a`.
Compact physical embedding gives a nonzero nonpositive weak limit; moving
cutoff continuity places it in the form domain at `a`. Orthogonality to
the negative space forces it into the kernel, while orthogonality to the
kernel forces it to vanish. This contradiction gives the upper bound;
strict aperture growth gives the matching lower bound.

## Lean status

All modules passed Lean; umbrella imports complete:

- `HTGeometry/NonpositiveSpacesAvoidingTheKernel`: nonpositive dimension
  bound, negative-space/kernel decomposition, finite nullity.
- `ArithmeticContinuationAndCriticalEnergy/NullModesForceApertureIndexGrowth`:
  `negativeRank_add_nullity_le_of_aperture_lt`, `sum_nullity_le_negativeRank`, and
  `finite_resonant_apertures_below`.
- `SignedArithmeticEnergyIncidence/UnitNonpositiveLimitsDoNotVanish` and
  `ArithmeticContinuationAndCriticalEnergy/NonpositiveRightApertureLimits`:
  nonzero unit weak limits and support descent.
- `ArithmeticContinuationAndCriticalEnergy/TheRightApertureIndexIncludesExactlyTheNullModes`:
  `exists_right_interval_negativeRank_eq`.

Corpus searches found the inputs, but no assembled nullity-plus-index
growth theorem.
