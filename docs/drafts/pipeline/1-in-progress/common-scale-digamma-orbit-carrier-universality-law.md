# Common-scale digamma orbit-carrier universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Lean sources

- `hypertranscendental_digamma_orbit_charge`
- `hypertranscendental_comp_add_const_iff`
- `hypertranscendental_comp_const_mul_iff_uncond`
- `hypertranscendental_smul_digamma_affine`

## Survivor

For any finite integer-shift orbit, any nonzero common complex scale, and any complex base shift,
the affine digamma carrier has a sharp two-sided phase law. Nonzero total charge gives global
hypertranscendence. At every jet order `j`, affine pullback contributes exactly `c^j`, and the jet
splits into total charge times the common polygamma carrier plus an exact rational shift tail. Zero
total charge cancels that carrier simultaneously through the entire affine jet tower at every point
off the Gamma pole orbit.

The corpus separately had arbitrary finite orbit charge only at unit scale and arbitrary affine
scale only for a single factor.  Affine argument invariance closes the missing two-dimensional
generality and strictly subsumes both regimes.

## Proof skeleton

Start from the unit-scale finite-orbit carrier. Translate its argument by the arbitrary base shift,
then rescale it by the nonzero common scale using unconditional argument-scaling invariance. For the
full jet law, commute iterated derivatives through the finite charged sum, translate the orbit, and
apply the unconditional affine scaling chain rule. Then apply the all-order orbit-charge decomposition
at the affine base point. The value-level neutral branch is its `j = 0` specialization. The conclusion
is deliberately off-pole: Lean's totalized digamma has pole-junk values, so the corpus does not
support a global differential-algebraic converse.

## Novelty audit

Pending post-formalization literature search.
