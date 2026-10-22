# Moment-indeterminacy maximal-total-variation universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Lean sources

- `nevLeaf_hasHamburgerMoments`
- `mutuallySingular_leaf`
- `totalVariation_univ_eq_of_isProbability`
- `exists_ne_hasHamburgerMoments`

## Survivor

Every normalized positive Hamburger moment sequence whose kernel is bounded at zero carries a
real-parameter family of probability measures with the same complete moment sequence. Every two
distinct finite-parameter leaves are mutually singular, and the total variation of their signed
difference has mass exactly `2`.

Thus complete equality of all polynomial moments coexists with maximal statistical separation
throughout a continuum family. Existing indeterminacy code proves only distinctness/embedding;
existing fiber code proves pairwise singularity; existing variation code computes the norm after
singularity. Their combination gives the sharp global metric law.

## Proof skeleton

Use the constructed Nevanlinna extremal family and restrict its projective parameter to `ℝ`. Every
leaf represents the original normalized moment sequence. Distinct real parameters have disjoint
measurable denominator fibers, hence mutually singular leaves. Since both leaves are probability
measures, the Jordan decomposition of their signed difference has total mass `1 + 1 = 2`.

## Novelty audit

Pending post-formalization literature search.
