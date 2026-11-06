# W4 — the torus critical points have a constant Tate trace

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Every normalized critical point of the reciprocal double-zero locus is defined over the prime field. Its critical-point count is unchanged by finite field extension. In characteristic different from two, with `m+1` homogeneous coordinates, the count is `Σ_{0≤r≤m, (m+1)=2r in F} binom(m,r)`.

## Proof mechanism

The checked theorem `normalizedDoubleZeroTorus_critical_iff` identifies critical tuples with sign coordinates. A subset of the `m` free coordinates specifies the negative signs. Both vanishing-sum equations reduce to `(m+1)=2r` in the field, where `r` is the subset size. Distinct subsets give distinct tuples when `2≠0`. In characteristic two, only the all-one tuple remains, and it belongs exactly when `m+1` vanishes in the field. Field embeddings preserve and reflect these equations.

Coordinatewise application of any field embedding is injective on torus tuples, preserves and reflects both sum equations, and is surjective on the critical locus because every sign descends. This proves equal cardinalities directly, without a characteristic restriction. The resulting extension trace has eigenvalue `1` once for each actual critical point.

## Scope

This determines the zero-dimensional critical-locus trace. It supplies neither the exceptional quadric trace of a resolution nor the compactification's cohomological trace formula.

Fresán–Sabbah–Yu, [§5.1.2–5.1.4](https://perso.pages.math.cnrs.fr/users/claude.sabbah/articles/kloosterman-revised10.pdf), classify sign singularities of the related Laurent hypersurface `Σ(y_i+1/y_i)=0`. The present target concerns the actual normalized projective double-zero locus already used in the Lean moment identity; no scheme-theoretic singularity or cohomology theorem is assumed.

## Lean

[`CriticalPointTateTrace.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/CriticalPointTateTrace.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `momentTorusMap_mem_double_iff`, `momentTorusMap_signs_descend`: preservation, reflection, and sign descent.
- `reciprocalTorusCriticalPoints_card_embedding`, `criticalPointTateTrace_extension_count`: the constant trace over every finite extension.
- `criticalSignSubsets_card`, `reciprocalTorusCriticalPoints_card`: negative-coordinate parametrization and the exact binomial sum when `2≠0`.
- `reciprocalTorusCriticalPoints_card_char_two`: count one or zero according as `m+1` vanishes or does not vanish.

Direct Lean check passed. The next local input is the [transverse quadric trace](../1-in-progress/w4-transverse-quadric-trace.md).
