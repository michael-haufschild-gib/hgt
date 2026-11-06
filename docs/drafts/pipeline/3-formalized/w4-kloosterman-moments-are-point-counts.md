# W4 — Kloosterman moments are differences of point counts

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `b ≠ 0`, primitive `ψ`, and `q = #F`, the degree-`m` Kloosterman moment satisfies `(q−1)M_m = q²A_m−qB_m`, where `B_m` counts nonzero tuples with coordinate sum zero and `A_m` also imposes reciprocal sum zero.

## Proof

Scaling the summation variable gives `K(a,b)=K(ab,1)`, so `Σ_a K(a,b)^m` is independent of nonzero `b`. Summing over both parameters and applying orthogonality gives `q²A_m`. The parameter `b=0` contributes `qB_m` by the one-constraint moment identity. The other `q−1` parameters give the claimed equality.

For `m>0`, simultaneous scalar multiplication acts freely on both tuple sets. Normalizing the first coordinate to one gives counts `A'_m,B'_m` with `A_m=(q−1)A'_m`, `B_m=(q−1)B'_m`; hence `M_m=q(qA'_m−B'_m)`.

For positive even `m`, moment positivity gives `B'_m ≤ qA'_m`. A primitive complex character is obtained by composing the standard prime-field character with the field trace, so this incidence inequality holds over every finite field with no character premise.

## Open arithmetic content

The identities identify explicit counting loci for the global moments. Positivity supplies the lower incidence bound, not the upper cancellation bound required for purity. Their cohomological realization and the corresponding ζ family remain open.

## Formalization

`ArithmeticKunnethTheory/WeightFamilies/KloostermanMomentCounts.lean`:

- `kloosterman_moment_count_identity`: `(q−1)M_m=q²A_m−qB_m` in every degree.
- `torusScaleSplit`, `coordinateZeroTorus_card`, `doubleZeroTorus_card`: explicit normalization and orbit counts.
- `kloosterman_moment_projective_counts`: `M_m=q(qA'_m−B'_m)` in positive degrees.
- `normalized_even_incidence`: `B'_m≤qA'_m` in every positive even degree, over every finite field.

Checked with `lake --old env lean`.
