# Higher-subset covariance Fock lift — formalized closure

- **ID:** `ccm-higher-subset-covariance-fock-lift-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-higher-subset-covariance-fock-lift.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCMSubsetCovarianceFock`

Standing on the local-ratio layer of `ccm-local-ratio-second-order-covariance-charge` (already
Stage 3). Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`–`(5)` | `covIndex`, `covFeature`, `covarianceAnomaly_eq_readout` | the subset feature carrier and the scalar readout identity. `covFeature` takes no ambient set: the coordinate `V_V(t)_I` does not depend on `V`, which is what makes `(8)` a triviality rather than a compatibility check |
| low-degree complement | `powerset_filter_card_le_one`, `empty_notMem_image_singleton` | extracted once, reused for the grading and the dimension count |
| `(6)`–`(7)` | `covKernel`, `covKernel_quadratic_form`, `covKernel_quadratic_form_nonneg` | a triple sum interchange plus `conj z * z = ‖z‖²`; no Hilbert space is needed since the carrier is finite dimensional. Stated as an equality with `∑_I ‖∑_j c_j V(t_j)_I‖²`, so it exhibits the positive lift rather than asserting semidefiniteness |
| `(8)` | `covIndex_subset`, `sum_covIndex_extend` | the directed system and the isometry of extension by zero |
| `(9)` | `covGrade`, `sum_covIndex_eq_sum_grades` | the grading by subset size, as the `Ico 2 (m+1)` decomposition; the `V = ∅` case is separated because `Ico 2 1` is empty |
| grade-two closed form | `sum_powersetCard_two` | `∑_{\|I\|=2} ∏_{v∈I} c_v = ((∑c)² - ∑c²)/2`, by induction through `Finset.powersetCard_succ_insert` |
| order of vanishing | `tendsto_covFeature_div_pow` | each degree-`k` coordinate vanishes to order exactly `k` at the seam, with jet `∏_{v∈I} c_v` |
| `(10)`–`(12)` | `tendsto_covFeature_div_sq_of_card_two`, `tendsto_covFeature_div_sq_of_three_le`, `tendsto_covarianceAnomaly_div_sq_eq_gradeTwo` | the quadratic jet of a degree-`k ≥ 3` coordinate is zero, that of a pair is `c_v c_w`, and the whole quadratic jet of the anomaly is the degree-two grade sum: the cofinal curvature charge lives entirely in `H^(2)` |
| `(14)`, `(16)` | `card_covIndex`, `card_covGradeTwo` | the dimensions `2^m - m - 1` and `binom(m,2)` |
| `(15)` | `norm_readout_le`, `norm_readout_ones` | sharp two-sided form: `\|∑_I x_I\| ≤ √(dim) √(∑_I \|x_I\|²)` with equality at the all-ones vector, so `√(2^m - m - 1)` is the norm and the unboundedness claim of section 4 is a theorem |
| `(18)`–`(19)` | `hardyCorner`, `sub_self_mul_sub_self`, `hardyCorner_mul` | the product formula, using only idempotence of the projection, in an arbitrary ring with an arbitrary multiplicative symbol map |
| `(21)`–`(22)` | `hardyCorner_mul_mem`, `hardyCorner_prod_mem` | symbols whose corner lies in a two-sided ideal are closed under multiplication, so every nonempty subset product has its corner in the ideal. Representing the ideal abstractly is the honest formalization: "quasi-inner implies compact" is imported from Connes–Consani and is not proved here |
| `(25)` | `hardyCorner_sum` | `H(C_F) = S_F ∘ 𝓗_F`, additivity of the corner in the symbol; with `norm_readout_ones` this gives the full content of `(25)` |

## Axioms

`#print axioms` on every theorem returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

The card's own `[NOT PROVED]` items and open gates: identification of the finite feature kernel with
the actual Sonin compression or a restricted-Weil kernel, cutoff-uniform weighting, shifted-Xi Pick
index transport, cofinal determinant convergence, and uniform positive Gauss lifting.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
