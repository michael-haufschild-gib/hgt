# Joint Marked Moments and the Optimized Zero-Free Half-Plane `Re s > B∗`

- **ID:** jmm-joint-marked-moments-optimized-half-plane
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, external) → Lean formalization
- **Source:** B. Liu, *Joint marked moments and optimized zero-free half-planes for unitary Hecke L-functions*, hexagon:2611.00421v1 (https://hexagonmath.org/pdf/2611.00421v1)
- **Statement:** `L_K(s, ω) ≠ 0` for `Re s > B∗ = (99r∗ − 14)/(12(9r∗ − 1)) = 0.87334585610671857…` for every number field `K` and continuous unitary Hecke character `ω` (norm-character pole permitted), where `r∗ ∈ (0.7523220538, 0.7523220539)` solves `(19(3r−2)(9r+2)/(3(45r−14)))⁵ = 7r⁴(r−2/3)`.

## Goal
Formalize the paper in Lean on corpus building blocks. Lean folder `formal/GaloisForLFunctions/JointMarkedMoments/`, umbrella `JointMarkedMoments.lean` (wired into `MainTheorems.lean`).

## Gates
- [x] 0 → 1  in-progress: source read, dependency map below
- [ ] 1 → 2  fully-proven: paper proof dependency-closed (it is not: analytic inputs below are external)
- [ ] 2 → 3  formalized

## Dependency map
The analytic core (Theorem 8.12, Props 8.6, 8.8–8.11, 8.13, Theorems 8.14, 9.3, 9.4, Cor 9.5) invokes as known the theta, inverse-moment, detector, Mellin-comparison and continuation theorems of Liu [arXiv:2610.26835] and [hexagon:2611.00082] over fields `F ⊃ μ₁₂`, the ordinary-moment face `P + (49/20)S ≤ 99/100` of [2611.00082], the unitary estimates of Hu [2610.00216] and Gao [2611.00334], and Artin formalism for induced Weil-group characters.

Corpus status of those inputs:
- Over `ℚ(ω)` only: `MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean` (`hecke_nonzero`, `Re s > 7/8`) and `MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean` (`hecke_beta_le_sub_seven_eighths`, `β ≤ 20999/24000`). The old count `R_o`, `J_o` of §5 is the corpus `rowCount`/`rowJ`/`rowP`.
- Absent: Hecke `L`-functions over general `F ⊃ μ₁₂`; sextic theta over such `F`; the `κ₁ = 374887/500000` inverse estimate; ordinary character-sum moments; the joint moment induction; unitary families; abelian base change beyond `DirichletBaseChange`.
- §5 (240-stage chain, Theorems 5.2–5.4) and §7.1 (limiting Bernstein cover) are machine-certificate verifications; the certificates are not printed in the paper.

## Lean status
| Paper | Module | Lean |
|---|---|---|
| Prop 4.1, Cor 4.2, count `R_g` | `Detection/TheTwoBranchMinimax` | `detectionExponent_lt_of_ne_minimizer`, `detectionExponent_minimizer_eq`, `minimaxValue_eq_improvedCount`, `hasDerivAt_minimaxValue_intercept`, `hasDerivAt_minimaxValue_slope` |
| Lemma 6.1 | `LimitingRange/TheLimitingImprovement` | `limitImprovement_seven_ninths`, `hasDerivAt_limitImprovement`, `limitSlope_eq_recursionSlope`, `hasDerivAt_limitSlope`, `limitCurvature_pos`, `limitImprovement_tangent_le`, `convexOn_limitImprovement` |
| Prop 6.2 | `LimitingRange/TheMomentRecursionStaysBelowTheLimit` | `propagatedImprovement_thresholdCutoff`, `propagatedImprovement_le_limitImprovement`, `chain_le_limitImprovement` |
| Prop 6.3 | `LimitingRange/TheCeilingOfEarlierMomentRanges` | `stage_total_le_of_class`, `referenceCutoff_identity`, `monotone_ceilingTotal`, `antitone_markCeiling`, `admitted_stage_le_markCeiling`, `available_le_markCeiling`, `markCeiling_eq_limit` |
| (33)–(36), Prop 6.5, B∗ comparisons | `Comparison/TheComparisonBoundary` | `boundaryPoint_mem`, `limitCore_boundaryPoint`, `relativeBoundary_eq`, `comparisonBoundary_bounds`, `tangentSlope_eq`, `tangentIntercept_eq`, `le_relativeBoundary_of_planes`, `comparisonBoundary_lt_markedInductionBoundary`, `markedInductionBoundary_lt_selectedMomentBoundary` |
| §7.2–7.3 planes | `Comparison/TheNecessaryComparisonPlanes` | `numerator_gap_of_planes`, `le_of_halfEndpoint_planes`, `le_of_shortNumerator_planes`, `criticalCount_short_split`, `criticalCount_long_split`, `criticalLength_lt` |
| (47), Prop 8.9, (49), §8.8, (50), (52) | `Induction/TheLargeValueExponents` | `selected_exponents`, `shortClass_bound`, `longClass_value`, `longClass_increment`, `longClass_bound`, `excess_slope_short`, `cutoff_condition_of_condition13`, `referenceKernel_exponents`, `ordinary_side_normalization` |
| Lemmas 8.1, 8.4 | `Arithmetic/GaussSumPowersOfOrderThreeAndSix` | `cubic_gauss_power_identities`, `cube_eq_quadraticChar`, `sextic_duplication`, `sextic_conversion` |
| Lemma 8.2 (injectivity) | `Arithmetic/InjectiveMarks` | `prod_primes_injective` |
| Lemma 9.1 (identity, holomorphy) | `Archimedean/TheAngularHankelMultiplier` | `tateFactor_mul`, `hankelMultiplier_mul_reflect`, `differentiableOn_hankelMultiplier` |
| Lemma 8.3 | `Archimedean/NormScaledFourierHomogeneity` | `fourier_normScaled` |

## Open
- Not yet formalized, self-contained: Prop 6.4 (finite approximation of `G` by rational chains with the fourteen margins), the convex majorant (32) and amplitude model (42)–(43), Lemma 8.7 (reciprocal Euler restoration, unmarked and marked), Lemma 8.5 (coprimality-restricted lattice Poisson), Lemma 8.2 counting bounds, Lemma 9.1 Stirling growth, uniqueness of `r∗` in its interval, the degree-nine minimal polynomial of `B∗`.
- Certificate-dependent: Theorems 5.2–5.4 and the §7.1 limiting cover.
- External analytic inputs listed above: Theorems 8.12, 8.14, 9.3, 9.4, Cor 9.5.
