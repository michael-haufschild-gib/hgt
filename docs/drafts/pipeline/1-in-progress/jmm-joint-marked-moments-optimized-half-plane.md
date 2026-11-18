# Joint Marked Moments and the Optimized Zero-Free Half-Plane `Re s > B∗`

- **ID:** jmm-joint-marked-moments-optimized-half-plane
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, external) → Lean formalization
- **Source:** B. Liu, *Joint marked moments and optimized zero-free half-planes for unitary Hecke L-functions*, hexagon:2611.00421v1 (https://hexagonmath.org/pdf/2611.00421v1)
- **Statement:** `L_K(s, ω) ≠ 0` for `Re s > B∗ = (99r∗ − 14)/(12(9r∗ − 1)) = 0.87334585610671857…` for every number field `K` and continuous unitary Hecke character `ω` (norm-character pole permitted), where `r∗ ∈ (0.7523220538, 0.7523220539)` solves `(19(3r−2)(9r+2)/(3(45r−14)))⁵ = 7r⁴(r−2/3)`.

## Goal
Formalize the paper in Lean on corpus building blocks. Lean folder: `formal/GaloisForLFunctions/JointMarkedMoments/`, umbrella `JointMarkedMoments.lean`.

## Gates
- [x] 0 → 1  in-progress: source read, dependency map below
- [ ] 1 → 2  fully-proven: paper proof dependency-closed (it is not: analytic inputs below are external)
- [ ] 2 → 3  formalized

## Dependency map
The paper's analytic core (Theorem 8.12, Props 8.6, 8.8–8.11, 8.13, Theorems 8.14, 9.3, 9.4, Cor 9.5) invokes as "known" the theta, inverse-moment, detector, Mellin-comparison and continuation theorems of Liu [arXiv:2610.26835] and [hexagon:2611.00082] over fields `F ⊃ μ₁₂`, the ordinary-moment face `P + (49/20)S ≤ 99/100` of [2611.00082], the unitary estimates of Hu [2610.00216] and Gao [2611.00334], and Artin formalism for `Ind` of Weil-group characters.

Corpus status of those inputs:
- Over `ℚ(ω)` only: `MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean` (`hecke_nonzero`, `Re s > 7/8`) and `MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean` (`hecke_beta_le_sub_seven_eighths`, `β ≤ 20999/24000`). The old count of §5 (`R_o`, `J_o`) is the corpus `rowCount`/`rowJ`/`rowP` of `FamilyContinuationTheory`.
- Absent: Hecke `L`-functions over general `F ⊃ μ₁₂`; sextic theta over such `F`; the `κ₁ = 374887/500000` inverse estimate; ordinary (non-Möbius) character-sum moments; the joint moment induction; unitary (infinite-order) families; abelian base change beyond the corpus `DirichletBaseChange`.
- §5 (240-stage chain, Theorems 5.2–5.4) and §7.1 (limiting Bernstein cover) are machine-certificate verifications; the paper does not print the certificates.

## Lean plan (self-contained mathematics first)
| Paper | Module | Status |
|---|---|---|
| Prop 4.1, Cor 4.2 | `TheTwoBranchMinimax` | open |
| Lemma 6.1 | `TheLimitingImprovement` | open |
| Prop 6.2 | `TheMomentRecursionStaysBelowTheLimit` | open |
| Prop 6.3, (32) | `TheCeilingOfEarlierMomentRanges` | open |
| (33)–(36), Prop 6.5, Theorem 7.2 value, minimal polynomial | `TheComparisonBoundary` | open |
| §7.2–7.3 necessary planes | `TheNecessaryComparisonPlanes` | open |
| Prop 8.9, (47), (49), §8.8 exponents, (52) | `TheLargeValueExponents` | open |
| Lemmas 8.1, 8.4 | `GaussSumPowersOfOrderThreeAndSix` | open |
| Lemma 8.7 | `ReciprocalEulerRestoration` | open |
| Lemma 9.1 | `TheAngularHankelMultiplier` | open |
| Lemmas 8.2, 8.3 | `InjectiveMarksAndNormScaledFourier` | open |
| Theorems 8.12, 8.14, 9.3; Prop 6.4; §7.1 | — | blocked by the external analytic inputs and certificates above |
