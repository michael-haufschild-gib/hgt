# Review-0611 §2.1 finite verification (A1–A9)

- **ID:** review-0611-finite-verification
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md)
- **Statement:** Each task A1–A9 gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A1 | `T = 67` done; `T ≈ 10²` needs phases, a computation | `VerifiedHeightRungs/HadamardBudget/`: `rhVerifiedThrough_sixtySeven` |
| A4 | done | `ThetaCuspSections/TheTenthSectionFromHeightSixtySeven.lean`: `thetaCuspCenterMixedSignedHankel_ten_posDef`, `0 < a ≤ ½` |
| A5 | done | `xi_centre_pfSeq_twoHundred`, `xiSliceCoeff_nonneg_of_abs_le_band` (`\|t\| ≤ 133/2`), `re_xiLiPaired_nonneg_of_le` |
| A2 | partial: theta `D` and the mass floor reduced; `windowHeight` unchanged | `ThetaCuspSections/EverySectionFromItsVerifiedHeight.lean`, `SquareRootThreshold/EffectiveHorizons/TheZeroMassHasItsSecondTerm.lean`, `VerifiedHeightRungs/JensenEntries.lean`, `VerifiedHeightRungs/HeatGridEntries.lean`, `SquareRootThreshold/EffectiveHorizons/TheEGCContourIsExplicit.lean` |
| A8 | done below `27/5`: one finite template decides every `k`; no finite template exists from `27/5` on; no exact horizon on `[27/5, 6)` | `WindowTowerOfSpecZ/FiniteTemplatesBelowTwentySevenFifths.lean`: `tateFunction_nonneg_iff_template`, `exists_finite_hecke_template_iff` |
| A3, A6, A7, A9 | open | |

## A1: the Hadamard budget replaces Turing's method

An off-line zero `ρ = ½+δ+iγ` and its reflection contribute `≥ 2/a` to the positive Hadamard sum
`Re ξ'/ξ(½+a+iγ)` for every `a > ½`, an on-line simple zero only `1/a`. So
`Re ξ'/ξ(½+a+it) < 2/a` on `t ≤ T` proves `RHVerifiedThrough T` with no zero computed at all.
Pairs of close zeros are the only obstruction: the first failure is at the pair near `t ≈ 295`.

Fejér smoothing in `t` replaces the Dirichlet series by a finite polynomial and keeps positivity:
with `Λ_L(u) = (1−|u|/L)₊`, `σ = ½+a`, an off-line zero at height `γ` forces

`2∫₀^L Λ_L(u) e^{−au} du ≤ Arch(γ) − Σ_{log n<L} Λ(n) n^{−σ} Λ_L(log n) cos(γ log n)`.

`Arch(γ) ≈ ½ log(γ/2π)`. The left side is `≈ 2/a` for large `L`. Numerics (uncertified):

| `a` | `L` | terms | first failure | margin at 100 |
|---|---|---|---|---|
| 0.6 | 5 | 47 | 150 | 0.33 |
| 0.6 | 6 | 98 | 185 | 0.47 |
| 0.55 | 8 | 465 | 295 | 0.74 |

Past `295`: subtract certified on-line zeros at the close pairs (`hardyZ` sign changes).

## Progress

- **A1:** `HadamardBudget/TheVerifiedHeightSixtySeven.lean`: `rhVerifiedThrough_sixtySeven`, by hand, no zero or value of `ζ` located. The worst-phase budget (Kronecker limit) cannot pass `T ≈ 80`. Past it, phase information is needed: that is a finite computation, excluded by the goal's rule.
- **A5:** `xi_centre_pfSeq_twoHundred` (`PF_200`), `xiSliceCoeff_nonneg_of_abs_le_band` (`|t| ≤ 133/2`), `re_xiLiPaired_nonneg_of_le` (`n ≤ 314`).
- **A4:** rank 10 from height 66. Cubic `D(N+1)³` is an artifact of factorial Hankel bounds. Replaced by: parity reduces rank 10 to polynomials of degree `≤ 4` in `t = b²`; Legendre reproducing kernel on `t ∈ [1, 25]`; explicit tail `|current a b| ≤ 6.05·10⁹ a e^{−(7/5)|b|}`; core floor `≥ 6·10⁻⁴ a` on `|b| ≤ 5` from `2 + γ − log 4π` and `Ξ(b) ≥ Ξ(0)(1 − (b²/2)Σ1/|ρ−½|²)`.
- **A2, theta `D`:** `thetaCuspCenterMixedSignedHankel_posDef_of_rhVerifiedThrough`: rank `N` at `0 < a ≤ ½` from RH through `40 + 6(N+2)log(N+2) + 1`. The older `exists_signedHankel_posDef_of_rhVerifiedThrough` covers `a ≤ 3/4` with an unspecified `D`.
- **A2, mass:** `abs_xiSymmetricMass_sub_sharp_le`: `|M(T) − (T/π)(log T − log 2π − 1)| ≤ 80 + 65 log T` for `T ≥ 8`. The Jensen, heat and EGC rungs now start at `e¹²` in place of `xiMassHeight (1/100) = e⁴⁰⁰⁰ + 1`: `jensenNonrealCount_eq_zero_of_verified` has no height floor for `d ≥ 1`; `heatGridHeight` has floor `4e¹²`.
- **A2, open:** `windowHeight` is still iterated-exponential. Its size comes from `gapHeight` and the Lagrange constant `48^{2n}`. `HausdorffShifts` still uses `xiMassHeight (1/500)`.
- **A8:** finite templates end at spread `27/5`, not `6`. Moves `q ↦ 81q/80` (`q < 16/15`), `q ↦ 15q/16` (`q ≥ 16/15`) stay in `[1, 27/25)`, are paths of ratio-2,3,5 edges inside `[1, 27/5)`, and lower `v₂` by 4 each. Below `27/5`, five shears reduce to two generators on `[1, X/5)`, where orbits exit by pigeonhole and ratio persistence. The template is existential, not listed.
- **A3, A6, A7, A9 (no theorem):** A3 needs rigorous Galerkin or a far lower `windowHeight`. A6 and A7 are numerical certificates. A9 has no precise statement yet: size certificates die at `E_c ≥ 1`, `c* ∈ (½log 5, ½log 6]`, and a window reading of A9 at `2c < log 16` is stronger than A3. All are unattempted in Lean.
