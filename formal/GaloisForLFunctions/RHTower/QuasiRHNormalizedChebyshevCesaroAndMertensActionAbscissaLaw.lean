import GaloisForLFunctions.RHTower.QuasiRHPowerMeshSquareSampleAndObserverJetAbscissaLaw
import GaloisForLFunctions.RHTower.QuasiRHMeanSquareAbscissa
import GaloisForLFunctions.RHTower.NormalizedChebyshevCesaroAndSqrtRieszBridge

/-!
# Quasi-RH Abscissa Laws IV: Exact Triadic Cesàro–Mertens Syzygy, Normalized Chebyshev Cesàro Sum, Square-Root Riesz Action, and Mean-Square Abscissa Bridges

This module connects four further sectors of the `RHTower` corpus to support unconditional proofs
of the quasi-RH strips `1/6 ≤ Re(ρ) ≤ 5/6` (`zetaZeroAbscissa ≤ 5/6`) and
`1/4 ≤ Re(ρ) ≤ 3/4` (`zetaZeroAbscissa ≤ 3/4`):

1. **Exact Pointwise Recombination & Triadic Cesàro–Mertens Syzygy (`Section 1`):**
   At every integer `d ≥ 2`, `integerLag d = lagBracket d / √d` satisfies the exact identity
   `integerLag d + (ψ(d) - d) / √d - √d * (mertensSum d - log d + γ) = (trivialZeroSeriesReal d - log(2π)) / √d`.
   Summing over `k < M - 2` (`d = k + 2`) yields an exact identity relating the three fundamental
   Cesàro sums `integerLagCesaroSum M`, `chebyshevNormalizedCesaroSum M`, and
   `mertensDeviationSqrtAction M` with a purely Archimedean `O(√M)` remainder bounded by
   `2 * (1 + log(2π)) * √M`. Taking the convex combination
   `(1 / 2) * integerLagLinearCesaroAction M + (1 / 4) * integerLagMertensSqrtAction M` cancels the
   unaveraged terminal boundary term `M * integerLag M` identically and matches
   `chebyshevNormalizedCesaroSum M` within `2 * (1 + log(2π)) * √M` for all `M : ℕ`.

2. **Master Linear-Bridge Abscissa Transfer Package (`Section 2`):**
   For any sequence `F : ℕ → ℝ` and scale `α > 0` satisfying a uniform `O(M)` linear bridge
   `|mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * M` for all `M ≥ 3`, we establish in one
   unified mechanism:
   - the `M ≥ 2` normalized `O(1)` comparison `|mobiusDivisorSquareRootAbelMoment M / M - α * (F M / M)| ≤ D`,
   - unconditional forward `zetaZeroAbscissa` subpower bounds (`∀ ε > 0`),
   - one-sided upper and lower strip laws on power-gap sets, on all `M ≥ 3`, and along any `m`-th
     power mesh `M = j^m` (`m ≥ 1`),
   - exact `sInf` abscissa formulas on the full grid and along any `m`-th power mesh, and
   - cumulative mean-square energy (`∑_{2 ≤ k ≤ N} (F k / k)^2`) abscissa laws and exact `sInf`
     exponent formulas (`2 * zetaZeroAbscissa`).

3. **Boundary-Free Normalized Chebyshev Cesàro Sum & Square-Root Riesz Action Abscissa Laws (`Section 3`):**
   Instantiating Section 2 for `chebyshevNormalizedCesaroSum M = ∑_{k < M - 2} (ψ(k + 2) - (k + 2)) / √(k + 2)`
   (whose summands are completely independent of `M`, with no Mertens sum, no `γ`, and no floor
   quotient) and `vonMangoldtSqrtRieszAction M = ∑_{k < M - 2} (√M - √(k + 3)) (Λ(k + 3) - 1)` yields
   unconditional forward bounds, one-sided full-grid and `m`-th power mesh strip laws, exact `sInf`
   abscissa formulas, cumulative mean-square energy equivalences, and explicit `5/6` (`c = 1/3`,
   mean-square `r = 5/3 + ε`) and `3/4` (`c = 1/4`, mean-square `r = 3/2 + ε`) strip criteria.

4. **Terminal-Lag / Mertens-Deviation & Linear–Cesàro Action Abscissa Laws (`Section 4`):**
   Instantiating Section 2 for `integerLagMertensSqrtAction M`, `integerLagMertensCanonicalAction M`,
   and `integerLagLinearCesaroAction M` yields their forward bounds, one-sided full-grid and `m`-th
   power mesh strip laws, exact `sInf` formulas, cumulative mean-square energy laws, and direct
   tradeoff criteria between `M * integerLag M`, `mertensDeviationSqrtAction M`, and
   `integerLagCesaroSum M`.
-/

open Complex Real Filter Topology MeasureTheory Finset
open scoped BigOperators ArithmeticFunction Chebyshev
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Section 1: Exact Pointwise Recombination & Triadic Cesàro–Mertens Syzygy -/

/-- **Exact Pointwise Recombination of `integerLag`, Normalized Chebyshev Error, and Mertens Deviation:**
For every integer `d ≥ 2`, the `√d` denominator in `integerLag d = lagBracket d / √d` cancels one
factor of `d = √d * √d` in `d * (mertensSum d - log d + γ)`, yielding the exact identity
`integerLag d + (ψ(d) - d) / √d - √d * (mertensSum d - log d + γ) = (trivialZeroSeriesReal d - log(2π)) / √d`. -/
theorem integerLag_add_chebyshev_div_sqrt_sub_sqrt_mul_mertensDeviation_eq
    {d : ℕ} (hd : 2 ≤ d) :
    integerLag d + (Chebyshev.psi (d : ℝ) - (d : ℝ)) / Real.sqrt (d : ℝ) -
        Real.sqrt (d : ℝ) *
          (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant) =
      (trivialZeroSeriesReal d - Real.log (2 * Real.pi)) / Real.sqrt (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd0.le
  rw [integerLag_eq_lagBracket hd]
  unfold lagBracket
  have h1 :
      (d : ℝ) * (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant) =
        (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) *
          (mertensSum d - Real.log (d : ℝ) + Real.eulerMascheroniConstant) := by
    rw [hsq]
  rw [h1]
  field_simp [hsd.ne']
  ring

/-- Purely Archimedean / trivial-zero Cesàro remainder
`∑_{k < M - 2} (trivialZeroSeriesReal (k + 2) - log(2π)) / √(k + 2)`. -/
def archimedeanCesaroSqrtRemainder (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (trivialZeroSeriesReal (k + 2 : ℕ) - Real.log (2 * Real.pi)) / Real.sqrt (k + 2 : ℕ)

/-- **Exact Cesàro Recombination Identity:**
For every `M : ℕ`, the Weil integer-lag Cesàro sum, the boundary-free normalized Chebyshev Cesàro
sum, and the square-root-weighted Mertens-deviation action satisfy the exact identity
`integerLagCesaroSum M + chebyshevNormalizedCesaroSum M - (1 / 2) * mertensDeviationSqrtAction M = archimedeanCesaroSqrtRemainder M`. -/
theorem integerLagCesaroSum_add_chebyshevNormalizedCesaroSum_sub_half_mertensDeviationSqrtAction_eq
    (M : ℕ) :
    integerLagCesaroSum M + chebyshevNormalizedCesaroSum M -
        (1 / 2 : ℝ) * mertensDeviationSqrtAction M =
      archimedeanCesaroSqrtRemainder M := by
  unfold integerLagCesaroSum chebyshevNormalizedCesaroSum mertensDeviationSqrtAction
    archimedeanCesaroSqrtRemainder
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have h := integerLag_add_chebyshev_div_sqrt_sub_sqrt_mul_mertensDeviation_eq
    (d := k + 2) (by omega)
  linarith

/-- **Exact Triadic Syzygy Between `integerLagLinearCesaroAction`, `integerLagMertensSqrtAction`,
and `chebyshevNormalizedCesaroSum`:**
Taking `(1 / 2) * integerLagLinearCesaroAction M + (1 / 4) * integerLagMertensSqrtAction M` cancels
the unaveraged terminal boundary term `M * integerLag M` identically (`(1/2)*(4/3) + (1/4)*(-8/3) = 0`),
yielding `-archimedeanCesaroSqrtRemainder M` after subtracting `chebyshevNormalizedCesaroSum M`. -/
theorem half_integerLagLinearCesaroAction_add_quarter_mertensSqrtAction_sub_chebyshevNormalizedCesaroSum_eq
    (M : ℕ) :
    (1 / 2 : ℝ) * integerLagLinearCesaroAction M +
        (1 / 4 : ℝ) * integerLagMertensSqrtAction M -
        chebyshevNormalizedCesaroSum M =
      -archimedeanCesaroSqrtRemainder M := by
  have h := integerLagCesaroSum_add_chebyshevNormalizedCesaroSum_sub_half_mertensDeviationSqrtAction_eq M
  unfold integerLagLinearCesaroAction integerLagMertensSqrtAction
  linarith

/-- Unconditional `O(√M)` bound on `archimedeanCesaroSqrtRemainder M` for all `M : ℕ`. -/
theorem abs_archimedeanCesaroSqrtRemainder_le (M : ℕ) :
    |archimedeanCesaroSqrtRemainder M| ≤
      2 * (1 + Real.log (2 * Real.pi)) * Real.sqrt (M : ℝ) := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hlog0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg hpi
  unfold archimedeanCesaroSqrtRemainder
  have hterm : ∀ k ∈ Finset.range (M - 2),
      |(trivialZeroSeriesReal (k + 2 : ℕ) - Real.log (2 * Real.pi)) /
          Real.sqrt (k + 2 : ℕ)| ≤
        (1 + Real.log (2 * Real.pi)) *
          (shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k) := by
    intro k _
    have hk1 : (1 : ℝ) ≤ (k + 2 : ℕ) := by exact_mod_cast (show 1 ≤ k + 2 by omega)
    have hsk : 0 < Real.sqrt (k + 2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hS0 : 0 ≤ trivialZeroSeriesReal (k + 2 : ℕ) := trivialZeroSeriesReal_nonneg hk1
    have hS1 : trivialZeroSeriesReal (k + 2 : ℕ) ≤ 1 := trivialZeroSeriesReal_le_one hk1
    have hnum :
        |trivialZeroSeriesReal (k + 2 : ℕ) - Real.log (2 * Real.pi)| ≤
          1 + Real.log (2 * Real.pi) := by
      rw [abs_le]
      constructor <;> linarith
    rw [shiftedHarmonicSqrtPrefix_succ_sub, abs_div, abs_of_pos hsk, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)
  have htel :
      (∑ k ∈ Finset.range (M - 2),
          (1 + Real.log (2 * Real.pi)) *
            (shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k)) =
        (1 + Real.log (2 * Real.pi)) * shiftedHarmonicSqrtPrefix (M - 2) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => shiftedHarmonicSqrtPrefix k),
      shiftedHarmonicSqrtPrefix_zero, sub_zero]
  have hpref_le : shiftedHarmonicSqrtPrefix (M - 2) ≤ 2 * Real.sqrt (M : ℝ) := by
    rcases lt_or_ge M 2 with hM2 | hM2
    · have h0 : M - 2 = 0 := by omega
      rw [h0, shiftedHarmonicSqrtPrefix_zero]
      positivity
    · linarith [(shiftedHarmonicSqrtPrefix_sub_two_bounds hM2).1]
  calc
    |∑ k ∈ Finset.range (M - 2),
        (trivialZeroSeriesReal (k + 2 : ℕ) - Real.log (2 * Real.pi)) /
          Real.sqrt (k + 2 : ℕ)| ≤
      ∑ k ∈ Finset.range (M - 2),
        |(trivialZeroSeriesReal (k + 2 : ℕ) - Real.log (2 * Real.pi)) /
          Real.sqrt (k + 2 : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (M - 2),
        (1 + Real.log (2 * Real.pi)) *
          (shiftedHarmonicSqrtPrefix (k + 1) - shiftedHarmonicSqrtPrefix k) :=
      Finset.sum_le_sum hterm
    _ = (1 + Real.log (2 * Real.pi)) * shiftedHarmonicSqrtPrefix (M - 2) := htel
    _ ≤ (1 + Real.log (2 * Real.pi)) * (2 * Real.sqrt (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hpref_le (by positivity)
    _ = 2 * (1 + Real.log (2 * Real.pi)) * Real.sqrt (M : ℝ) := by ring

/-- **Unconditional `O(√M)` Recombination Bound:**
For all `M : ℕ`, `integerLagCesaroSum M + chebyshevNormalizedCesaroSum M` and
`(1 / 2) * mertensDeviationSqrtAction M` agree within `2 * (1 + log(2π)) * √M`. -/
theorem abs_integerLagCesaroSum_add_chebyshevNormalizedCesaroSum_sub_half_mertensDeviationSqrtAction_le
    (M : ℕ) :
    |integerLagCesaroSum M + chebyshevNormalizedCesaroSum M -
        (1 / 2 : ℝ) * mertensDeviationSqrtAction M| ≤
      2 * (1 + Real.log (2 * Real.pi)) * Real.sqrt (M : ℝ) := by
  rw [integerLagCesaroSum_add_chebyshevNormalizedCesaroSum_sub_half_mertensDeviationSqrtAction_eq]
  exact abs_archimedeanCesaroSqrtRemainder_le M

/-- **Unconditional `O(√M)` Triadic Syzygy Bound:**
For all `M : ℕ`, the terminal-boundary-free convex combination
`(1 / 2) * integerLagLinearCesaroAction M + (1 / 4) * integerLagMertensSqrtAction M`
agrees with `chebyshevNormalizedCesaroSum M` within `2 * (1 + log(2π)) * √M`. -/
theorem abs_half_linearCesaro_add_quarter_mertensSqrt_sub_chebyshevNormalizedCesaroSum_le
    (M : ℕ) :
    |(1 / 2 : ℝ) * integerLagLinearCesaroAction M +
        (1 / 4 : ℝ) * integerLagMertensSqrtAction M -
        chebyshevNormalizedCesaroSum M| ≤
      2 * (1 + Real.log (2 * Real.pi)) * Real.sqrt (M : ℝ) := by
  rw [half_integerLagLinearCesaroAction_add_quarter_mertensSqrtAction_sub_chebyshevNormalizedCesaroSum_eq,
    abs_neg]
  exact abs_archimedeanCesaroSqrtRemainder_le M

/-! ## Section 2: Master Linear-Bridge Abscissa Transfer Package -/

/-- Extending a linear `O(M)` bridge from `M ≥ 3` to a normalized `O(1)` comparison for all `M ≥ 2`. -/
theorem exists_abs_mobiusDivisorAbel_div_sub_of_linear_bridge
    {F : ℕ → ℝ} {α : ℝ}
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ M : ℕ, 2 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M / (M : ℝ) - α * (F M / (M : ℝ))| ≤ D := by
  obtain ⟨B, hB0, hB⟩ := hbridge
  let d₂ : ℝ := |mobiusDivisorSquareRootAbelMoment 2 / (2 : ℝ) - α * (F 2 / (2 : ℝ))|
  refine ⟨max B d₂, le_max_of_le_left hB0, fun M hM2 => ?_⟩
  by_cases hM_eq_2 : M = 2
  · subst M
    exact le_max_right B d₂
  · have hM3 : 3 ≤ M := by omega
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have h1 := hB M hM3
    have hdiv :
        mobiusDivisorSquareRootAbelMoment M / (M : ℝ) - α * (F M / (M : ℝ)) =
          (mobiusDivisorSquareRootAbelMoment M - α * F M) / (M : ℝ) := by ring
    rw [hdiv, abs_div, abs_of_pos hMpos]
    exact ((div_le_iff₀ hMpos).mpr h1).trans (le_max_left B d₂)

/-- **Master Unconditional Forward `zetaZeroAbscissa` Bound** for any sequence `F` with a linear
`O(M)` bridge to `mobiusDivisorSquareRootAbelMoment`. -/
theorem exists_subpower_zetaZeroAbscissa_of_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |F M / (M : ℝ)| ≤ C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_mobiusDivisorAbel_div_sub_of_linear_bridge hbridge
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  have hhalf := half_le_zetaZeroAbscissa
  have hexp0 : 0 ≤ zetaZeroAbscissa - 1 / 2 + ε := by linarith
  refine ⟨(C₀ + D) / α, by positivity, fun M hM2 => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hrpow1 : (1 : ℝ) ≤ (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
    Real.one_le_rpow hM1 hexp0
  have h1 := hC₀ M hM2
  have h2 := hD M hM2
  have htri :
      α * |F M / (M : ℝ)| ≤ (C₀ + D) * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
    have hα_abs : α * |F M / (M : ℝ)| = |α * (F M / (M : ℝ))| := by
      rw [abs_mul, abs_of_pos hα]
    rw [hα_abs]
    calc
      |α * (F M / (M : ℝ))| =
        |mobiusDivisorSquareRootAbelMoment M / (M : ℝ) -
          (mobiusDivisorSquareRootAbelMoment M / (M : ℝ) - α * (F M / (M : ℝ)))| := by ring_nf
      _ ≤ |mobiusDivisorSquareRootAbelMoment M / (M : ℝ)| +
          |mobiusDivisorSquareRootAbelMoment M / (M : ℝ) - α * (F M / (M : ℝ))| := abs_sub _ _
      _ ≤ C₀ * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) + D := add_le_add h1 h2
      _ ≤ C₀ * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) +
          D * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by nlinarith
      _ = (C₀ + D) * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hα]
  linarith

/-- **Master One-Sided Upper Power-Gap Strip Law** for any sequence `F` with a linear `O(M)` bridge. -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerGaps_linear_bridge_le_rpow
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    {A : Set ℕ} {C c K δ : ℝ} {N₀ : ℕ}
    (hC0 : 0 ≤ C) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA_bound : ∀ k ∈ A, 2 ≤ k → F k / (k : ℝ) ≤ C + C * (k : ℝ) ^ c)
    (hA_gaps : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_mobiusDivisorAbel_div_sub_of_linear_bridge hbridge
  refine zetaZeroAbscissa_le_half_add_max_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    (M := α * C + D) (by positivity) hδ hK (fun k hkA hk2 => ?_) hA_gaps
  have h1 := hA_bound k hkA hk2
  have h2 := (abs_sub_le_iff.mp (hD k hk2)).1
  have hrpow0 : 0 ≤ (k : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg k) c
  nlinarith

/-- **Master One-Sided Lower Power-Gap Strip Law** for any sequence `F` with a linear `O(M)` bridge. -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerGaps_neg_rpow_le_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    {A : Set ℕ} {C c K δ : ℝ} {N₀ : ℕ}
    (hC0 : 0 ≤ C) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA_bound : ∀ k ∈ A, 2 ≤ k → -(C + C * (k : ℝ) ^ c) ≤ F k / (k : ℝ))
    (hA_gaps : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_mobiusDivisorAbel_div_sub_of_linear_bridge hbridge
  refine zetaZeroAbscissa_le_half_add_max_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    (M := α * C + D) (by positivity) hδ hK (fun k hkA hk2 => ?_) hA_gaps
  have h1 := hA_bound k hkA hk2
  have h2 := (abs_sub_le_iff.mp (hD k hk2)).2
  have hrpow0 : 0 ≤ (k : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg k) c
  nlinarith

/-- **Master Arbitrary `m`-th Power Mesh Upper Strip Law (`m ≥ 1`)** for any sequence `F` with a
linear `O(M)` bridge. -/
theorem zetaZeroAbscissa_le_half_add_max_of_linear_bridge_pow_le_rpow
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    {m : ℕ} {C c : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      F (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤ C + C * ((j ^ m : ℕ) : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_mobiusDivisorAbel_div_sub_of_linear_bridge hbridge
  refine zetaZeroAbscissa_le_half_add_max_of_mobiusDivisorSquareRootAbel_pow_le_rpow
    (M := α * C + D) hm (by positivity) (fun j hj => ?_)
  have h1 := hpow j hj
  have h2 := (abs_sub_le_iff.mp (hD (j ^ m) hj)).1
  have hrpow0 : 0 ≤ ((j ^ m : ℕ) : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) c
  nlinarith

/-- **Master Arbitrary `m`-th Power Mesh Lower Strip Law (`m ≥ 1`)** for any sequence `F` with a
linear `O(M)` bridge. -/
theorem zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_linear_bridge_pow
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    {m : ℕ} {C c : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      -(C + C * ((j ^ m : ℕ) : ℝ) ^ c) ≤ F (j ^ m) / ((j ^ m : ℕ) : ℝ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_mobiusDivisorAbel_div_sub_of_linear_bridge hbridge
  refine zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_mobiusDivisorSquareRootAbel_pow
    (M := α * C + D) hm (by positivity) (fun j hj => ?_)
  have h1 := hpow j hj
  have h2 := (abs_sub_le_iff.mp (hD (j ^ m) hj)).2
  have hrpow0 : 0 ≤ ((j ^ m : ℕ) : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg _) c
  nlinarith

/-- **Master Full-Grid (`M ≥ 3`) Upper Strip Law** for any sequence `F` with a linear `O(M)` bridge. -/
theorem zetaZeroAbscissa_le_half_add_max_of_linear_bridge_le_rpow
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ M : ℕ, 3 ≤ M → F M / (M : ℝ) ≤ C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  let C' : ℝ := max C (max 0 (F 2 / (2 : ℝ)))
  have hC'0 : 0 ≤ C' := le_max_of_le_left hC0
  refine zetaZeroAbscissa_le_half_add_max_of_linear_bridge_pow_le_rpow
    hα hbridge (m := 1) le_rfl hC'0 (fun j hj => ?_)
  rw [pow_one] at hj ⊢
  by_cases hj2 : j = 2
  · subst j
    have hle : F 2 / (2 : ℝ) ≤ C' :=
      (le_max_right 0 (F 2 / (2 : ℝ))).trans (le_max_right C _)
    have hrpow0 : 0 ≤ (2 : ℝ) ^ c := Real.rpow_nonneg (by norm_num) c
    nlinarith
  · have hj3 : 3 ≤ j := by omega
    have h1 := hbound j hj3
    have hle : C ≤ C' := le_max_left _ _
    have hrpow0 : 0 ≤ (j : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg j) c
    nlinarith

/-- **Master Full-Grid (`M ≥ 3`) Lower Strip Law** for any sequence `F` with a linear `O(M)` bridge. -/
theorem zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ M : ℕ, 3 ≤ M → -(C * (M : ℝ) ^ c) ≤ F M / (M : ℝ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  let C' : ℝ := max C (max 0 (-(F 2 / (2 : ℝ))))
  have hC'0 : 0 ≤ C' := le_max_of_le_left hC0
  refine zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_linear_bridge_pow
    hα hbridge (m := 1) le_rfl hC'0 (fun j hj => ?_)
  rw [pow_one] at hj ⊢
  by_cases hj2 : j = 2
  · subst j
    have hle : -(F 2 / (2 : ℝ)) ≤ C' :=
      (le_max_right 0 (-(F 2 / (2 : ℝ)))).trans (le_max_right C _)
    have hrpow0 : 0 ≤ (2 : ℝ) ^ c := Real.rpow_nonneg (by norm_num) c
    nlinarith
  · have hj3 : 3 ≤ j := by omega
    have h1 := hbound j hj3
    have hle : C ≤ C' := le_max_left _ _
    have hrpow0 : 0 ≤ (j : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg j) c
    nlinarith

/-- **Master Exact `sInf` Upper Abscissa Formula (`M ≥ 3`)** for any sequence `F` with a linear
`O(M)` bridge. -/
theorem zetaZeroAbscissa_eq_half_add_sInf_upper_of_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ)) :
    zetaZeroAbscissa =
      1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
        F M / (M : ℝ) ≤ C * (M : ℝ) ^ c} := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
    F M / (M : ℝ) ≤ C * (M : ℝ) ^ c}
  have hbdd : BddBelow S := ⟨0, fun _ hc => hc.1⟩
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_subpower_zetaZeroAbscissa_of_linear_bridge hα hbridge ε hε
    refine ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0, fun M hM3 => ?_⟩
    exact (le_abs_self _).trans (hC M (by omega))
  have h1 : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
    refine le_csInf ⟨zetaZeroAbscissa - 1 / 2 + 1, hmem 1 zero_lt_one⟩ ?_
    rintro c ⟨hc0, C, hC0, hC⟩
    have hle := zetaZeroAbscissa_le_half_add_max_of_linear_bridge_le_rpow hα hbridge hC0 hC
    rw [max_eq_right hc0] at hle
    linarith
  have h2 : sInf S ≤ zetaZeroAbscissa - 1 / 2 :=
    le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)
  change zetaZeroAbscissa = 1 / 2 + sInf S
  linarith

/-- **Master Exact `sInf` Lower Abscissa Formula (`M ≥ 3`)** for any sequence `F` with a linear
`O(M)` bridge. -/
theorem zetaZeroAbscissa_eq_half_add_sInf_lower_of_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ)) :
    zetaZeroAbscissa =
      1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
        -(C * (M : ℝ) ^ c) ≤ F M / (M : ℝ)} := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
    -(C * (M : ℝ) ^ c) ≤ F M / (M : ℝ)}
  have hbdd : BddBelow S := ⟨0, fun _ hc => hc.1⟩
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_subpower_zetaZeroAbscissa_of_linear_bridge hα hbridge ε hε
    refine ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0, fun M hM3 => ?_⟩
    exact (neg_le_neg (hC M (by omega))).trans (neg_abs_le _)
  have h1 : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
    refine le_csInf ⟨zetaZeroAbscissa - 1 / 2 + 1, hmem 1 zero_lt_one⟩ ?_
    rintro c ⟨hc0, C, hC0, hC⟩
    have hle := zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_linear_bridge hα hbridge hC0 hC
    rw [max_eq_right hc0] at hle
    linarith
  have h2 : sInf S ≤ zetaZeroAbscissa - 1 / 2 :=
    le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)
  change zetaZeroAbscissa = 1 / 2 + sInf S
  linarith

/-- **Master Cumulative Mean-Square Abscissa Law** for any sequence `F` with a linear `O(M)` bridge:
if `∑_{2 ≤ k ≤ N} (F k / k)^2 ≤ C * N^r` (`r ≥ 1`), then `zetaZeroAbscissa ≤ r / 2`. -/
theorem zetaZeroAbscissa_le_half_of_sum_sq_le_rpow_of_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    {C r : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hE : ∀ N : ℕ, 2 ≤ N → ∑ k ∈ Icc 2 N, (F k / (k : ℝ)) ^ 2 ≤ C * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ r / 2 := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_mobiusDivisorAbel_div_sub_of_linear_bridge hbridge
  refine zetaZeroAbscissa_le_half_of_mobiusDivisorAbelMeanSquareEnergy_le_rpow
    (C := 2 * α ^ 2 * C + 2 * D ^ 2) (by positivity) hr (fun N hN => ?_)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNr : (N : ℝ) ≤ (N : ℝ) ^ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hr
  have hterm : ∀ k ∈ Icc 2 N,
      (mobiusDivisorSquareRootAbelMoment k / (k : ℝ)) ^ 2 ≤
        2 * α ^ 2 * (F k / (k : ℝ)) ^ 2 + 2 * D ^ 2 := by
    intro k hk
    have hs := (sq_le_sq₀
      (abs_nonneg (mobiusDivisorSquareRootAbelMoment k / (k : ℝ) - α * (F k / (k : ℝ)))) hD0).mpr
      (hD k (mem_Icc.mp hk).1)
    rw [sq_abs] at hs
    nlinarith [sq_nonneg (mobiusDivisorSquareRootAbelMoment k / (k : ℝ) - 2 * α * (F k / (k : ℝ)))]
  have hcard : ((Icc 2 N).card : ℝ) ≤ N := by
    exact_mod_cast (show (Icc 2 N).card ≤ N by rw [Nat.card_Icc]; omega)
  have hsum :
      mobiusDivisorAbelMeanSquareEnergy N ≤
        2 * α ^ 2 * (∑ k ∈ Icc 2 N, (F k / (k : ℝ)) ^ 2) + 2 * D ^ 2 * N := by
    unfold mobiusDivisorAbelMeanSquareEnergy
    calc
      ∑ k ∈ Icc 2 N, (mobiusDivisorSquareRootAbelMoment k / (k : ℝ)) ^ 2 ≤
        ∑ k ∈ Icc 2 N, (2 * α ^ 2 * (F k / (k : ℝ)) ^ 2 + 2 * D ^ 2) := sum_le_sum hterm
      _ = 2 * α ^ 2 * (∑ k ∈ Icc 2 N, (F k / (k : ℝ)) ^ 2) +
          ((Icc 2 N).card : ℝ) * (2 * D ^ 2) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ 2 * α ^ 2 * (∑ k ∈ Icc 2 N, (F k / (k : ℝ)) ^ 2) + 2 * D ^ 2 * N := by
        nlinarith [sq_nonneg D]
  have hEN := hE N hN
  nlinarith [sq_nonneg α, sq_nonneg D]

/-- **Master Unconditional Forward Cumulative Mean-Square Bound** at every exponent above
`2 * zetaZeroAbscissa`. -/
theorem exists_sum_sq_le_rpow_zetaZeroAbscissa_of_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∑ k ∈ Icc 2 N, (F k / (k : ℝ)) ^ 2 ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    exists_subpower_zetaZeroAbscissa_of_linear_bridge hα hbridge (ε / 2) (by positivity)
  refine ⟨C₀ ^ 2, sq_nonneg _, fun N hN => ?_⟩
  have h := sum_sq_le_rpow_of_abs_le_rpow hC₀0
    (by linarith [half_le_zetaZeroAbscissa] : 0 ≤ zetaZeroAbscissa - 1 / 2 + ε / 2) hC₀ hN
  simpa only [show 2 * (zetaZeroAbscissa - 1 / 2 + ε / 2) + 1 = 2 * zetaZeroAbscissa + ε by ring]
    using h

/-- **Master Exact Cumulative Mean-Square `sInf` Formula (`2 * zetaZeroAbscissa`)** for any
sequence `F` with a linear `O(M)` bridge. -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_sum_sq_exponents_of_linear_bridge
    {F : ℕ → ℝ} {α : ℝ} (hα : 0 < α)
    (hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - α * F M| ≤ B * (M : ℝ)) :
    2 * zetaZeroAbscissa =
      sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        ∑ k ∈ Icc 2 N, (F k / (k : ℝ)) ^ 2 ≤ C * (N : ℝ) ^ r} := by
  let S : Set ℝ := {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∑ k ∈ Icc 2 N, (F k / (k : ℝ)) ^ 2 ≤ C * (N : ℝ) ^ r}
  have hmem : ∀ ε : ℝ, 0 < ε → 2 * zetaZeroAbscissa + ε ∈ S := by
    intro ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa],
      exists_sum_sq_le_rpow_zetaZeroAbscissa_of_linear_bridge hα hbridge ε hε⟩
  have hne : S.Nonempty := ⟨2 * zetaZeroAbscissa + 1, hmem 1 zero_lt_one⟩
  have hbdd : BddBelow S := ⟨1, fun _ hr => hr.1⟩
  change 2 * zetaZeroAbscissa = sInf S
  apply le_antisymm
  · refine le_csInf hne fun r ⟨hr, C, hC, hE⟩ => ?_
    have h := zetaZeroAbscissa_le_half_of_sum_sq_le_rpow_of_linear_bridge hα hbridge hC hr hE
    linarith
  · exact le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)

/-! ## Section 3: Boundary-Free Normalized Chebyshev Cesàro Sum & Square-Root Riesz Action Abscissa Laws -/

/-- By functional-equation symmetry of `xi`, every zero `xi ρ = 0` satisfies
`1 - zetaZeroAbscissa ≤ ρ.re`. -/
theorem one_sub_zetaZeroAbscissa_le_xi_zero_re {ρ : ℂ} (hρ : xi ρ = 0) :
    1 - zetaZeroAbscissa ≤ ρ.re := by
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  linarith [(abs_le.mp (xiZeroCopy_abs_re_sub_half_le_zetaZeroAbscissa q)).1]

/-- **Explicit `2 |γ| + 4` Normalized Bridge Between `mobiusDivisorSquareRootAbelMoment` and
`(1 / 2) * chebyshevNormalizedCesaroSum`:**
Combining `abs_mobiusDivisorSquareRootAbel_div_sub_chebyshevSqrtIncrementAction_div_le` (`≤ 2 |γ| + 1`)
with `abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le` (`≤ 3 M`) yields the
explicit constant `2 |γ| + 4` for all `M ≥ 2`. -/
theorem abs_mobiusDivisorSquareRootAbel_div_sub_half_chebyshevNormalizedCesaroSum_div_le
    {M : ℕ} (hM : 2 ≤ M) :
    |mobiusDivisorSquareRootAbelMoment M / (M : ℝ) -
        (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M / (M : ℝ))| ≤
      2 * |Real.eulerMascheroniConstant| + 4 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h1 := abs_mobiusDivisorSquareRootAbel_div_sub_chebyshevSqrtIncrementAction_div_le hM
  have h2 := abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M
  have h2_div :
      |chebyshevSqrtIncrementAction M / (M : ℝ) -
          (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M / (M : ℝ))| ≤ 3 := by
    have heq :
        chebyshevSqrtIncrementAction M / (M : ℝ) -
            (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M / (M : ℝ)) =
          (chebyshevSqrtIncrementAction M -
            (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M) / (M : ℝ) := by ring
    rw [heq, abs_div, abs_of_pos hMpos]
    exact (div_le_iff₀ hMpos).mpr h2
  calc
    |mobiusDivisorSquareRootAbelMoment M / (M : ℝ) -
        (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M / (M : ℝ))| =
      |(mobiusDivisorSquareRootAbelMoment M / (M : ℝ) -
          chebyshevSqrtIncrementAction M / (M : ℝ)) +
        (chebyshevSqrtIncrementAction M / (M : ℝ) -
          (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M / (M : ℝ)))| := by ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment M / (M : ℝ) -
          chebyshevSqrtIncrementAction M / (M : ℝ)| +
        |chebyshevSqrtIncrementAction M / (M : ℝ) -
          (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M / (M : ℝ))| := abs_add_le _ _
    _ ≤ (2 * |Real.eulerMascheroniConstant| + 1) + 3 := add_le_add h1 h2_div
    _ = 2 * |Real.eulerMascheroniConstant| + 4 := by ring

/-- Cumulative mean-square energy of the boundary-free normalized Chebyshev Cesàro sum:
`chebyshevNormalizedCesaroMeanSquareEnergy N = ∑_{2 ≤ k ≤ N} (chebyshevNormalizedCesaroSum k / k)^2`. -/
def chebyshevNormalizedCesaroMeanSquareEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (chebyshevNormalizedCesaroSum k / (k : ℝ)) ^ 2

/-- Cumulative mean-square energy of the square-root Riesz von Mangoldt action:
`vonMangoldtSqrtRieszMeanSquareEnergy N = ∑_{2 ≤ k ≤ N} (vonMangoldtSqrtRieszAction k / k)^2`. -/
def vonMangoldtSqrtRieszMeanSquareEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (vonMangoldtSqrtRieszAction k / (k : ℝ)) ^ 2

/-- **Unconditional Forward `zetaZeroAbscissa` Subpower Bound for `chebyshevNormalizedCesaroSum`.** -/
theorem exists_chebyshevNormalizedCesaroSum_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |chebyshevNormalizedCesaroSum M / (M : ℝ)| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
  exists_subpower_zetaZeroAbscissa_of_linear_bridge (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear ε hε

/-- **One-Sided Upper Strip Law for `chebyshevNormalizedCesaroSum` (`M ≥ 3`).** -/
theorem zetaZeroAbscissa_le_half_add_max_of_chebyshevNormalizedCesaroSum_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ M : ℕ, 3 ≤ M → chebyshevNormalizedCesaroSum M / (M : ℝ) ≤ C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_half_add_max_of_linear_bridge_le_rpow (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear hC0 hbound

/-- **One-Sided Lower Strip Law for `chebyshevNormalizedCesaroSum` (`M ≥ 3`).** -/
theorem zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_chebyshevNormalizedCesaroSum
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ M : ℕ, 3 ≤ M → -(C * (M : ℝ) ^ c) ≤ chebyshevNormalizedCesaroSum M / (M : ℝ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_linear_bridge (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear hC0 hbound

/-- **Arbitrary `m`-th Power Mesh Upper Strip Law for `chebyshevNormalizedCesaroSum` (`m ≥ 1`).** -/
theorem zetaZeroAbscissa_le_half_add_max_of_chebyshevNormalizedCesaroSum_pow_le_rpow
    {m : ℕ} {C c : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      chebyshevNormalizedCesaroSum (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
        C + C * ((j ^ m : ℕ) : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_half_add_max_of_linear_bridge_pow_le_rpow (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear hm hC0 hpow

/-- **Arbitrary `m`-th Power Mesh Lower Strip Law for `chebyshevNormalizedCesaroSum` (`m ≥ 1`).** -/
theorem zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_chebyshevNormalizedCesaroSum_pow
    {m : ℕ} {C c : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      -(C + C * ((j ^ m : ℕ) : ℝ) ^ c) ≤
        chebyshevNormalizedCesaroSum (j ^ m) / ((j ^ m : ℕ) : ℝ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_linear_bridge_pow (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear hm hC0 hpow

/-- **Exact `sInf` Upper Abscissa Formula for `chebyshevNormalizedCesaroSum`.** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_chebyshevNormalizedCesaroSum_upper :
    zetaZeroAbscissa =
      1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
        chebyshevNormalizedCesaroSum M / (M : ℝ) ≤ C * (M : ℝ) ^ c} :=
  zetaZeroAbscissa_eq_half_add_sInf_upper_of_linear_bridge (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear

/-- **Exact `sInf` Lower Abscissa Formula for `chebyshevNormalizedCesaroSum`.** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_chebyshevNormalizedCesaroSum_lower :
    zetaZeroAbscissa =
      1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
        -(C * (M : ℝ) ^ c) ≤ chebyshevNormalizedCesaroSum M / (M : ℝ)} :=
  zetaZeroAbscissa_eq_half_add_sInf_lower_of_linear_bridge (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear

/-- **Cumulative Mean-Square Abscissa Law for `chebyshevNormalizedCesaroSum`:**
if `chebyshevNormalizedCesaroMeanSquareEnergy N ≤ C * N^r` (`r ≥ 1`), then `zetaZeroAbscissa ≤ r / 2`. -/
theorem zetaZeroAbscissa_le_half_of_chebyshevNormalizedCesaroMeanSquareEnergy_le_rpow
    {C r : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hE : ∀ N : ℕ, 2 ≤ N → chebyshevNormalizedCesaroMeanSquareEnergy N ≤ C * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ r / 2 :=
  zetaZeroAbscissa_le_half_of_sum_sq_le_rpow_of_linear_bridge (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear hC hr hE

/-- **Exact Cumulative Mean-Square `sInf` Formula (`2 * zetaZeroAbscissa`) for
`chebyshevNormalizedCesaroMeanSquareEnergy`.** -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_chebyshevNormalizedCesaroMeanSquareEnergy_exponents :
    2 * zetaZeroAbscissa =
      sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevNormalizedCesaroMeanSquareEnergy N ≤ C * (N : ℝ) ^ r} :=
  two_mul_zetaZeroAbscissa_eq_sInf_sum_sq_exponents_of_linear_bridge (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear

/-- **Two-Sided `1/6 ≤ Re(ρ) ≤ 5/6` (`zetaZeroAbscissa ≤ 5/6`) Criterion via `chebyshevNormalizedCesaroSum`:**
A one-sided upper bound `chebyshevNormalizedCesaroSum (j^m) / (j^m) ≤ C + C * (j^m)^(1/3)` along
any `m`-th power mesh (`m ≥ 1`) unconditionally forces `1/6 ≤ Re(ρ) ≤ 5/6` for all `xi` zeros. -/
theorem five_sixths_strip_of_chebyshevNormalizedCesaroSum_pow_le_one_third
    {m : ℕ} {C : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      chebyshevNormalizedCesaroSum (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
        C + C * ((j ^ m : ℕ) : ℝ) ^ (1 / 3 : ℝ)) :
    zetaZeroAbscissa ≤ 5 / 6 ∧
      ∀ ρ : ℂ, xi ρ = 0 → (1 / 6 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 5 / 6 := by
  have h := zetaZeroAbscissa_le_half_add_max_of_chebyshevNormalizedCesaroSum_pow_le_rpow
    hm hC0 hpow
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 3)] at h
  have habs : zetaZeroAbscissa ≤ 5 / 6 := by linarith
  refine ⟨habs, fun ρ hρ => ?_⟩
  have h1 := xi_zero_re_le_zetaZeroAbscissa hρ
  have h2 := one_sub_zetaZeroAbscissa_le_xi_zero_re hρ
  constructor <;> linarith

/-- **Two-Sided `1/4 ≤ Re(ρ) ≤ 3/4` (`zetaZeroAbscissa ≤ 3/4`) Criterion via `chebyshevNormalizedCesaroSum`:**
A one-sided upper bound `chebyshevNormalizedCesaroSum (j^m) / (j^m) ≤ C + C * (j^m)^(1/4)` along
any `m`-th power mesh (`m ≥ 1`) unconditionally forces `1/4 ≤ Re(ρ) ≤ 3/4` for all `xi` zeros. -/
theorem three_quarters_strip_of_chebyshevNormalizedCesaroSum_pow_le_one_quarter
    {m : ℕ} {C : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      chebyshevNormalizedCesaroSum (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
        C + C * ((j ^ m : ℕ) : ℝ) ^ (1 / 4 : ℝ)) :
    zetaZeroAbscissa ≤ 3 / 4 ∧
      ∀ ρ : ℂ, xi ρ = 0 → (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3 / 4 := by
  have h := zetaZeroAbscissa_le_half_add_max_of_chebyshevNormalizedCesaroSum_pow_le_rpow
    hm hC0 hpow
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 4)] at h
  have habs : zetaZeroAbscissa ≤ 3 / 4 := by linarith
  refine ⟨habs, fun ρ hρ => ?_⟩
  have h1 := xi_zero_re_le_zetaZeroAbscissa hρ
  have h2 := one_sub_zetaZeroAbscissa_le_xi_zero_re hρ
  constructor <;> linarith

/-- **Exact Cumulative Mean-Square Equivalence for the `1/6 ≤ Re(ρ) ≤ 5/6` Strip (`r = 5/3 + ε`)
via `chebyshevNormalizedCesaroMeanSquareEnergy`.** -/
theorem five_sixths_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 6 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 5 / 6) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevNormalizedCesaroMeanSquareEnergy N ≤ C * (N : ℝ) ^ ((5 / 3 : ℝ) + ε) := by
  constructor
  · intro hstrip ε hε
    have habs : zetaZeroAbscissa ≤ 5 / 6 := by
      have hhalf : (0 : ℝ) ≤ 1 / 3 := by norm_num
      have h := zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound hhalf
        (fun ρ hρ => by linarith [(hstrip ρ hρ).2])
      linarith
    obtain ⟨C, hC0, hC⟩ := exists_sum_sq_le_rpow_zetaZeroAbscissa_of_linear_bridge
      (by norm_num : (0 : ℝ) < 1 / 2)
      exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear ε hε
    refine ⟨C, hC0, fun N hN => (hC N hN).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC0
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
  · intro hE
    have habs : zetaZeroAbscissa ≤ 5 / 6 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨C, hC0, hC⟩ := hE (2 * ε) (by positivity)
      have hle := zetaZeroAbscissa_le_half_of_chebyshevNormalizedCesaroMeanSquareEnergy_le_rpow
        hC0 (by linarith : (1 : ℝ) ≤ (5 / 3 : ℝ) + 2 * ε) hC
      linarith
    intro ρ hρ
    have h1 := xi_zero_re_le_zetaZeroAbscissa hρ
    have h2 := one_sub_zetaZeroAbscissa_le_xi_zero_re hρ
    constructor <;> linarith

/-- **Exact Cumulative Mean-Square Equivalence for the `1/4 ≤ Re(ρ) ≤ 3/4` Strip (`r = 3/2 + ε`)
via `chebyshevNormalizedCesaroMeanSquareEnergy`.** -/
theorem three_quarters_strip_iff_chebyshevNormalizedCesaroMeanSquareEnergy_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3 / 4) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevNormalizedCesaroMeanSquareEnergy N ≤ C * (N : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
  constructor
  · intro hstrip ε hε
    have habs : zetaZeroAbscissa ≤ 3 / 4 := by
      have hhalf : (0 : ℝ) ≤ 1 / 4 := by norm_num
      have h := zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound hhalf
        (fun ρ hρ => by linarith [(hstrip ρ hρ).2])
      linarith
    obtain ⟨C, hC0, hC⟩ := exists_sum_sq_le_rpow_zetaZeroAbscissa_of_linear_bridge
      (by norm_num : (0 : ℝ) < 1 / 2)
      exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear ε hε
    refine ⟨C, hC0, fun N hN => (hC N hN).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC0
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
  · intro hE
    have habs : zetaZeroAbscissa ≤ 3 / 4 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨C, hC0, hC⟩ := hE (2 * ε) (by positivity)
      have hle := zetaZeroAbscissa_le_half_of_chebyshevNormalizedCesaroMeanSquareEnergy_le_rpow
        hC0 (by linarith : (1 : ℝ) ≤ (3 / 2 : ℝ) + 2 * ε) hC
      linarith
    intro ρ hρ
    have h1 := xi_zero_re_le_zetaZeroAbscissa hρ
    have h2 := one_sub_zetaZeroAbscissa_le_xi_zero_re hρ
    constructor <;> linarith

/-- **Unconditional Forward `zetaZeroAbscissa` Subpower Bound for `vonMangoldtSqrtRieszAction`.** -/
theorem exists_vonMangoldtSqrtRieszAction_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |vonMangoldtSqrtRieszAction M / (M : ℝ)| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  have hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - (1 : ℝ) * vonMangoldtSqrtRieszAction M| ≤ B * (M : ℝ) := by
    simpa [one_mul] using exists_abs_mobiusDivisorSquareRootAbel_sub_vonMangoldtSqrtRieszAction_linear
  exact exists_subpower_zetaZeroAbscissa_of_linear_bridge zero_lt_one hbridge ε hε

/-- **Exact `sInf` Upper Abscissa Formula for `vonMangoldtSqrtRieszAction`.** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_vonMangoldtSqrtRieszAction_upper :
    zetaZeroAbscissa =
      1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
        vonMangoldtSqrtRieszAction M / (M : ℝ) ≤ C * (M : ℝ) ^ c} := by
  have hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - (1 : ℝ) * vonMangoldtSqrtRieszAction M| ≤ B * (M : ℝ) := by
    simpa [one_mul] using exists_abs_mobiusDivisorSquareRootAbel_sub_vonMangoldtSqrtRieszAction_linear
  exact zetaZeroAbscissa_eq_half_add_sInf_upper_of_linear_bridge zero_lt_one hbridge

/-- **Exact Cumulative Mean-Square `sInf` Formula (`2 * zetaZeroAbscissa`) for
`vonMangoldtSqrtRieszMeanSquareEnergy`.** -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_vonMangoldtSqrtRieszMeanSquareEnergy_exponents :
    2 * zetaZeroAbscissa =
      sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        vonMangoldtSqrtRieszMeanSquareEnergy N ≤ C * (N : ℝ) ^ r} := by
  have hbridge : ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M - (1 : ℝ) * vonMangoldtSqrtRieszAction M| ≤ B * (M : ℝ) := by
    simpa [one_mul] using exists_abs_mobiusDivisorSquareRootAbel_sub_vonMangoldtSqrtRieszAction_linear
  exact two_mul_zetaZeroAbscissa_eq_sInf_sum_sq_exponents_of_linear_bridge zero_lt_one hbridge

/-! ## Section 4: Terminal-Lag / Mertens-Deviation & Linear–Cesàro Action Abscissa Laws -/

/-- Uniform `O(M)` linear bridge between `mobiusDivisorSquareRootAbelMoment M` and
`(3 / 8) * integerLagMertensSqrtAction M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_three_eighths_mertensSqrtAction_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M| ≤ B * (M : ℝ) := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_neg_mul_integerLag_add_mertensSqrtAction_linear
  refine ⟨B, hB0, fun M hM => ?_⟩
  have h1 := hB M hM
  have hscale :
      -(M : ℝ) * integerLag M + (3 / 4 : ℝ) * mertensDeviationSqrtAction M =
        (3 / 8 : ℝ) * integerLagMertensSqrtAction M := by
    unfold integerLagMertensSqrtAction; ring
  rw [hscale] at h1
  exact h1

/-- Cumulative mean-square energy of `integerLagMertensSqrtAction`:
`integerLagMertensSqrtMeanSquareEnergy N = ∑_{2 ≤ k ≤ N} (integerLagMertensSqrtAction k / k)^2`. -/
def integerLagMertensSqrtMeanSquareEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (integerLagMertensSqrtAction k / (k : ℝ)) ^ 2

/-- Cumulative mean-square energy of `integerLagLinearCesaroAction`:
`integerLagLinearCesaroMeanSquareEnergy N = ∑_{2 ≤ k ≤ N} (integerLagLinearCesaroAction k / k)^2`. -/
def integerLagLinearCesaroMeanSquareEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (integerLagLinearCesaroAction k / (k : ℝ)) ^ 2

/-- **Unconditional Forward `zetaZeroAbscissa` Subpower Bound for `integerLagMertensSqrtAction`.** -/
theorem exists_integerLagMertensSqrtAction_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |integerLagMertensSqrtAction M / (M : ℝ)| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
  exists_subpower_zetaZeroAbscissa_of_linear_bridge (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_three_eighths_mertensSqrtAction_linear ε hε

/-- **Arbitrary `m`-th Power Mesh Upper Strip Law for `integerLagMertensSqrtAction` (`m ≥ 1`).** -/
theorem zetaZeroAbscissa_le_half_add_max_of_integerLagMertensSqrtAction_pow_le_rpow
    {m : ℕ} {C c : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      integerLagMertensSqrtAction (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
        C + C * ((j ^ m : ℕ) : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_half_add_max_of_linear_bridge_pow_le_rpow (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_three_eighths_mertensSqrtAction_linear hm hC0 hpow

/-- **Exact `sInf` Upper Abscissa Formula for `integerLagMertensSqrtAction`.** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_integerLagMertensSqrtAction_upper :
    zetaZeroAbscissa =
      1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
        integerLagMertensSqrtAction M / (M : ℝ) ≤ C * (M : ℝ) ^ c} :=
  zetaZeroAbscissa_eq_half_add_sInf_upper_of_linear_bridge (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_three_eighths_mertensSqrtAction_linear

/-- **Exact Cumulative Mean-Square `sInf` Formula (`2 * zetaZeroAbscissa`) for
`integerLagMertensSqrtMeanSquareEnergy`.** -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_integerLagMertensSqrtMeanSquareEnergy_exponents :
    2 * zetaZeroAbscissa =
      sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        integerLagMertensSqrtMeanSquareEnergy N ≤ C * (N : ℝ) ^ r} :=
  two_mul_zetaZeroAbscissa_eq_sInf_sum_sq_exponents_of_linear_bridge (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_three_eighths_mertensSqrtAction_linear

/-- **Unconditional Forward `zetaZeroAbscissa` Subpower Bound for `integerLagLinearCesaroAction`.** -/
theorem exists_integerLagLinearCesaroAction_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |integerLagLinearCesaroAction M / (M : ℝ)| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
  exists_subpower_zetaZeroAbscissa_of_linear_bridge (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear ε hε

/-- **Arbitrary `m`-th Power Mesh Upper Strip Law for `integerLagLinearCesaroAction` (`m ≥ 1`).** -/
theorem zetaZeroAbscissa_le_half_add_max_of_integerLagLinearCesaroAction_pow_le_rpow
    {m : ℕ} {C c : ℝ} (hm : 1 ≤ m) (hC0 : 0 ≤ C)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      integerLagLinearCesaroAction (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
        C + C * ((j ^ m : ℕ) : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_half_add_max_of_linear_bridge_pow_le_rpow (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear hm hC0 hpow

/-- **Exact `sInf` Upper Abscissa Formula for `integerLagLinearCesaroAction`.** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_integerLagLinearCesaroAction_upper :
    zetaZeroAbscissa =
      1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
        integerLagLinearCesaroAction M / (M : ℝ) ≤ C * (M : ℝ) ^ c} :=
  zetaZeroAbscissa_eq_half_add_sInf_upper_of_linear_bridge (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear

/-- **Exact Cumulative Mean-Square `sInf` Formula (`2 * zetaZeroAbscissa`) for
`integerLagLinearCesaroMeanSquareEnergy`.** -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_integerLagLinearCesaroMeanSquareEnergy_exponents :
    2 * zetaZeroAbscissa =
      sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        integerLagLinearCesaroMeanSquareEnergy N ≤ C * (N : ℝ) ^ r} :=
  two_mul_zetaZeroAbscissa_eq_sInf_sum_sq_exponents_of_linear_bridge (by norm_num : (0 : ℝ) < 3 / 8)
    exists_abs_mobiusDivisorSquareRootAbel_sub_linearCesaroAction_linear

end

end RHTower
