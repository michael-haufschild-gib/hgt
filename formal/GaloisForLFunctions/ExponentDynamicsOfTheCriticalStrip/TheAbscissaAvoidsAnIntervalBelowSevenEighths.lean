import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.EveryRulerCarriesTheSeedAndEveryLever
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.LeversThatBiteFailInTheWorlds
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheBestDoublingFactorOfTheMarginIsTwoToTheWidth
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth

/-!
# The Abscissa of `ζ` Avoids an Interval Below Seven Eighths

This module formalizes the unconditional avoided interval, monotone lever, wall collapse, ruler
jump, and `[D]` corollaries implied by `zetaZeroAbscissa ≤ 20999 / 24000` (`= 7/8 - 1/24000`) and
`zetaZeroWidth ≤ 8999 / 24000` (`= 3/8 - 1/24000`):

* **Avoided intervals and explicit levers for `ζ`**:
  - `zetaZeroAbscissa ∉ (20999 / 24000, 7 / 8]` and `zetaZeroAbscissa ∉ (20999 / 24000, 7 / 8)`,
    witnessing `1 / 2 < b₁ < b₂ ≤ 7 / 8` at `b₁ = 20999 / 24000`, `b₂ = 7 / 8`
    (`exists_avoided_interval_below_seven_eighths`).
  - `subSevenEighthsLever = closedRightBandLever (20999 / 24000) (7 / 8)` is monotone, is an
    unconditional lever for `zetaZeroAbscissa`, has exact gap `(20999 / 24000, 7 / 8]`, sends `7/8`
    directly to `20999 / 24000`, and collapses `wall {subSevenEighthsLever} (7 / 8)` (and its
    generated closure) to `20999 / 24000` (`exists_lever_below_seven_eighths`,
    `wall_subSevenEighthsLever`, `wall_generated_subSevenEighthsLever`).
* **Simultaneous ruler jump across every `zetaZeroWidth` ruler** (`sub_three_eighths_ruler_jump`):
  Every ruler `IsRuler zetaZeroWidth D P` jumps unconditionally from `P (3 / 8)` to
  `P (8999 / 24000)`.
* **Unconditional `[D]` corollaries and exact boundary attainment at `3/8` and `7/8`**:
  - `newmanConstant ≤ 80982001 / 1152000000 < 9 / 128` and
    `wdHeatThreshold ≤ 80982001 / 1728000000 < 3 / 64`.
  - Mertens `O(n^β)` for every `β > 20999 / 24000`, and in particular `|M(n)| = O(n^{7/8})` with
    no `+ ε` loss (`exists_mertens_le_seven_eighths_exact`).
  - Critical-line Möbius polynomials `O(X^{8999/24000 + ε})` and `O(X^{3/8})` exact; mollified unit
    window `O(X^{2*(8999/24000 + ε)})` and `O(X^{3/4})` exact; zero-free Möbius polynomials on
    compact subsets of `{Re z > 20999 / 24000}` (including compact subsets of `Re z = 7 / 8`).
  - Zeta kernel signal `O(Z^{7/8})` exact (`O(Z^{b'})` for `b' > 20999 / 24000`), antisymmetric
    two-end depth `O(e^{(8999/24000) v})`, long moments `O(T^{4 + (8999/12000) θ})` and
    `O(T^{6 + (8999/12000) θ})`, `SlopeLaw (8999 / 12000)` (`< 3 / 4`),
    `LogEnergyFloor (8999 / 24000)` (`< 3 / 8`), `MarginLaw ρ (3 / 8)` exact, and
    `DoublingLaw ρ (2 ^ (3 / 8))` exact.
  - Eternal-AdS Wightman strip analyticity on `0 < |Im ω| < 3001 / 48000` (`> 1 / 16`).
  - Worlds selectivity: `subSevenEighthsLever` fails on entire functional-equation `coshModel`s,
    two-sided prime edits with count `A x + O(x^{14/15})` realize zeros on every vertical line in
    `(20999 / 24000, 14 / 15)` (including `Re s = 7 / 8` itself), and shifted pairs
    `ζ(s - a) ζ(s + a)` realize every abscissa in `[20999 / 24000, 1)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg)
open GaloisForLFunctions.ZeroForcingCalculus
  (bandLever closedRightBandLever monotone_bandLever monotone_closedRightBandLever
   excluded_bandLever_eq_Ioo excluded_closedRightBandLever_eq_Ioc isLever_bandLever_iff
   isLever_closedRightBandLever_iff closedRightBandLever_apply_right
   zetaZeroWidth_le_sub_three_eighths zetaZeroAbscissa_le_sub_seven_eighths)
open GaloisForLFunctions.InfiniteRankWeilTheory (coshModel)
open GaloisForLFunctions.WorldsOfTheZeroConfiguration (linePoints exists_isEdit_zeros_on_a_vertical_line)
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits (IsEdit editSystem)
open _root_.RHTower (shiftedZetaPair shiftedPairCoeff zetaZeroAbscissa half_le_zetaZeroAbscissa)

/-! ### 1. Avoided intervals and explicit monotone levers below `7/8` -/

/-- Unconditionally, `zetaZeroAbscissa` avoids the right-closed interval `(20999 / 24000, 7 / 8]`. -/
theorem zetaZeroAbscissa_notMem_sub_seven_eighths_Ioc :
    zetaZeroAbscissa ∉ Set.Ioc (20999 / 24000 : ℝ) (7 / 8) := by
  intro hmem
  exact not_lt_of_ge zetaZeroAbscissa_le_sub_seven_eighths hmem.1

/-- Unconditionally, `zetaZeroAbscissa` avoids the open interval `(20999 / 24000, 7 / 8)`. -/
theorem zetaZeroAbscissa_notMem_sub_seven_eighths_Ioo :
    zetaZeroAbscissa ∉ Set.Ioo (20999 / 24000 : ℝ) (7 / 8) :=
  fun hmem => zetaZeroAbscissa_notMem_sub_seven_eighths_Ioc ⟨hmem.1, hmem.2.le⟩

/-- **Solution to the avoided-interval problem below `7/8`:** there exist `1 / 2 < b₁ < b₂ ≤ 7 / 8`
(explicitly `b₁ = 20999 / 24000`, `b₂ = 7 / 8`) such that `zetaZeroAbscissa ∉ (b₁, b₂)` and
`zetaZeroAbscissa ∉ (b₁, b₂]`, with no hypothesis on zeros. -/
theorem exists_avoided_interval_below_seven_eighths :
    ∃ b₁ b₂ : ℝ, 1 / 2 < b₁ ∧ b₁ < b₂ ∧ b₂ ≤ 7 / 8 ∧
      zetaZeroAbscissa ∉ Set.Ioo b₁ b₂ ∧ zetaZeroAbscissa ∉ Set.Ioc b₁ b₂ :=
  ⟨20999 / 24000, 7 / 8, by norm_num, by norm_num, le_rfl,
    zetaZeroAbscissa_notMem_sub_seven_eighths_Ioo,
    zetaZeroAbscissa_notMem_sub_seven_eighths_Ioc⟩

/-- Explicit monotone lever clamping `[20999 / 24000, 7 / 8]` down to `20999 / 24000`. -/
def subSevenEighthsLever : ℝ → ℝ :=
  closedRightBandLever (20999 / 24000) (7 / 8)

theorem monotone_subSevenEighthsLever : Monotone subSevenEighthsLever :=
  monotone_closedRightBandLever (by norm_num)

theorem excluded_subSevenEighthsLever :
    excluded subSevenEighthsLever = Set.Ioc (20999 / 24000 : ℝ) (7 / 8) :=
  excluded_closedRightBandLever_eq_Ioc (20999 / 24000) (7 / 8)

theorem subSevenEighthsLever_seven_eighths :
    subSevenEighthsLever (7 / 8) = 20999 / 24000 :=
  closedRightBandLever_apply_right (by norm_num)

theorem subSevenEighthsLever_self_left :
    subSevenEighthsLever (20999 / 24000) = 20999 / 24000 := by
  unfold subSevenEighthsLever closedRightBandLever
  rw [if_pos (by norm_num : (20999 / 24000 : ℝ) ≤ 7 / 8), min_self]

/-- **Unconditional lever theorem for `zetaZeroAbscissa` below `7/8`:** `subSevenEighthsLever` is a
monotone lever for `zetaZeroAbscissa` (`Θ ≤ b → Θ ≤ subSevenEighthsLever b`) biting strictly across
`(20999 / 24000, 7 / 8]`. -/
theorem isLever_zetaZeroAbscissa_subSevenEighthsLever :
    IsLever zetaZeroAbscissa subSevenEighthsLever :=
  (isLever_closedRightBandLever_iff (by norm_num)).mpr
    zetaZeroAbscissa_notMem_sub_seven_eighths_Ioc

/-- Open-band companion lever `bandLever (20999 / 24000) (7 / 8)` with gap `(20999 / 24000, 7 / 8)`. -/
theorem isLever_zetaZeroAbscissa_openSubSevenEighthsLever :
    IsLever zetaZeroAbscissa (bandLever (20999 / 24000) (7 / 8)) :=
  (isLever_bandLever_iff (by norm_num)).mpr zetaZeroAbscissa_notMem_sub_seven_eighths_Ioo

/-- Global clamping lever `b ↦ min b (20999 / 24000)` biting on `(20999 / 24000, ∞)`. -/
theorem isLever_zetaZeroAbscissa_min_subSevenEighths :
    IsLever zetaZeroAbscissa (fun b => min b (20999 / 24000)) :=
  fun _ hb => le_min hb zetaZeroAbscissa_le_sub_seven_eighths

/-- **Solution to the lever problem below `7/8`:** there exist `1 / 2 < b₁ < b₂ ≤ 7 / 8` and a
monotone map `T : ℝ → ℝ` such that `IsLever zetaZeroAbscissa T` (`Θ ≤ b → Θ ≤ T b`) and `T b < b`
for every `b ∈ (b₁, b₂]` (hence for every `b ∈ (b₁, b₂)`). -/
theorem exists_lever_below_seven_eighths :
    ∃ (b₁ b₂ : ℝ) (T : ℝ → ℝ),
      1 / 2 < b₁ ∧ b₁ < b₂ ∧ b₂ ≤ 7 / 8 ∧ Monotone T ∧ IsLever zetaZeroAbscissa T ∧
      (∀ b ∈ Set.Ioc b₁ b₂, T b < b) ∧ (∀ b ∈ Set.Ioo b₁ b₂, T b < b) := by
  refine ⟨20999 / 24000, 7 / 8, subSevenEighthsLever, by norm_num, by norm_num, le_rfl,
    monotone_subSevenEighthsLever, isLever_zetaZeroAbscissa_subSevenEighthsLever, ?_, ?_⟩
  · intro b hb
    have hmem : b ∈ excluded subSevenEighthsLever := by
      rwa [excluded_subSevenEighthsLever]
    exact hmem
  · intro b hb
    have hmem : b ∈ excluded subSevenEighthsLever := by
      rw [excluded_subSevenEighthsLever]
      exact ⟨hb.1, hb.2.le⟩
    exact hmem

/-- **Wall collapse below `7/8`:** `subSevenEighthsLever` lowers `wall` below the seed `7/8` to
`20999 / 24000`, and closing under composition and pointwise minimum preserves that wall. -/
theorem wall_subSevenEighthsLever :
    wall {subSevenEighthsLever} (7 / 8) = 20999 / 24000 ∧
      wall {T | Generated {subSevenEighthsLever} T} (7 / 8) = 20999 / 24000 := by
  have hmem : (20999 / 24000 : ℝ) ∈ allowed {subSevenEighthsLever} (7 / 8) := by
    refine ⟨by norm_num, ?_⟩
    intro T hT
    rw [Set.mem_singleton_iff.mp hT, subSevenEighthsLever_self_left]
  have hlo : (20999 / 24000 : ℝ) ≤ wall {subSevenEighthsLever} (7 / 8) :=
    le_csSup (bddAbove_allowed _ _) hmem
  have hhi : wall {subSevenEighthsLever} (7 / 8) ≤ 20999 / 24000 := by
    refine csSup_le ⟨20999 / 24000, hmem⟩ fun b hb => ?_
    have hTb : b ≤ subSevenEighthsLever b := hb.2 subSevenEighthsLever rfl
    unfold subSevenEighthsLever closedRightBandLever at hTb
    rw [if_pos hb.1] at hTb
    exact hTb.trans (min_le_right b (20999 / 24000))
  have hw : wall {subSevenEighthsLever} (7 / 8) = 20999 / 24000 := le_antisymm hhi hlo
  have hmono : ∀ T ∈ ({subSevenEighthsLever} : Set (ℝ → ℝ)), Monotone T := by
    intro T hT
    rw [Set.mem_singleton_iff.mp hT]
    exact monotone_subSevenEighthsLever
  exact ⟨hw, (wall_generated hmono (7 / 8)).trans hw⟩

/-! ### 2. Width lever and simultaneous jump across every `zetaZeroWidth` ruler -/

/-- Explicit monotone lever on widths clamping `[8999 / 24000, 3 / 8]` down to `8999 / 24000`. -/
def subThreeEighthsWidthLever : ℝ → ℝ :=
  closedRightBandLever (8999 / 24000) (3 / 8)

theorem zetaZeroWidth_notMem_sub_three_eighths_Ioc :
    zetaZeroWidth ∉ Set.Ioc (8999 / 24000 : ℝ) (3 / 8) :=
  fun hmem => not_lt_of_ge zetaZeroWidth_le_sub_three_eighths hmem.1

theorem isLever_zetaZeroWidth_subThreeEighthsWidthLever :
    IsLever zetaZeroWidth subThreeEighthsWidthLever :=
  (isLever_closedRightBandLever_iff (by norm_num)).mpr zetaZeroWidth_notMem_sub_three_eighths_Ioc

/-- **Simultaneous jump across every ruler of `zetaZeroWidth`:** every ruler containing `8999 / 24000`
and `3 / 8` jumps unconditionally from its `3 / 8` reading to its `8999 / 24000` reading. -/
theorem sub_three_eighths_ruler_jump (D : Set ℝ) (P : ℝ → Prop)
    (hR : IsRuler zetaZeroWidth D P)
    (h1 : (8999 / 24000 : ℝ) ∈ D) (h2 : (3 / 8 : ℝ) ∈ D) (hP : P (3 / 8)) :
    P (8999 / 24000) := by
  have heval : subThreeEighthsWidthLever (3 / 8) = 8999 / 24000 :=
    closedRightBandLever_apply_right (by norm_num)
  have hread := isLever_zetaZeroWidth_subThreeEighthsWidthLever.reading hR h2 (heval.symm ▸ h1) hP
  rwa [heval] at hread

/-! ### 3. Unconditional `[D]` corollaries and exact boundary attainment at `3/8` and `7/8` -/

/-- **De Bruijn–Newman constant bound:** `Λ ≤ 80982001 / 1152000000 < 9 / 128`. -/
theorem newmanConstant_le_sub_nine_div_128 :
    _root_.RHTower.DeBruijn.newmanConstant ≤ 80982001 / 1152000000 := by
  have hsq : zetaZeroWidth ^ 2 ≤ (8999 / 24000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ zetaZeroWidth_nonneg zetaZeroWidth_le_sub_three_eighths 2
  have h := SquareRootThreshold.newmanConstant_le_half_sq_zetaZeroWidth
  linarith only [h, hsq]

theorem newmanConstant_lt_nine_div_128 :
    _root_.RHTower.DeBruijn.newmanConstant < 9 / 128 :=
  lt_of_le_of_lt newmanConstant_le_sub_nine_div_128 (by norm_num)

/-- **Slice heat threshold bound:** `λ_WD ≤ 80982001 / 1728000000 < 3 / 64`. -/
theorem wdHeatThreshold_le_sub_three_div_64 :
    _root_.RHTower.DeBruijn.wdHeatThreshold ≤ 80982001 / 1728000000 := by
  have hsq : zetaZeroWidth ^ 2 ≤ (8999 / 24000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ zetaZeroWidth_nonneg zetaZeroWidth_le_sub_three_eighths 2
  have h := _root_.RHTower.DeBruijn.wdHeatThreshold_le_third_sq_zetaZeroWidth
  linarith only [h, hsq]

theorem wdHeatThreshold_lt_three_div_64 :
    _root_.RHTower.DeBruijn.wdHeatThreshold < 3 / 64 :=
  lt_of_le_of_lt wdHeatThreshold_le_sub_three_div_64 (by norm_num)

/-- **Mertens bound below `7/8`:** `M(n) = O(n^β)` for every `β > 20999 / 24000`. -/
theorem exists_mertens_le_of_sub_seven_eighths_lt {β : ℝ} (hβ : 20999 / 24000 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Finset.Icc 1 n, BezoutValuationIncidence.moebiusReal d| ≤ C * (n : ℝ) ^ β :=
  BezoutValuationIncidence.exists_moebius_power_bound_of_abscissa_lt
    (lt_of_le_of_lt zetaZeroAbscissa_le_sub_seven_eighths hβ)

/-- **Exact `O(n^{7/8})` Mertens bound (with no `+ ε` loss).** -/
theorem exists_mertens_le_seven_eighths_exact :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Finset.Icc 1 n, BezoutValuationIncidence.moebiusReal d| ≤
        C * (n : ℝ) ^ (7 / 8 : ℝ) :=
  exists_mertens_le_of_sub_seven_eighths_lt (by norm_num)

/-- **Critical-line Möbius polynomials:** `O(X^{8999/24000 + ε})` at every height `t₀`. -/
theorem exists_norm_moebiusPoly_le_sub_three_eighths (t₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ‖MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint t₀)‖ ≤
        C * (X : ℝ) ^ (8999 / 24000 + ε) :=
  (isRuler_moebiusPoly_pointwise t₀ (8999 / 24000) (mem_Ici.2 (by norm_num))).1
    zetaZeroWidth_le_sub_three_eighths ε hε

/-- **Exact `O(X^{3/8})` pointwise critical-line Möbius polynomial bound (with no `+ ε` loss).** -/
theorem exists_norm_moebiusPoly_le_three_eighths_exact (t₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ‖MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint t₀)‖ ≤
        C * (X : ℝ) ^ (3 / 8 : ℝ) := by
  obtain ⟨C, hC, h⟩ := exists_norm_moebiusPoly_le_sub_three_eighths t₀ (ε := 1 / 24000) (by norm_num)
  refine ⟨C, hC, fun X hX => ?_⟩
  simpa only [show (8999 / 24000 + 1 / 24000 : ℝ) = 3 / 8 by norm_num] using h X hX

/-- **Mollified unit window:** `∫₀¹ |ζ M_X|² = O(X^{2*(8999/24000 + ε)})`. -/
theorem exists_unit_window_le_sub_three_eighths {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 1 ≤ X →
      ∫ u in (0 : ℝ)..1, ‖riemannZeta (MultiscaleMollifiedZetaField.linePoint u) *
        MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint u)‖ ^ 2 ≤
          B * (X : ℝ) ^ (2 * (8999 / 24000 + ε)) :=
  (isRuler_unit_window (8999 / 24000) (mem_Ici.2 (by norm_num))).1
    zetaZeroWidth_le_sub_three_eighths ε hε

/-- **Exact `O(X^{3/4})` mollified unit-window bound (with no `+ 2ε` loss).** -/
theorem exists_unit_window_le_three_quarters_exact :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 1 ≤ X →
      ∫ u in (0 : ℝ)..1, ‖riemannZeta (MultiscaleMollifiedZetaField.linePoint u) *
        MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint u)‖ ^ 2 ≤
          B * (X : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨B, hB, h⟩ := exists_unit_window_le_sub_three_eighths (ε := 1 / 24000) (by norm_num)
  refine ⟨B, hB, fun X hX => ?_⟩
  simpa only [show (2 * (8999 / 24000 + 1 / 24000) : ℝ) = 3 / 4 by norm_num] using h X hX

/-- **Zero-free compacts for Möbius polynomials right of `20999 / 24000`** (including compact
subsets of `Re z = 7 / 8`). -/
theorem eventually_moebiusPoly_ne_zero_right_of_sub_seven_eighths {K : Set ℂ} (hK : IsCompact K)
    (hre : ∀ z ∈ K, 20999 / 24000 < z.re) (h1 : (1 : ℂ) ∉ K) :
    ∀ᶠ X : ℕ in atTop, ∀ z ∈ K, MultiscaleMollifiedZetaField.moebiusPoly X z ≠ 0 :=
  (isRuler_moebiusPoly_zero_free (8999 / 24000) (mem_univ _)).1
    zetaZeroWidth_le_sub_three_eighths K hK (fun z hz => by linarith only [hre z hz]) h1

/-- **Zeta kernel signal:** `O(Z^{b'})` for every `20999 / 24000 < b' ≤ 1`. -/
theorem exists_signal_le_of_sub_seven_eighths_lt {b' : ℝ}
    (hb' : 20999 / 24000 < b') (hb'1 : b' ≤ 1) :
    ∃ K : ℝ, ∀ Z : ℝ, 0 < Z →
      ‖FamilyContinuationTheory.signal (FamilyContinuationTheory.zetaKernel 0) 2 Z‖ ≤
        K * Z ^ b' :=
  (isRuler_signal (8999 / 24000) ⟨by norm_num, by norm_num⟩).1
    zetaZeroWidth_le_sub_three_eighths b' (by linarith only [hb']) hb'1

/-- **Exact `O(Z^{7/8})` zeta-kernel signal bound (with no `+ ε` loss).** -/
theorem exists_signal_le_seven_eighths_exact :
    ∃ K : ℝ, ∀ Z : ℝ, 0 < Z →
      ‖FamilyContinuationTheory.signal (FamilyContinuationTheory.zetaKernel 0) 2 Z‖ ≤
        K * Z ^ (7 / 8 : ℝ) :=
  exists_signal_le_of_sub_seven_eighths_lt (by norm_num) (by norm_num)

/-- **Two-end antisymmetric state depth:** `O(e^{(8999 / 24000) v})`. -/
theorem exists_twoEndOdd_rate_sub_three_eighths :
    ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → ∀ Q : ℕ,
      (∀ n : ℕ, Q < n → AbsoluteGeometryOfSpecZ.packetAutocorr
        (MixingArithmeticOfTheFloorTrees.twoEndOdd v) (Real.log n) = 0) →
        -(C * Real.exp (8999 / 24000 * v)) ≤
          AbsoluteGeometryOfSpecZ.neutralForm Q (MixingArithmeticOfTheFloorTrees.twoEndOdd v) :=
  (isRuler_twoEndOdd (8999 / 24000) ⟨by norm_num, by norm_num⟩).1
    zetaZeroWidth_le_sub_three_eighths

/-- **Long second moment of Möbius polynomials:** `O(T^{4 + (8999 / 12000) θ})`. -/
theorem exists_pure_moebius_moment_le_sub_seed {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖RHTower.edPoly ConjugateDiagonalGeometry.NearLineLogMean.moebiusMollifierCoeff
          (Finset.Icc 1 ⌊T ^ θ⌋₊) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (4 + 8999 / 12000 * θ) := by
  obtain ⟨C, hC, h⟩ :=
    ConjugateDiagonalGeometry.NearLineLogMean.exists_pure_moebius_moment_le_zetaZeroWidth hθ
  refine ⟨C, hC, fun T hT => (h T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT ?_) hC)⟩
  have := mul_le_mul_of_nonneg_right zetaZeroWidth_le_sub_three_eighths hθ.le
  linarith only [this]

/-- **Long second moment of mollified zeta:** `O(T^{6 + (8999 / 12000) θ})`. -/
theorem exists_moebius_mollifier_moment_le_sub_seed {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly ConjugateDiagonalGeometry.NearLineLogMean.moebiusMollifierCoeff
            (Finset.Icc 1 ⌊T ^ θ⌋₊) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (6 + 8999 / 12000 * θ) := by
  obtain ⟨C, hC, h⟩ :=
    ConjugateDiagonalGeometry.NearLineLogMean.exists_moebius_mollifier_moment_le_zetaZeroWidth hθ
  refine ⟨C, hC, fun T hT => (h T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT ?_) hC)⟩
  have := mul_le_mul_of_nonneg_right zetaZeroWidth_le_sub_three_eighths hθ.le
  linarith only [this]

/-- **Long-moment slope law below `3/4`:** `SlopeLaw (8999 / 12000)` (`8999 / 12000 < 3 / 4`). -/
theorem slopeLaw_sub_three_quarters : SlopeLaw (8999 / 12000) := by
  have h := slopeLaw_of_zetaZeroWidth_le zetaZeroWidth_le_sub_three_eighths
  have e : (2 : ℝ) * (8999 / 24000) = 8999 / 12000 := by norm_num
  rwa [e] at h

/-- **Weil floor in the logarithmic energy below `3/8`:** `LogEnergyFloor (8999 / 24000)`. -/
theorem logEnergyFloor_sub_three_eighths : LogEnergyFloor (8999 / 24000) :=
  logEnergyFloor_of_zetaZeroWidth_le zetaZeroWidth_le_sub_three_eighths

/-- **Window-matrix margin law below `3/8`:** `MarginLaw ρ β` for every `β > 8999 / 24000`. -/
theorem marginLaw_of_sub_three_eighths_lt {ρ : ℕ → ℕ} (hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) {β : ℝ} (hβ : 8999 / 24000 < β) : MarginLaw ρ β :=
  marginLaw_of_zetaZeroWidth_lt hρ₁ hρA (lt_of_le_of_lt zetaZeroWidth_le_sub_three_eighths hβ)

/-- **Exact `3/8` window-matrix margin law (with no `+ ε` loss).** -/
theorem marginLaw_three_eighths_exact {ρ : ℕ → ℕ} (hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) : MarginLaw ρ (3 / 8) :=
  marginLaw_of_sub_three_eighths_lt hρ₁ hρA (by norm_num)

/-- **Window-matrix doubling law below `2^{3/8}`:** `DoublingLaw ρ (2 ^ β)` for every
`β > 8999 / 24000`. -/
theorem doublingLaw_of_sub_three_eighths_lt {ρ : ℕ → ℕ} (hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) {β : ℝ} (hβ : 8999 / 24000 < β) :
    DoublingLaw ρ ((2 : ℝ) ^ β) :=
  doublingLaw_of_zetaZeroWidth_lt hρ₁ hρA (lt_of_le_of_lt zetaZeroWidth_le_sub_three_eighths hβ)

/-- **Exact `2^{3/8}` window-matrix doubling law (with no `+ ε` loss).** -/
theorem doublingLaw_two_rpow_three_eighths_exact {ρ : ℕ → ℕ} (hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) : DoublingLaw ρ ((2 : ℝ) ^ (3 / 8 : ℝ)) :=
  doublingLaw_of_sub_three_eighths_lt hρ₁ hρA (by norm_num)

/-- **Eternal-AdS two-boundary Wightman strip widening:** `modularWightmanRL` is complex-analytic
throughout `0 < |Im ω| < 3001 / 48000` (`= 1 / 16 + 1 / 48000 > 1 / 16`). -/
theorem modularWightmanRL_analyticOnNhd_sub_one_sixteenth :
    AnalyticOnNhd ℂ BlackHoleRingdown.modularWightmanRL
      {ω : ℂ | 0 < |ω.im| ∧ |ω.im| < 3001 / 48000} := by
  rw [BlackHoleRingdown.modularWightmanRL_analyticOnNhd_strip_iff (by norm_num) (by norm_num)]
  intro ρ hζ h0
  have hmem :=
    MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip h0 hζ
  linarith [hmem.2]

/-! ### 4. Worlds selectivity: what `subSevenEighthsLever` necessarily uses -/

/-- `subSevenEighthsLever` fails on an entire functional-equation `coshModel` at `7/8`: any proof of
it for `ζ` necessarily uses the Dirichlet series. -/
theorem exists_coshModel_not_isLever_subSevenEighthsLever :
    ∃ Q : Finset ℂ, ¬ IsLever (zeroSupRe (coshModel Q)) subSevenEighthsLever := by
  refine exists_coshModel_not_isLever (b := 7 / 8) (by norm_num) ?_
  rw [subSevenEighthsLever_seven_eighths]
  norm_num

/-- **Prime-edit selectivity across `(20999 / 24000, 14 / 15)` (including `σ = 7 / 8`):** for every
`20999 / 24000 < σ < 14 / 15`, a two-sided edit of the rational primes with count
`A' x + O(x^{14/15})` has a zero on `Re s = σ` and all its zeros right of `20999 / 24000` away from
`1` lie on `Re s = σ`. -/
theorem exists_isEdit_zeros_on_line_right_of_sub_seed {σ : ℝ}
    (hσ : 20999 / 24000 < σ) (hσ1 : σ < 14 / 15) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A' C : ℝ, 0 ≤ A' ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A' * x| ≤ C * x ^ (14 / 15 : ℝ)) ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
        (∃ z : ℂ, z.re = σ ∧ G z = 0) ∧
        ∀ z : ℂ, 20999 / 24000 < z.re → z ≠ 1 → G z = 0 → z.re = σ := by
  have hd : 0 < 14 / 15 - σ := by linarith only [hσ1]
  have hA : 0 < 1 / (14 / 15 - σ) := one_div_pos.mpr hd
  have hroom : σ + 1 / (2 * (1 / (14 / 15 - σ))) < 14 / 15 := by
    have : 1 / (2 * (1 / (14 / 15 - σ))) = (14 / 15 - σ) / 2 := by field_simp
    rw [this]
    linarith only [hd]
  obtain ⟨e, he, hcount, G, hG, hGF, hzero⟩ :=
    exists_isEdit_zeros_on_a_vertical_line (σ := σ) (A := 1 / (14 / 15 - σ))
      (by linarith only [hσ]) hA hroom (β := 14 / 15) hroom (by norm_num)
  have hζ : ∀ z : ℂ, 20999 / 24000 < z.re → riemannZeta z ≠ 0 := fun z hz =>
    MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hz
  have hline : ∀ z : ℂ, (∃ j, z = linePoints σ (1 / (14 / 15 - σ)) j ∨
      z = (starRingEnd ℂ) (linePoints σ (1 / (14 / 15 - σ)) j)) → z.re = σ := by
    rintro z ⟨j, rfl | rfl⟩
    · rfl
    · rw [conj_re]
      rfl
  refine ⟨e, he, hcount, G, hG, hGF, ⟨linePoints σ (1 / (14 / 15 - σ)) 0, rfl, ?_⟩, ?_⟩
  · have hre : (linePoints σ (1 / (14 / 15 - σ)) 0).re = σ := rfl
    have hne : linePoints σ (1 / (14 / 15 - σ)) 0 ≠ 1 := fun h1 => by
      have := congrArg Complex.re h1
      rw [hre, one_re] at this
      linarith only [this, hσ1]
    exact (hzero _ (by rw [hre]; linarith only [hσ]) hne (hζ _ (by rw [hre]; exact hσ))).2
      ⟨0, Or.inl rfl⟩
  · intro z hz hz1 hGz
    exact hline z ((hzero z (by linarith only [hz]) hz1 (hζ z hz)).1 hGz)

/-- `[20999 / 24000, 1)` is realized by the shifted zeta pairs `ζ(s - a) ζ(s + a)`. -/
theorem Ico_sub_seven_eighths_one_subset :
    Ico (20999 / 24000 : ℝ) 1 ⊆ Ico zetaZeroAbscissa (zetaZeroAbscissa + 1 / 2) :=
  fun _ hb => ⟨zetaZeroAbscissa_le_sub_seven_eighths.trans hb.1,
    by linarith only [hb.2, half_le_zetaZeroAbscissa]⟩

/-- At every point `b ∈ (20999 / 24000, 7 / 8]` (including `b = 7 / 8`), `subSevenEighthsLever`
fails for the shifted pair `a = b - Θ > 0`: any proof of `subSevenEighthsLever` uses the Ramanujan /
degree-one structure of `ζ`. -/
theorem exists_shiftedPair_not_isLever_subSevenEighthsLever {b : ℝ}
    (hb : b ∈ Set.Ioc (20999 / 24000 : ℝ) (7 / 8)) :
    ¬ IsLever (zeroSupRe (shiftedZetaPair (b - zetaZeroAbscissa))) subSevenEighthsLever := by
  have hmem : b ∈ Ico zetaZeroAbscissa (zetaZeroAbscissa + 1 / 2) :=
    Ico_sub_seven_eighths_one_subset ⟨hb.1.le, by linarith only [hb.2]⟩
  have hT : subSevenEighthsLever b < b := by
    have hex : b ∈ excluded subSevenEighthsLever := by
      rwa [excluded_subSevenEighthsLever]
    exact hex
  exact (exists_shiftedPair_not_isLever hmem hT).1

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

