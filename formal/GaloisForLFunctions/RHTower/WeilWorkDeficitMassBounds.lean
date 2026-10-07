import GaloisForLFunctions.RHTower.WeilFullConeLocalMassBound
import GaloisForLFunctions.RHTower.WeilWorkDeficitSharedMass
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Interval mass bounds for the canonical Weil measure

The logarithmic unit-window estimate extends to every bounded interval, with a factor equal
to its length plus one. The estimate applies to the entire measure, including diffuse mass.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace RHTower.WeilSpectral

private theorem interval_mass_le_of_unit_bound {μ : Measure ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hunit : ∀ t : ℝ, μ (Icc (t - 1) (t + 1)) ≤
      ENNReal.ofReal (C * Real.log (|t| + 3))) {a b : ℝ} (hab : a ≤ b) :
    μ (Icc a b) ≤ ENNReal.ofReal (C * (b - a + 1) * Real.log (max |a| |b| + 3)) := by
  classical
  let N : ℕ := ⌊b - a⌋₊ + 1
  let J : ℕ → Set ℝ := fun i => Icc (a + i - 1) (a + i + 1)
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
  have hcover : Icc a b ⊆ ⋃ i ∈ Finset.range N, J i := by
    intro x hx
    let i : ℕ := ⌊x - a⌋₊
    have hi : i ∈ Finset.range N := by
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.floor_mono (sub_le_sub_right hx.2 a))
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, ?_⟩⟩
    have hlo := Nat.floor_le (show 0 ≤ x - a by linarith [hx.1])
    have hhi := Nat.lt_floor_add_one (x - a)
    change a + (i : ℝ) - 1 ≤ x ∧ x ≤ a + (i : ℝ) + 1
    dsimp [i]
    constructor <;> linarith
  have hcenter : ∀ i ∈ Finset.range N, |a + (i : ℝ)| ≤ max |a| |b| := by
    intro i hi
    have hiN : i ≤ ⌊b - a⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hiR : (i : ℝ) ≤ b - a := (Nat.cast_le.mpr hiN).trans (Nat.floor_le hwidth)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    apply abs_le.mpr
    constructor
    · linarith [neg_le_abs a, le_max_left |a| |b|]
    · linarith [le_abs_self b, le_max_right |a| |b|]
  have hterm : ∀ i ∈ Finset.range N,
      μ (J i) ≤ ENNReal.ofReal (C * Real.log (max |a| |b| + 3)) := by
    intro i hi
    refine (hunit (a + i)).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.log_le_log (by positivity) (by linarith [hcenter i hi])
  calc
    μ (Icc a b) ≤ μ (⋃ i ∈ Finset.range N, J i) := measure_mono hcover
    _ ≤ ∑ i ∈ Finset.range N, μ (J i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range N,
        ENNReal.ofReal (C * Real.log (max |a| |b| + 3)) := Finset.sum_le_sum hterm
    _ ≤ ENNReal.ofReal (C * (b - a + 1) * Real.log (max |a| |b| + 3)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      apply ENNReal.ofReal_le_ofReal
      have hN : (N : ℝ) ≤ b - a + 1 := by
        dsimp [N]
        push_cast
        linarith [Nat.floor_le hwidth]
      have hlog : 0 ≤ Real.log (max |a| |b| + 3) :=
        Real.log_nonneg (by linarith [abs_nonneg a, le_max_left |a| |b|])
      calc
        (N : ℝ) * (C * Real.log (max |a| |b| + 3)) ≤
            (b - a + 1) * (C * Real.log (max |a| |b| + 3)) :=
          mul_le_mul_of_nonneg_right hN (mul_nonneg hC hlog)
        _ = _ := by ring

/-- The canonical spectral mass grows at most logarithmically per unit interval. -/
theorem exists_boundaryMeasure_Icc_le_length_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, a ≤ b →
      boundaryMeasure hW (Icc a b) ≤
        ENNReal.ofReal (C * (b - a + 1) * Real.log (max |a| |b| + 3)) := by
  obtain ⟨C, hC, hunit⟩ := exists_boundaryMeasure_Icc_le_log hW
  exact ⟨C, hC, fun _ _ hab => interval_mass_le_of_unit_bound hC hunit hab⟩

theorem boundaryMeasure_Icc_ne_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a b : ℝ) :
    boundaryMeasure hW (Icc a b) ≠ ∞ := by
  by_cases hab : a ≤ b
  · obtain ⟨C, _, hC⟩ := exists_boundaryMeasure_Icc_le_length_log hW
    exact (lt_of_le_of_lt (hC a b hab) ENNReal.ofReal_lt_top).ne
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

private theorem deficitOrdinateMeasure_unit (t : ℝ) :
    deficitOrdinateMeasure (Icc (t - 1) (t + 1)) =
      ((finite_xiOrdinateWindow 1 t).toFinset.card : ℝ≥0∞) := by
  classical
  have hm (q : XiZeroCopy) : (q.1 : ℂ).im ∈ Icc (t - 1) (t + 1) ↔
      q ∈ (finite_xiOrdinateWindow 1 t).toFinset := by
    rw [Set.Finite.mem_toFinset]
    change _ ↔ |(q.1 : ℂ).im - t| ≤ 1
    rw [abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [deficitOrdinateMeasure, Measure.sum_apply _ measurableSet_Icc]
  calc
    (∑' q : XiZeroCopy, Measure.dirac (q.1 : ℂ).im (Icc (t - 1) (t + 1))) =
        ∑ q ∈ (finite_xiOrdinateWindow 1 t).toFinset,
          Measure.dirac (q.1 : ℂ).im (Icc (t - 1) (t + 1)) := by
      apply tsum_eq_sum
      intro q hq
      rw [Measure.dirac_apply' _ measurableSet_Icc,
        Set.indicator_of_notMem ((hm q).not.mpr hq)]
    _ = ∑ _q ∈ (finite_xiOrdinateWindow 1 t).toFinset, (1 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Measure.dirac_apply_of_mem ((hm q).mpr hq)
    _ = _ := by simp

/-- The projected actual divisor has a logarithmic bound on every bounded interval. -/
theorem exists_deficitOrdinateMeasure_Icc_le_length_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, a ≤ b →
      deficitOrdinateMeasure (Icc a b) ≤
        ENNReal.ofReal (C * (b - a + 1) * Real.log (max |a| |b| + 3)) := by
  let A : ℝ := (|xiLineTwoLogDerivConstant| + Real.log 2) / Real.log 3
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := div_nonneg (add_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num))) hlog3.le
  have hunit (t : ℝ) : deficitOrdinateMeasure (Icc (t - 1) (t + 1)) ≤
      ENNReal.ofReal (16 * (A + 1) * Real.log (|t| + 3)) := by
    rw [deficitOrdinateMeasure_unit, ← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have hn := ncard_xiOrdinateWindow_one_le_log t
    rw [Set.ncard_eq_toFinset_card _ (finite_xiOrdinateWindow 1 t)] at hn
    have hL : Real.log 3 ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    have hlog : Real.log (|t| + 4) ≤ Real.log 2 + Real.log (|t| + 3) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      apply Real.log_le_log (by positivity)
      linarith [abs_nonneg t]
    have hprod : |xiLineTwoLogDerivConstant| + Real.log 2 = A * Real.log 3 := by
      dsimp [A]
      field_simp [hlog3.ne']
    have hscale := mul_le_mul_of_nonneg_left hL hA
    rw [← hprod] at hscale
    nlinarith [le_abs_self xiLineTwoLogDerivConstant]
  exact ⟨16 * (A + 1), by positivity, fun _ _ hab =>
    interval_mass_le_of_unit_bound (by positivity) hunit hab⟩

theorem deficitOrdinateMeasure_Icc_ne_top (a b : ℝ) :
    deficitOrdinateMeasure (Icc a b) ≠ ∞ := by
  by_cases hab : a ≤ b
  · obtain ⟨C, _, hC⟩ := exists_deficitOrdinateMeasure_Icc_le_length_log
    exact (lt_of_le_of_lt (hC a b hab) ENNReal.ofReal_lt_top).ne
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

/-- The Cauchy weight is integrable for all actual copies, on both ordinate half-lines. -/
theorem integrable_deficitOrdinateCauchyWeight :
    Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) deficitOrdinateMeasure := by
  unfold deficitOrdinateMeasure
  apply integrable_sum_measure
  · intro q
    exact integrable_dirac (by simp)
  · have hn (q : XiZeroCopy) : ‖(1 : ℝ) / (1 + (q.1 : ℂ).im ^ 2)‖ =
        1 / (1 + (q.1 : ℂ).im ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [integral_dirac, hn] using summable_inv_one_add_sq_im

end RHTower.WeilSpectral

end
