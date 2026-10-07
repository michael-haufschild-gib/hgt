import GaloisForLFunctions.RHTower.WeilFullConeLocalMassBound

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

end RHTower.WeilSpectral

end
