import GaloisForLFunctions.BiScaleUncertainty.DyadicMantissaTent
import GaloisForLFunctions.BiScaleUncertainty.FiniteWindowVariance

/-!
# Stable doubling incidence recovered from perturbed positions

The explicit triangular weight vanishes off integer doubling pairs and stays
between one minus six times the displacement and one on those pairs. Its
actual all-pairs graph energy therefore retains linear window coercivity.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- The literal physical mismatch determines the weight, with no supplied matching. -/
def softDoublingWeight (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  max 0 (1 - 2 * |x j - 2 * x i|)

/-- The weighted graph uses all ordered pairs of nodes in the actual window. -/
def softDoublingEnergy (N : ℕ) (x f : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, softDoublingWeight x i j * (f j - f i) ^ 2

theorem softDoublingWeight_bounds (x : ℕ → ℝ) (i j : ℕ) :
    0 ≤ softDoublingWeight x i j ∧ softDoublingWeight x i j ≤ 1 := by
  unfold softDoublingWeight
  exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith only [abs_nonneg (x j - 2 * x i)])⟩

/-- Every nonzero integer doubling mismatch has size at least one. -/
theorem integer_doubling_mismatch_ge_one (i j : ℕ) (hne : j ≠ 2 * i) :
    (1 : ℝ) ≤ |(j : ℝ) - 2 * (i : ℝ)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hb : (j : ℝ) + 1 ≤ 2 * (i : ℝ) := by
      exact_mod_cast (show j + 1 ≤ 2 * i by omega)
    linarith only [hb, neg_le_abs ((j : ℝ) - 2 * (i : ℝ))]
  · have hb : 2 * (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (show 2 * i + 1 ≤ j by omega)
    linarith only [hb, le_abs_self ((j : ℝ) - 2 * (i : ℝ))]

/-- Independent node errors amplify by exactly at most three in the physical doubling mismatch. -/
theorem abs_perturbed_doubling_error_le (x : ℕ → ℝ) (i j : ℕ) {δ : ℝ}
    (hi : |x i - (i : ℝ)| ≤ δ) (hj : |x j - (j : ℝ)| ≤ δ) :
    |(x j - 2 * x i) - ((j : ℝ) - 2 * (i : ℝ))| ≤ 3 * δ := by
  rw [show (x j - 2 * x i) - ((j : ℝ) - 2 * (i : ℝ)) =
    (x j - (j : ℝ)) - 2 * (x i - (i : ℝ)) by ring]
  have hb := abs_sub (x j - (j : ℝ)) (2 * (x i - (i : ℝ)))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
  linarith only [hb, hi, hj]

/-- Below displacement one sixth, no non-doubling integer pair receives positive weight. -/
theorem softDoublingWeight_eq_zero_of_ne (x : ℕ → ℝ) (i j : ℕ) {δ : ℝ}
    (hδ : δ < 1 / 6) (hi : |x i - (i : ℝ)| ≤ δ) (hj : |x j - (j : ℝ)| ≤ δ)
    (hne : j ≠ 2 * i) : softDoublingWeight x i j = 0 := by
  have hg := integer_doubling_mismatch_ge_one i j hne
  have he := abs_perturbed_doubling_error_le x i j hi hj
  have ht := abs_add_le (x j - 2 * x i)
    (-((x j - 2 * x i) - ((j : ℝ) - 2 * (i : ℝ))))
  rw [show (x j - 2 * x i) + -((x j - 2 * x i) - ((j : ℝ) - 2 * (i : ℝ))) =
    (j : ℝ) - 2 * (i : ℝ) by ring, abs_neg] at ht
  unfold softDoublingWeight
  apply max_eq_left
  linarith only [hg, he, ht, hδ]

/-- At a true integer doubling pair the exact lower weight is one minus six displacements. -/
theorem softDoublingWeight_double_bounds (x : ℕ → ℝ) (i : ℕ) {δ : ℝ}
    (hi : |x i - (i : ℝ)| ≤ δ) (hj : |x (2 * i) - ((2 * i : ℕ) : ℝ)| ≤ δ) :
    1 - 6 * δ ≤ softDoublingWeight x i (2 * i) ∧ softDoublingWeight x i (2 * i) ≤ 1 := by
  have he := abs_perturbed_doubling_error_le x i (2 * i) hi hj
  simp only [Nat.cast_mul, Nat.cast_ofNat, sub_self, sub_zero] at he
  refine ⟨?_, (softDoublingWeight_bounds x i (2 * i)).2⟩
  exact (show 1 - 6 * δ ≤ 1 - 2 * |x (2 * i) - 2 * x i| by linarith only [he]).trans
    (le_max_right _ _)

/-- The all-pairs weighted energy reduces exactly to the recovered doubling pairs. -/
theorem softDoublingEnergy_eq_doubling_sum (N : ℕ) (x f : ℕ → ℝ) {δ : ℝ}
    (hδ : δ < 1 / 6) (hx : ∀ i ∈ Icc 1 N, |x i - (i : ℝ)| ≤ δ) :
    softDoublingEnergy N x f =
      ∑ i ∈ Icc 1 (N / 2), softDoublingWeight x i (2 * i) * (f (2 * i) - f i) ^ 2 := by
  have hsub : Icc 1 (N / 2) ⊆ Icc 1 N := by
    intro i hi
    exact mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans (Nat.div_le_self N 2)⟩
  have hout (i : ℕ) (hi : i ∈ Icc 1 N) (hout : i ∉ Icc 1 (N / 2)) :
      (∑ j ∈ Icc 1 N, softDoublingWeight x i j * (f j - f i) ^ 2) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hne : j ≠ 2 * i := by
      have hi' := mem_Icc.mp hi
      have hj' := mem_Icc.mp hj
      intro he
      apply hout
      exact mem_Icc.mpr ⟨hi'.1, by omega⟩
    rw [softDoublingWeight_eq_zero_of_ne x i j hδ (hx i hi) (hx j hj) hne, zero_mul]
  unfold softDoublingEnergy
  calc
    _ = ∑ i ∈ Icc 1 (N / 2), ∑ j ∈ Icc 1 N,
        softDoublingWeight x i j * (f j - f i) ^ 2 := (sum_subset hsub hout).symm
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_Icc.mp hi
      have h2i : 2 * i ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
      apply sum_eq_single (2 * i)
      · intro j hj hne
        rw [softDoublingWeight_eq_zero_of_ne x i j hδ (hx i (hsub hi)) (hx j hj) hne, zero_mul]
      · exact fun hn => (hn h2i).elim

theorem softDoublingEnergy_nonneg (N : ℕ) (x f : ℕ → ℝ) :
    0 ≤ softDoublingEnergy N x f :=
  sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (softDoublingWeight_bounds x i j).1 (sq_nonneg _)

/-- The exact two-sided comparison retains the coefficient one minus six displacements. -/
theorem softDoublingEnergy_comparison (N : ℕ) (x f : ℕ → ℝ) {δ : ℝ}
    (hδ : δ < 1 / 6) (hx : ∀ i ∈ Icc 1 N, |x i - (i : ℝ)| ≤ δ) :
    (1 - 6 * δ) * multiplicativeScaleEnergy 2 N f ≤ softDoublingEnergy N x f ∧
      softDoublingEnergy N x f ≤ multiplicativeScaleEnergy 2 N f := by
  rw [softDoublingEnergy_eq_doubling_sum N x f hδ hx]
  simp only [multiplicativeScaleEnergy, Icc_self, sum_singleton]
  rw [mul_sum]
  constructor
  · apply sum_le_sum
    intro i hi
    have hi' := mem_Icc.mp hi
    have hiN : i ∈ Icc 1 N := mem_Icc.mpr ⟨hi'.1, hi'.2.trans (Nat.div_le_self N 2)⟩
    have h2i : 2 * i ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
    exact mul_le_mul_of_nonneg_right
      (softDoublingWeight_double_bounds x i (hx i hiN) (hx (2 * i) h2i)).1 (sq_nonneg _)
  · apply sum_le_sum
    intro i hi
    exact mul_le_of_le_one_left (sq_nonneg _) (softDoublingWeight_bounds x i (2 * i)).2

/-- The original tent remains an exact weighted-doubling null vector. -/
theorem softDoublingEnergy_dyadicMantissaTent (N : ℕ) (x : ℕ → ℝ) {δ : ℝ}
    (hδ : δ < 1 / 6) (hx : ∀ i ∈ Icc 1 N, |x i - (i : ℝ)| ≤ δ) :
    softDoublingEnergy N x dyadicMantissaTent = 0 := by
  apply le_antisymm _ (softDoublingEnergy_nonneg N x dyadicMantissaTent)
  simpa only [multiplicativeScaleEnergy_dyadicMantissaTent] using
    (softDoublingEnergy_comparison N x dyadicMantissaTent hδ hx).2

/-- Every nonempty perturbed window has the exact stated weighted coercivity coefficient. -/
theorem softDoubling_window_coercivity (N : ℕ) (hN : 1 ≤ N) (x f : ℕ → ℝ) {δ : ℝ}
    (hδ : δ < 1 / 6) (hx : ∀ i ∈ Icc 1 N, |x i - (i : ℝ)| ≤ δ) :
    integerWindowVariance N f ≤ (24 * (N : ℝ) / (1 - 6 * δ)) *
      (additiveStepEnergy N f + softDoublingEnergy N x f) := by
  have hδ0 : 0 ≤ δ :=
    (abs_nonneg (x 1 - ((1 : ℕ) : ℝ))).trans (hx 1 (mem_Icc.mpr ⟨le_rfl, hN⟩))
  have hd : 0 < 1 - 6 * δ := by linarith only [hδ]
  have hA := additiveStepEnergy_nonneg N f
  have hD := (softDoublingEnergy_comparison N x f hδ hx).1
  have henergy : (1 - 6 * δ) * biScaleJointEnergy 2 N f ≤
      additiveStepEnergy N f + softDoublingEnergy N x f := by
    unfold biScaleJointEnergy
    nlinarith only [hD, hA, hδ0, mul_nonneg hδ0 hA]
  have hbase := (integerWindowVariance_le_centered N f (f 1)).trans (doubling_window_coercivity N f)
  have hscale := mul_le_mul_of_nonneg_left hbase hd.le
  have htransfer := mul_le_mul_of_nonneg_left henergy
    (by positivity : (0 : ℝ) ≤ 6 * (N : ℝ))
  have hnonneg : 0 ≤ additiveStepEnergy N f + softDoublingEnergy N x f :=
    add_nonneg hA (softDoublingEnergy_nonneg N x f)
  have hb : integerWindowVariance N f ≤
      (6 * (N : ℝ) * (additiveStepEnergy N f + softDoublingEnergy N x f)) / (1 - 6 * δ) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hscale, htransfer]
  calc
    _ ≤ _ := hb
    _ ≤ (24 * (N : ℝ) * (additiveStepEnergy N f + softDoublingEnergy N x f)) /
        (1 - 6 * δ) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by have hn := Nat.cast_nonneg (α := ℝ) N; linarith only [hn]) hnonneg) hd.le
    _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
