import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheBoxCameraSeesNearTopClusters

/-!
# Geometric exterior loss beats a fixed depth deficit

At order `n`, allow logarithmic zero mass proportional to `n+1`. After
dividing by a signal of size `exp(-η b (n+1))`, both exterior terms are
polynomial multiples of geometric sequences. Their ratios are
`exp(η b)/(h g)` and `exp(η b-d a)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

def boxRelativeExteriorMajorant (A h g d a b η L : ℝ) (n : ℕ) : ℝ :=
  8 * (xiLineTwoLogDerivConstant + L) *
    (((2 / h) * ((1 + g ^ 2) / g ^ 2)) * Real.exp (η * b) *
        (((n : ℝ) + 1) * (Real.exp (η * b) / (h * g)) ^ n) +
      (4 * A + 4 / h) * Real.exp (η * b - d * a) *
        (((n : ℝ) + 1) * Real.exp (η * b - d * a) ^ n))

private theorem tendsto_succ_mul_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) atTop (𝓝 0) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm).tendsto_atTop_zero
  have h0 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hnorm).tendsto_atTop_zero
  have hs := h1.add h0
  simpa only [pow_one, pow_zero, one_mul, zero_add, add_mul, one_mul] using hs

theorem tendsto_boxRelativeExteriorMajorant
    {A h g d a b η L : ℝ} (hh : 0 < h) (hg : 0 < g)
    (hgap : Real.exp (η * b) < h * g) (hdepth : η * b < d * a) :
    Tendsto (boxRelativeExteriorMajorant A h g d a b η L) atTop (𝓝 0) := by
  have hq := tendsto_succ_mul_geometric
    (by positivity : 0 ≤ Real.exp (η * b) / (h * g))
    ((div_lt_one (mul_pos hh hg)).mpr hgap)
  have hp := tendsto_succ_mul_geometric (Real.exp_pos (η * b - d * a)).le
    (Real.exp_lt_one_iff.mpr (sub_neg.mpr hdepth))
  have hs := (hq.const_mul (((2 / h) * ((1 + g ^ 2) / g ^ 2)) * Real.exp (η * b))).add
    (hp.const_mul ((4 * A + 4 / h) * Real.exp (η * b - d * a)))
  have ht := hs.const_mul (8 * (xiLineTwoLogDerivConstant + L))
  simp only [mul_zero, add_zero] at ht
  exact ht.congr fun n => rfl

/-- The existing logarithmic zero-mass estimate supplies the entire height cost. -/
theorem boxExteriorBound_mul_exp_le
    {A h r g d a b η L y t : ℝ} (hA : 0 ≤ A) (hh : 0 < h)
    (hg : 0 < g) (hd : 0 ≤ d) (hL : 0 ≤ L) (n : ℕ)
    (hlag : a * ((n : ℝ) + 1) ≤ y - boxCameraRadius A h n r)
    (ht : Real.log (|t| + 4) ≤ L * ((n : ℝ) + 1)) :
    boxExteriorBound A h n r g d y t * Real.exp (η * b * ((n : ℝ) + 1)) ≤
      boxRelativeExteriorMajorant A h g d a b η L n := by
  have hξ := xiLineTwoLogDerivConstant_nonneg
  have hmass : lorentzMass t ≤
      (8 * (xiLineTwoLogDerivConstant + L)) * ((n : ℝ) + 1) := by
    have hc := le_mul_of_one_le_right xiLineTwoLogDerivConstant_nonneg
      (show (1 : ℝ) ≤ (n : ℝ) + 1 from le_add_of_nonneg_left (Nat.cast_nonneg n))
    have hm := lorentzMass_le_log t
    nlinarith only [hc, hm, ht]
  have he : Real.exp (η * b * ((n : ℝ) + 1)) =
      Real.exp (η * b) * Real.exp (η * b) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hq : (1 / (h * g)) ^ n * Real.exp (η * b * ((n : ℝ) + 1)) =
      Real.exp (η * b) * (Real.exp (η * b) / (h * g)) ^ n := by
    simp only [he, div_pow, one_pow]
    ring
  have hp : Real.exp (-(d * (y - boxCameraRadius A h n r))) *
      Real.exp (η * b * ((n : ℝ) + 1)) ≤
      Real.exp (η * b - d * a) * Real.exp (η * b - d * a) ^ n := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hlag hd
    nlinarith only [hm]
  unfold boxExteriorBound
  calc
    _ ≤ (((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n +
          (4 * A + 4 / h) * Real.exp (-(d * (y - boxCameraRadius A h n r)))) *
        ((8 * (xiLineTwoLogDerivConstant + L)) * ((n : ℝ) + 1))) *
          Real.exp (η * b * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity))
        (Real.exp_pos _).le
    _ = (8 * (xiLineTwoLogDerivConstant + L)) * ((n : ℝ) + 1) *
        (((2 / h) * ((1 + g ^ 2) / g ^ 2)) *
          ((1 / (h * g)) ^ n * Real.exp (η * b * ((n : ℝ) + 1))) +
        (4 * A + 4 / h) * (Real.exp (-(d * (y - boxCameraRadius A h n r))) *
          Real.exp (η * b * ((n : ℝ) + 1)))) := by ring
    _ ≤ (8 * (xiLineTwoLogDerivConstant + L)) * ((n : ℝ) + 1) *
        (((2 / h) * ((1 + g ^ 2) / g ^ 2)) *
          (Real.exp (η * b) * (Real.exp (η * b) / (h * g)) ^ n) +
        (4 * A + 4 / h) *
          (Real.exp (η * b - d * a) * Real.exp (η * b - d * a) ^ n)) := by
      rw [hq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by unfold boxRelativeExteriorMajorant; ring

/-- Both rate inequalities hold for a fixed positive depth deficit. -/
theorem exists_positive_box_depth_deficit {h g d a b : ℝ}
    (hgap : 1 < h * g) (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    ∃ η : ℝ, 0 < η ∧ Real.exp (η * b) < h * g ∧ η * b < d * a := by
  have hl : 0 < Real.log (h * g) := Real.log_pos hgap
  have hm : 0 < min (Real.log (h * g)) (d * a) := lt_min hl (mul_pos hd ha)
  have he : min (Real.log (h * g)) (d * a) / (2 * b) * b =
      min (Real.log (h * g)) (d * a) / 2 := by field_simp [hb.ne']
  refine ⟨min (Real.log (h * g)) (d * a) / (2 * b), by positivity, ?_, ?_⟩
  · rw [he]
    have hlt : min (Real.log (h * g)) (d * a) / 2 < Real.log (h * g) := by
      linarith only [hm, min_le_left (Real.log (h * g)) (d * a)]
    exact (Real.exp_lt_exp.mpr hlt).trans_eq (Real.exp_log (zero_lt_one.trans hgap))
  · rw [he]
    linarith only [hm, min_le_right (Real.log (h * g)) (d * a)]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
