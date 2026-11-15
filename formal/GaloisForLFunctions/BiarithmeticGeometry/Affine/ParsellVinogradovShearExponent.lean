import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exact homogeneous-shear overlap exponent

Matching determinant upper and lower bounds identify the optimal real power
for every block dimension: a weighted overlap is uniformly bounded exactly
when its exponent is at most `⌊m²/4⌋`. Independent translations of the two
cubes preserve the same threshold.
-/

open Filter MeasureTheory
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

private theorem regularized_real_volume_bound (q r : ℕ) (θ : ℝ)
    (a b : Fin (2 * q + r) → ℝ) :
    (1 + |θ|) ^ (q * (q + r)) * (volume (shearCubeOverlap q r θ a b)).toReal ≤
      (2 : ℝ) ^ (2 * q + r + q * (q + r)) / min 1 |shearMinorConstant q r| := by
  have hc : 0 < min 1 |shearMinorConstant q r| :=
    lt_min (by norm_num) (abs_pos.mpr (shearMinorConstant_ne_zero q r))
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    regularized_shear_mul_real_volume_le q r θ a b

/-- Balanced blocks have bounded weighted overlap exactly up to their determinant exponent. -/
theorem bounded_balanced_shear_overlap_iff (q r : ℕ) (hr : r ≤ 1) (p : ℝ) :
    (∃ C : ℝ, ∀ θ : ℝ,
      (1 + |θ|) ^ p * (volume (shearCubeOverlap q r θ 0 0)).toReal ≤ C) ↔
        p ≤ (q * (q + r) : ℕ) := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨c, hc, hlo⟩ := exists_regularized_shear_volume_lower q r hr
    by_contra hp
    have hd : 0 < p - (q * (q + r) : ℕ) := sub_pos.mpr (lt_of_not_ge hp)
    have hg : ∀ᶠ x : ℝ in atTop, (|C| + 1) / c < x ^ (p - (q * (q + r) : ℕ)) :=
      (tendsto_rpow_atTop hd).eventually (eventually_gt_atTop ((|C| + 1) / c))
    obtain ⟨x, hxg, hx⟩ := (hg.and (eventually_ge_atTop (1 : ℝ))).exists
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hb : 1 + |x - 1| = x := by rw [abs_of_nonneg (sub_nonneg.mpr hx)]; ring
    have hl := hlo (x - 1)
    have hu := hC (x - 1)
    rw [hb] at hl hu
    have hmul := mul_le_mul_of_nonneg_left hl
      (Real.rpow_nonneg hx0.le (p - (q * (q + r) : ℕ)))
    have he : x ^ (p - (q * (q + r) : ℕ)) * x ^ (q * (q + r)) = x ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
      congr 1
      ring
    have hbound : x ^ (p - (q * (q + r) : ℕ)) * c ≤ C := by
      calc
        _ ≤ x ^ (p - (q * (q + r) : ℕ)) *
            (x ^ (q * (q + r)) * (volume (shearCubeOverlap q r (x - 1) 0 0)).toReal) := hmul
        _ = x ^ p * (volume (shearCubeOverlap q r (x - 1) 0 0)).toReal := by rw [← mul_assoc, he]
        _ ≤ C := hu
    have hxg' := (div_lt_iff₀ hc).mp hxg
    linarith only [hbound, hxg', le_abs_self C]
  · intro hp
    refine ⟨(2 : ℝ) ^ (2 * q + r + q * (q + r)) / min 1 |shearMinorConstant q r|,
      fun θ => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ (q * (q + r)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans
      (regularized_real_volume_bound q r θ 0 0)

private theorem balanced_quarter_square (q r : ℕ) (hr : r ≤ 1) :
    (2 * q + r) ^ 2 / 4 = q * (q + r) := by
  have hr' : r = 0 ∨ r = 1 := by omega
  rcases hr' with rfl | rfl
  · have h : (2 * q + 0) ^ 2 = 4 * (q * (q + 0)) := by ring
    rw [h]; omega
  · have h : (2 * q + 1) ^ 2 = 4 * (q * (q + 1)) + 1 := by ring
    rw [h]; omega

/-- Centered homogeneous shear overlaps have matching quarter-square power bounds. -/
theorem exists_shear_overlap_two_sided (m : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : ℝ,
      ENNReal.ofReal (c / (1 + |θ|) ^ (m ^ 2 / 4)) ≤
        volume (centeredCube (0 : Fin m → ℝ) 1 ∩
          (Matrix.toLin' (shearBlock m θ)) ⁻¹' centeredCube 0 1) ∧
      volume (centeredCube (0 : Fin m → ℝ) 1 ∩
          (Matrix.toLin' (shearBlock m θ)) ⁻¹' centeredCube 0 1) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ (m ^ 2 / 4)) := by
  obtain ⟨C, hC, hupper⟩ := exists_uniform_shear_overlap_decay m
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r ≤ 1 ∧ m = 2 * q + r := by
    refine ⟨m / 2, m % 2, ?_, ?_⟩ <;> omega
  obtain ⟨c, hc, hlower⟩ := exists_regularized_shear_volume_lower q r hr
  refine ⟨c, C, hc, hC, fun θ => ⟨?_, hupper θ 0 0⟩⟩
  rw [balanced_quarter_square q r hr]
  have hp : 0 < (1 + |θ|) ^ (q * (q + r)) := by positivity
  have hreal : c / (1 + |θ|) ^ (q * (q + r)) ≤
      (volume (shearCubeOverlap q r θ 0 0)).toReal := by
    apply (div_le_iff₀ hp).mpr
    rw [mul_comm]
    exact hlower θ
  have hfinite : volume (shearCubeOverlap q r θ 0 0) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (volume_shearCubeOverlap_le q r θ 0 0)
  change ENNReal.ofReal (c / (1 + |θ|) ^ (q * (q + r))) ≤
    volume (shearCubeOverlap q r θ 0 0)
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The exact threshold for every homogeneous block is the integral quarter-square. -/
theorem bounded_shear_overlap_iff (m : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ θ : ℝ,
      (1 + |θ|) ^ p *
        (volume (centeredCube (0 : Fin m → ℝ) 1 ∩
          (Matrix.toLin' (shearBlock m θ)) ⁻¹' centeredCube 0 1)).toReal ≤ C) ↔
            p ≤ (m ^ 2 / 4 : ℕ) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r ≤ 1 ∧ m = 2 * q + r := by
    refine ⟨m / 2, m % 2, ?_, ?_⟩ <;> omega
  rw [balanced_quarter_square q r hr]
  exact bounded_balanced_shear_overlap_iff q r hr p

/-- Allowing arbitrary independent cube centers leaves the sharp threshold unchanged. -/
theorem bounded_shear_overlap_uniform_centers_iff (m : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ : ℝ) (a b : Fin m → ℝ),
      (1 + |θ|) ^ p *
        (volume (centeredCube a 1 ∩
          (Matrix.toLin' (shearBlock m θ)) ⁻¹' centeredCube b 1)).toReal ≤ C) ↔
            p ≤ (m ^ 2 / 4 : ℕ) := by
  constructor
  · rintro ⟨C, hC⟩
    exact (bounded_shear_overlap_iff m p).mp ⟨C, fun θ => hC θ 0 0⟩
  · intro hp
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r ≤ 1 ∧ m = 2 * q + r := by
      refine ⟨m / 2, m % 2, ?_, ?_⟩ <;> omega
    rw [balanced_quarter_square q r hr] at hp
    refine ⟨(2 : ℝ) ^ (2 * q + r + q * (q + r)) / min 1 |shearMinorConstant q r|,
      fun θ a b => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ (q * (q + r)) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans
      (regularized_real_volume_bound q r θ a b)

#print axioms bounded_balanced_shear_overlap_iff
#print axioms exists_shear_overlap_two_sided
#print axioms bounded_shear_overlap_iff
#print axioms bounded_shear_overlap_uniform_centers_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
