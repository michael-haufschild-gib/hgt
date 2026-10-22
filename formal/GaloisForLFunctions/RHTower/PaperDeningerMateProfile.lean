import GaloisForLFunctions.RHTower.Deninger.DeningerOneSidedFramedMateCurvatureTransgression
import GaloisForLFunctions.HTGeometry.PaperConvergentDiagonal

/-! # Bounded profiles of the literal Deninger mate curvature

Every degree `j+2` is retained. Dividing the actual radial curvature by its
positive reciprocal-gain sum gives a hyperbolic tangent, with a signed cofinal
limit. This introduces no curvature-vanishing premise.
-/

namespace RHTower
noncomputable section
open Filter Topology

def paperDeningerMateEnergy (s : ℂ) (j : ℕ) : ℝ :=
  deningerHalfDensityMateGain (j + 2) s + (deningerHalfDensityMateGain (j + 2) s)⁻¹

theorem paperDeningerMateEnergy_pos (s : ℂ) (j : ℕ) :
    0 < paperDeningerMateEnergy s j :=
  add_pos (deningerHalfDensityMateGain_pos _ _) (inv_pos.mpr (deningerHalfDensityMateGain_pos _ _))

/-- The numerator is the existing arithmetic mate curvature. -/
def paperDeningerMateWeight (s : ℂ) (j : ℕ) : ℝ :=
  deningerTensorSquareRadialMateCurvature (j + 2) s / paperDeningerMateEnergy s j

theorem paperDeningerMateWeight_eq_tanh (s : ℂ) (j : ℕ) :
    paperDeningerMateWeight s j = Real.tanh ((2 * s.re - 1) * Real.log (j + 2 : ℕ)) := by
  rw [paperDeningerMateWeight,
    ← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature (by omega : 0 < j + 2) s]
  simp only [paperDeningerMateEnergy, deningerHalfDensityMateGain, Real.tanh_eq, Real.exp_neg]

theorem abs_paperDeningerMateWeight_lt_one (s : ℂ) (j : ℕ) :
    |paperDeningerMateWeight s j| < 1 := by
  rw [paperDeningerMateWeight_eq_tanh]
  exact Real.abs_tanh_lt_one _

def paperDeningerMateLimit (s : ℂ) : ℝ :=
  if s.re = 1 / 2 then 0 else if s.re < 1 / 2 then -1 else 1

private theorem tanh_rescaled (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-x) * Real.exp (-x)) /
      (1 + Real.exp (-x) * Real.exp (-x)) := by
  rw [Real.tanh_eq, Real.exp_neg]
  have hp := Real.exp_pos x
  field_simp

private theorem tendsto_tanh_atTop_one : Tendsto Real.tanh atTop (𝓝 1) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.mul Real.tendsto_exp_neg_atTop_nhds_zero
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub h).div (tendsto_const_nhds.add h)
    (by norm_num : (1 : ℝ) + 0 * 0 ≠ 0)
  simpa only [mul_zero, sub_zero, add_zero, div_one] using
    hlim.congr (fun x => (tanh_rescaled x).symm)

theorem paperDeningerMateWeight_tendsto (s : ℂ) :
    Tendsto (paperDeningerMateWeight s) atTop (𝓝 (paperDeningerMateLimit s)) := by
  have hlog : Tendsto (fun j : ℕ => Real.log (j + 2 : ℕ)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
  change Tendsto (fun j => paperDeningerMateWeight s j) atTop (𝓝 (paperDeningerMateLimit s))
  simp_rw [paperDeningerMateWeight_eq_tanh]
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · have hp : 0 < -(2 * s.re - 1) := by linarith
    have ht := (tendsto_tanh_atTop_one.comp (hlog.const_mul_atTop hp)).neg
    have he (j : ℕ) : -Real.tanh (-(2 * s.re - 1) * Real.log (j + 2 : ℕ)) =
        Real.tanh ((2 * s.re - 1) * Real.log (j + 2 : ℕ)) := by
      rw [neg_mul, Real.tanh_neg, neg_neg]
    simpa only [paperDeningerMateLimit, if_neg (ne_of_lt h), if_pos h, Function.comp_def, he] using ht
  · simp [paperDeningerMateLimit, h]
  · have hp : 0 < 2 * s.re - 1 := by linarith
    simpa only [paperDeningerMateLimit, if_neg (ne_of_gt h), if_neg (not_lt_of_ge h.le),
      Function.comp_def] using
      tendsto_tanh_atTop_one.comp (hlog.const_mul_atTop hp)

theorem paperDeningerMateWeight_complex_tendsto (s : ℂ) :
    Tendsto (fun j => (paperDeningerMateWeight s j : ℂ)) atTop
      (𝓝 (paperDeningerMateLimit s : ℂ)) :=
  Complex.continuous_ofReal.continuousAt.tendsto.comp (paperDeningerMateWeight_tendsto s)

theorem paperDeningerMateLimit_eq_zero_iff (s : ℂ) :
    paperDeningerMateLimit s = 0 ↔ s.re = 1 / 2 := by
  simp only [paperDeningerMateLimit]
  split_ifs <;> simp_all

theorem norm_paperDeningerMateLimit (s : ℂ) :
    ‖(paperDeningerMateLimit s : ℂ)‖ = if s.re = 1 / 2 then 0 else 1 := by
  simp only [paperDeningerMateLimit]
  split_ifs <;> norm_num

theorem paperDeningerMateWeight_critical (s : ℂ) (h : s.re = 1 / 2) (j : ℕ) :
    paperDeningerMateWeight s j = 0 := by
  simp [paperDeningerMateWeight_eq_tanh, h]

end
end RHTower
