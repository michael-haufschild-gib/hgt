import Mathlib

/-!
# The Báez--Duarte beta wavelet

`w_k(t) = e^{-t}(1 - e^{-2t})^k` and its negative derivative `K_{k+1} = -w_{k+1}'`, the zero-mean
kernel that changes sign exactly once, at the logarithmic aperture `½ log(2k+3)`.
-/

namespace RHTower

open Real MeasureTheory intervalIntegral

noncomputable section

/-- The Báez--Duarte wavelet primitive `w_k(t) = e^{-t}(1 - e^{-2t})^k`. -/
def bdWavelet (k : ℕ) (t : ℝ) : ℝ := Real.exp (-t) * (1 - Real.exp (-2 * t)) ^ k

/-- The zero-mean beta wavelet `K_{k+1} = -w_{k+1}'`. -/
def bdKernel (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t) * (1 - Real.exp (-2 * t)) ^ k * (1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t))

theorem bdWavelet_zero (k : ℕ) : bdWavelet (k + 1) 0 = 0 := by
  simp [bdWavelet]

/-- **Equation (4).**  The kernel is minus the derivative of the wavelet primitive. -/
theorem hasDerivAt_bdWavelet (k : ℕ) (t : ℝ) :
    HasDerivAt (bdWavelet (k + 1)) (-(bdKernel k t)) t := by
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) t := hasDerivAt_neg t
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * (-1)) t := hneg.exp
  have hlin : HasDerivAt (fun t : ℝ => -2 * t) (-2) t := by
    simpa using (hasDerivAt_id' (x := t)).const_mul (-2 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := hlin.exp
  have h2 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-2 * t))
      (-(Real.exp (-2 * t) * (-2))) t := h3.const_sub 1
  have h4 : HasDerivAt (fun t : ℝ => (1 - Real.exp (-2 * t)) ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * (1 - Real.exp (-2 * t)) ^ k * (-(Real.exp (-2 * t) * (-2)))) t :=
    h2.pow (k + 1)
  have h5 : HasDerivAt (fun t : ℝ => Real.exp (-t) * (1 - Real.exp (-2 * t)) ^ (k + 1))
      (Real.exp (-t) * (-1) * (1 - Real.exp (-2 * t)) ^ (k + 1)
        + Real.exp (-t) * (((k + 1 : ℕ) : ℝ) * (1 - Real.exp (-2 * t)) ^ k
            * (-(Real.exp (-2 * t) * (-2))))) t := h1.mul h4
  have hfun : bdWavelet (k + 1) = fun t : ℝ => Real.exp (-t) * (1 - Real.exp (-2 * t)) ^ (k + 1) :=
    rfl
  rw [hfun]
  refine h5.congr_deriv ?_
  push_cast [bdKernel]
  ring

/-! ## The single sign seam -/

/-- The logarithmic aperture `t_k = ½ log(2k+3)` at which the kernel changes sign. -/
def bdSeam (k : ℕ) : ℝ := Real.log (2 * (k : ℝ) + 3) / 2

theorem bdAmplitude_pos (k : ℕ) : (0 : ℝ) < 2 * (k : ℝ) + 3 := by
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem bdSeam_pos (k : ℕ) : 0 < bdSeam k := by
  have h1 : (1 : ℝ) < 2 * (k : ℝ) + 3 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2 := Real.log_pos h1
  rw [bdSeam]
  linarith

theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-2 * t) := by
  have h : Real.exp (-2 * t) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_zero] at h
  linarith

theorem exp_neg_mul_exp (t : ℝ) : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
  rw [← Real.exp_add]
  norm_num

theorem bdAmplitude_lt_exp_iff (k : ℕ) (t : ℝ) :
    2 * (k : ℝ) + 3 < Real.exp (2 * t) ↔ 0 < 1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t) := by
  have hE : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
  have hprod : (2 * (k : ℝ) + 3) * Real.exp (-2 * t) * Real.exp (2 * t) = 2 * (k : ℝ) + 3 := by
    rw [mul_assoc, mul_comm (Real.exp (-2 * t)), exp_neg_mul_exp, mul_one]
  constructor
  · intro h
    have h2 := mul_lt_mul_of_pos_right h (Real.exp_pos (-2 * t))
    rw [exp_neg_mul_exp] at h2
    linarith
  · intro h
    have h2 := mul_lt_mul_of_pos_right (show (2 * (k : ℝ) + 3) * Real.exp (-2 * t) < 1 by linarith) hE
    rw [hprod, one_mul] at h2
    exact h2

/-- Beyond the seam the sign factor is positive. -/
theorem bdSeam_lt_iff (k : ℕ) (t : ℝ) :
    bdSeam k < t ↔ 0 < 1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t) := by
  have hpos := bdAmplitude_pos k
  rw [← bdAmplitude_lt_exp_iff, bdSeam]
  constructor
  · intro h
    have h2 : Real.log (2 * (k : ℝ) + 3) < 2 * t := by linarith
    calc 2 * (k : ℝ) + 3 = Real.exp (Real.log (2 * (k : ℝ) + 3)) := (Real.exp_log hpos).symm
      _ < Real.exp (2 * t) := Real.exp_lt_exp.mpr h2
  · intro h
    have h2 := Real.log_lt_log hpos h
    rw [Real.log_exp] at h2
    linarith

/-- Before the seam the sign factor is negative. -/
theorem lt_bdSeam_iff (k : ℕ) (t : ℝ) :
    t < bdSeam k ↔ 1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t) < 0 := by
  have hpos := bdAmplitude_pos k
  have hE : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
  have hprod : (2 * (k : ℝ) + 3) * Real.exp (-2 * t) * Real.exp (2 * t) = 2 * (k : ℝ) + 3 := by
    rw [mul_assoc, mul_comm (Real.exp (-2 * t)), exp_neg_mul_exp, mul_one]
  constructor
  · intro h
    rw [bdSeam] at h
    have h2 : 2 * t < Real.log (2 * (k : ℝ) + 3) := by linarith
    have h3 : Real.exp (2 * t) < 2 * (k : ℝ) + 3 := by
      calc Real.exp (2 * t) < Real.exp (Real.log (2 * (k : ℝ) + 3)) := Real.exp_lt_exp.mpr h2
        _ = 2 * (k : ℝ) + 3 := Real.exp_log hpos
    have h4 := mul_lt_mul_of_pos_right h3 (Real.exp_pos (-2 * t))
    rw [exp_neg_mul_exp] at h4
    nlinarith [h4]
  · intro h
    have h2 := mul_lt_mul_of_pos_right (show (1 : ℝ) < (2 * (k : ℝ) + 3) * Real.exp (-2 * t) by
      linarith) hE
    rw [hprod, one_mul] at h2
    have h3 := Real.log_lt_log hE h2
    rw [Real.log_exp] at h3
    rw [bdSeam]
    linarith

/-- **Equation (7).**  The kernel is strictly negative before the seam. -/
theorem bdKernel_neg_of_lt_seam {k : ℕ} {t : ℝ} (ht : 0 < t) (h : t < bdSeam k) :
    bdKernel k t < 0 := by
  have h1 : 0 < 1 - Real.exp (-2 * t) := one_sub_exp_pos ht
  have h5 : 1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t) < 0 := (lt_bdSeam_iff k t).mp h
  have hexp : 0 < Real.exp (-t) := Real.exp_pos _
  have hpow : 0 < (1 - Real.exp (-2 * t)) ^ k := pow_pos h1 k
  rw [bdKernel]
  exact mul_neg_of_pos_of_neg (mul_pos hexp hpow) h5

/-- **Equation (7).**  The kernel is strictly positive after the seam. -/
theorem bdKernel_pos_of_seam_lt {k : ℕ} {t : ℝ} (h : bdSeam k < t) : 0 < bdKernel k t := by
  have ht : 0 < t := lt_trans (bdSeam_pos k) h
  have h1 : 0 < 1 - Real.exp (-2 * t) := one_sub_exp_pos ht
  have h2 : 0 < 1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * t) := (bdSeam_lt_iff k t).mp h
  have hexp : 0 < Real.exp (-t) := Real.exp_pos _
  have hpow : 0 < (1 - Real.exp (-2 * t)) ^ k := pow_pos h1 k
  rw [bdKernel]
  exact mul_pos (mul_pos hexp hpow) h2

theorem bdKernel_seam_eq_zero (k : ℕ) : bdKernel k (bdSeam k) = 0 := by
  have hpos := bdAmplitude_pos k
  have hzero : 1 - (2 * (k : ℝ) + 3) * Real.exp (-2 * bdSeam k) = 0 := by
    have hexp : Real.exp (-2 * bdSeam k) = (2 * (k : ℝ) + 3)⁻¹ := by
      rw [bdSeam, show -2 * (Real.log (2 * (k : ℝ) + 3) / 2)
        = -Real.log (2 * (k : ℝ) + 3) by ring, Real.exp_neg, Real.exp_log hpos]
    rw [hexp, mul_inv_cancel₀ (ne_of_gt hpos)]
    ring
  rw [bdKernel, hzero, mul_zero]

end

end RHTower
