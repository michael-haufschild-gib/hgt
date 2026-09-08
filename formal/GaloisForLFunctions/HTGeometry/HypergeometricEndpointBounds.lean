import GaloisForLFunctions.HTGeometry.HypergeometricParameterHolomorphy

/-! A uniform linear horizon remainder for the original Gauss sum. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Removing the constant term preserves summability of the uniform majorant. -/
theorem gaussParameterMajorant_tail_summable {B δ r : ℝ} (hB : 0 < B)
    (hr : 0 < r) (hr1 : r < 1) (N : ℕ) :
    Summable (fun n => gaussParameterMajorant B δ N (n+1)*r^n) := by
  have hs := ((summable_nat_add_iff 1).mpr
    (gaussParameterMajorant_summable (δ := δ) hB hr.le hr1 N)).div_const r
  apply hs.congr
  intro n
  simp only [pow_succ]
  field_simp

/-- Uniform parameter bounds control the first spatial remainder by the distance to the horizon. -/
theorem hypergeometric_sub_one_bound {a b c z : ℂ} {B δ r : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hr : 0 < r) (hr1 : r < 1)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hsep : ∀ j : ℕ, δ ≤ ‖c+j‖) (N : ℕ) (hN : B+1 ≤ N) (hz : ‖z‖ ≤ r) :
    ‖ordinaryHypergeometric a b c z-1‖ ≤
      (∑' n, gaussParameterMajorant B δ N (n+1)*r^n)*‖z‖ := by
  have hcoef := gaussParameterMajorant_bound hB hδ ha hb hc hsep N hN
  have hnonneg (n : ℕ) : 0 ≤ gaussParameterMajorant B δ N n := (norm_nonneg _).trans (hcoef n)
  have hs := gaussParameterMajorant_summable (δ := δ) hB hr.le hr1 N
  have ht := gaussParameterMajorant_tail_summable (δ := δ) hB hr hr1 N
  have hbase (n : ℕ) : ‖ordinaryHypergeometricCoefficient a b c n*z^n‖ ≤
      gaussParameterMajorant B δ N n*r^n := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul (hcoef n) (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_nonneg (norm_nonneg _) _) (hnonneg n)
  have hf := hs.of_norm_bounded hbase
  have htail (n : ℕ) : ‖ordinaryHypergeometricCoefficient a b c (n+1)*z^(n+1)‖ ≤
      (gaussParameterMajorant B δ N (n+1)*r^n)*‖z‖ := by
    rw [norm_mul,norm_pow,pow_succ,← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hcoef (n+1)) (pow_le_pow_left₀ (norm_nonneg _) hz _)
        (pow_nonneg (norm_nonneg _) _) (hnonneg (n+1))) (norm_nonneg _)
  have htf := (ht.mul_right ‖z‖).of_norm_bounded htail
  have he : ordinaryHypergeometric a b c z-1 =
      ∑' n, ordinaryHypergeometricCoefficient a b c (n+1)*z^(n+1) := by
    simp only [ordinaryHypergeometric,ordinaryHypergeometric_sum_eq,smul_eq_mul]
    rw [hf.tsum_eq_zero_add]
    simp [ordinaryHypergeometricCoefficient]
  rw [he]
  exact (norm_tsum_le_tsum_norm htf.norm).trans
    ((htf.norm.tsum_le_tsum htail (ht.mul_right ‖z‖)).trans_eq (ht.tsum_mul_right ‖z‖))

end
end GaloisForLFunctions.HTGeometry
