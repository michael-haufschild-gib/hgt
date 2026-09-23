import GaloisForLFunctions.HTGeometry.HypergeometricEndpointBounds

/-! Uniform Taylor tails of the original Gauss sum, with every endpoint coefficient retained. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every finite shift of the actual coefficient majorant remains summable. -/
theorem gaussParameterMajorant_shift_summable {B δ r : ℝ} (hB : 0 < B)
    (hr : 0 < r) (hr1 : r < 1) (N k : ℕ) :
    Summable (fun n => gaussParameterMajorant B δ N (n+k)*r^n) := by
  have hs := ((summable_nat_add_iff k).mpr
    (gaussParameterMajorant_summable (δ := δ) hB hr.le hr1 N)).div_const (r^k)
  apply hs.congr
  intro n
  simp only [pow_add]
  field_simp

/-- Removing the actual first coefficients gains exactly their number of endpoint powers. -/
theorem hypergeometric_taylor_remainder_bound {a b c z : ℂ} {B δ r : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hr : 0 < r) (hr1 : r < 1)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hsep : ∀ j : ℕ, δ ≤ ‖c+j‖) (N : ℕ) (hN : B+1 ≤ N) (hz : ‖z‖ ≤ r) (k : ℕ) :
    ‖ordinaryHypergeometric a b c z-
      ∑ n ∈ Finset.range k, ordinaryHypergeometricCoefficient a b c n*z^n‖ ≤
      (∑' n, gaussParameterMajorant B δ N (n+k)*r^n)*‖z‖^k := by
  have hcoef := gaussParameterMajorant_bound hB hδ ha hb hc hsep N hN
  have hnonneg (n : ℕ) : 0 ≤ gaussParameterMajorant B δ N n := (norm_nonneg _).trans (hcoef n)
  have hs := gaussParameterMajorant_summable (δ := δ) hB hr.le hr1 N
  have ht := gaussParameterMajorant_shift_summable (δ := δ) hB hr hr1 N k
  have hbase (n : ℕ) : ‖ordinaryHypergeometricCoefficient a b c n*z^n‖ ≤
      gaussParameterMajorant B δ N n*r^n := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul (hcoef n) (pow_le_pow_left₀ (norm_nonneg _) hz _)
      (pow_nonneg (norm_nonneg _) _) (hnonneg n)
  have hf := hs.of_norm_bounded hbase
  have htail (n : ℕ) : ‖ordinaryHypergeometricCoefficient a b c (n+k)*z^(n+k)‖ ≤
      (gaussParameterMajorant B δ N (n+k)*r^n)*‖z‖^k := by
    rw [norm_mul,norm_pow,pow_add,← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hcoef (n+k)) (pow_le_pow_left₀ (norm_nonneg _) hz _)
        (pow_nonneg (norm_nonneg _) _) (hnonneg (n+k))) (pow_nonneg (norm_nonneg _) _)
  have htf := (ht.mul_right (‖z‖^k)).of_norm_bounded htail
  have he : ordinaryHypergeometric a b c z-
      ∑ n ∈ Finset.range k, ordinaryHypergeometricCoefficient a b c n*z^n =
      ∑' n, ordinaryHypergeometricCoefficient a b c (n+k)*z^(n+k) := by
    simp only [ordinaryHypergeometric,ordinaryHypergeometric_sum_eq,smul_eq_mul]
    have hh := hf.sum_add_tsum_nat_add k
    exact sub_eq_iff_eq_add.mpr (by rw [add_comm]; exact hh.symm)
  rw [he]
  exact (norm_tsum_le_tsum_norm htf.norm).trans
    ((htf.norm.tsum_le_tsum htail (ht.mul_right (‖z‖^k))).trans_eq (ht.tsum_mul_right (‖z‖^k)))

/-- The explicit constant and linear Gauss coefficients leave a uniform quadratic endpoint remainder. -/
theorem hypergeometric_second_endpoint_bound {a b c z : ℂ} {B δ r : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hr : 0 < r) (hr1 : r < 1)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ B)
    (hsep : ∀ j : ℕ, δ ≤ ‖c+j‖) (N : ℕ) (hN : B+1 ≤ N) (hz : ‖z‖ ≤ r) :
    ‖ordinaryHypergeometric a b c z-1-ordinaryHypergeometricCoefficient a b c 1*z‖ ≤
      (∑' n, gaussParameterMajorant B δ N (n+2)*r^n)*‖z‖^(2 : ℕ) := by
  have h := hypergeometric_taylor_remainder_bound hB hδ hr hr1 ha hb hc hsep N hN hz 2
  have hc0 : ordinaryHypergeometricCoefficient a b c 0=1 := by simp [ordinaryHypergeometricCoefficient]
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    pow_zero,pow_one,mul_one,hc0,sub_add_eq_sub_sub] using h

end
end GaloisForLFunctions.HTGeometry
