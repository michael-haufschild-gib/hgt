import GaloisForLFunctions.HTGeometry.PlanarLogSquare
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireBoundaryLowerBound
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiGrowth
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# An integrable canonical majorant for the logarithm of xi

The analytic residual controls the negative logarithm after subtracting the
finite canonical divisor. Each divisor term is bounded by a translated
positive planar logarithmic kernel, retaining its full multiplicity.
-/

open Complex MeromorphicOn Metric Set
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open RiemannGaussian HTGeometry

/-- The Gaussian and standard normalizations differ by the constant `-2`. -/
theorem gaussianXi_eq_neg_two_mul_xi (z : ℂ) :
    RiemannGaussian.riemannXi z = -2 * _root_.RHTower.xi z := by
  unfold RiemannGaussian.riemannXi _root_.RHTower.xi
  ring

/-- The positive canonical logarithmic mass at an interior point. -/
def xiCanonicalLogMass (n : ℕ) (z : ℂ) : ℝ :=
  ∑ᶠ i : ℂ, (divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℝ) *
    planarLogKernel (2 * xiCanonicalRadius n) (z - i)

theorem xiCanonicalLogMass_nonneg (n : ℕ) (z : ℂ) : 0 ≤ xiCanonicalLogMass n z := by
  unfold xiCanonicalLogMass
  apply finsum_nonneg
  intro i
  exact mul_nonneg (by
    exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i)
    (le_max_left _ _)

private theorem log_norm_canonicalResidual_ge {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖RiemannGaussian.riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ xiCanonicalRadius n / 4) :
    -(2 * A * (xiCanonicalRadius n + 1) ^ 2) ≤
      Real.log ‖riemannXiCanonicalResidual n z‖ := by
  have hR := xiCanonicalRadius_pos n
  have hzball : z ∈ ball 0 (xiCanonicalRadius n) := by
    rw [mem_ball, dist_zero_right]
    linarith only [hz, hR]
  have hratio : ‖z‖ / (xiCanonicalRadius n - ‖z‖) ≤ 1 := by
    apply (div_le_one (by linarith only [hz, hR])).2
    linarith only [hz, hR]
  have hL : ‖riemannXiCanonicalLog n z‖ ≤ 2 * A * (xiCanonicalRadius n + 1) ^ 2 := by
    calc
      ‖riemannXiCanonicalLog n z‖ ≤
          2 * (A * (xiCanonicalRadius n + 1) ^ 2) * ‖z‖ /
            (xiCanonicalRadius n - ‖z‖) :=
        norm_riemannXiCanonicalLog_le_of_growth hA hbound n hzball
      _ = (2 * A * (xiCanonicalRadius n + 1) ^ 2) *
          (‖z‖ / (xiCanonicalRadius n - ‖z‖)) := by ring
      _ ≤ (2 * A * (xiCanonicalRadius n + 1) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := mul_one _
  have hnorm := congrArg norm (exp_riemannXiCanonicalLog_mul_zero_eq n hzball)
  rw [norm_mul, Complex.norm_exp] at hnorm
  have hbase := one_le_norm_riemannXiCanonicalResidual_zero n
  have hlow : Real.exp (-(2 * A * (xiCanonicalRadius n + 1) ^ 2)) ≤
      ‖riemannXiCanonicalResidual n z‖ := by
    calc
      Real.exp (-(2 * A * (xiCanonicalRadius n + 1) ^ 2)) ≤
          Real.exp (-‖riemannXiCanonicalLog n z‖) := Real.exp_le_exp.mpr (neg_le_neg hL)
      _ ≤ Real.exp (riemannXiCanonicalLog n z).re :=
        Real.exp_le_exp.mpr ((abs_le.mp (Complex.abs_re_le_norm _)).1)
      _ ≤ Real.exp (riemannXiCanonicalLog n z).re * ‖riemannXiCanonicalResidual n 0‖ :=
        le_mul_of_one_le_right (Real.exp_pos _).le hbase
      _ = _ := hnorm
  have hlog := Real.log_le_log (Real.exp_pos _) hlow
  rwa [Real.log_exp] at hlog

/-- Canonical factorization bounds both signs of the logarithm, including the totalized value at zeros. -/
theorem abs_log_norm_gaussianXi_le {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖RiemannGaussian.riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ xiCanonicalRadius n / 4) :
    |Real.log ‖RiemannGaussian.riemannXi z‖| ≤
      2 * A * (xiCanonicalRadius n + 1) ^ 2 + xiCanonicalLogMass n z := by
  classical
  have hR := xiCanonicalRadius_pos n
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hM0 : 0 ≤ 2 * A * (xiCanonicalRadius n + 1) ^ 2 := by positivity
  have hmass := xiCanonicalLogMass_nonneg n z
  by_cases hxi : RiemannGaussian.riemannXi z = 0
  · rw [hxi, norm_zero, Real.log_zero, abs_zero]
    exact add_nonneg hM0 hmass
  have hzball : z ∈ ball 0 (xiCanonicalRadius n) := by
    rw [mem_ball, dist_zero_right]
    linarith only [hz, hR]
  have hzclosed := ball_subset_closedBall hzball
  have hfactor (i : ℂ)
      (hi : divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0) :
      Real.log ‖Complex.canonicalFactor (xiCanonicalRadius n) i z‖ ≤
        planarLogKernel (2 * xiCanonicalRadius n) (z - i) := by
    have hiBall := (divisor RiemannGaussian.riemannXi
      (ball 0 (xiCanonicalRadius n))).supportWithinDomain hi
    have hzi : z ≠ i := by
      intro he
      apply hxi
      rw [he]
      exact riemannXi_eq_zero_of_divisor_ball_ne_zero hi
    have hd : 0 < ‖z - i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzi)
    have hnorm := norm_canonicalFactor_le_of_inner_of_separated hR hd hiBall hz (le_refl _)
    have hpos := norm_pos_iff.mpr (Complex.canonicalFactor_ne_zero hiBall hzclosed hzi)
    exact (Real.log_le_log hpos hnorm).trans (le_max_right _ _)
  have hsum :
      (∑ᶠ i : ℂ, (divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℝ) *
        Real.log ‖Complex.canonicalFactor (xiCanonicalRadius n) i z‖) ≤
      xiCanonicalLogMass n z := by
    have hd : (Function.support (fun i : ℂ =>
        divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i)).Finite :=
      (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
    have hs (K : ℂ → ℝ) : Function.support (fun i : ℂ =>
        (divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℝ) * K i) ⊆
        hd.toFinset := by
      intro i hi
      apply hd.mem_toFinset.mpr
      intro hzero
      apply hi
      dsimp only at hzero ⊢
      rw [hzero, Int.cast_zero, zero_mul]
    unfold xiCanonicalLogMass
    rw [finsum_eq_sum_of_support_subset _ (hs _), finsum_eq_sum_of_support_subset _ (hs _)]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i = 0
    · simp only [hi, Int.cast_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hfactor i hi) (by
        exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i)
  have horder : meromorphicOrderAt RiemannGaussian.riemannXi z = 0 :=
    (analyticAt_riemannXi z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hxi
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq hzclosed horder hR
  have hsphere : (∑ᶠ i : ℂ,
      (divisor RiemannGaussian.riemannXi (sphere 0 (xiCanonicalRadius n)) i : ℝ) *
        Real.log ‖z - i‖) = 0 := by
    rw [divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  rw [hsphere, (analyticAt_riemannXi z).meromorphicTrailingCoeffAt_of_ne_zero hxi,
    sub_zero] at hlog
  have hlo := log_norm_canonicalResidual_ge hA hbound n hz
  have hhi := Real.log_le_log (norm_pos_iff.mpr hxi) (hbound z)
  rw [Real.log_exp] at hhi
  have hsq : (‖z‖ + 1) ^ 2 ≤ (xiCanonicalRadius n + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hz, hR]) 2
  have hup := mul_le_mul_of_nonneg_left hsq hA0
  apply abs_le.mpr
  constructor
  · linarith only [hlo, hlog, hsum]
  · nlinarith only [hhi, hup, hM0, hmass]


/-- Actual xi admits one canonical logarithmic majorant on all expanding inner discs. -/
theorem exists_abs_log_norm_gaussianXi_canonical_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ xiCanonicalRadius n / 4 →
      |Real.log ‖RiemannGaussian.riemannXi z‖| ≤
        2 * A * (xiCanonicalRadius n + 1) ^ 2 + xiCanonicalLogMass n z := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun n z hz => abs_log_norm_gaussianXi_le hA hbound n hz⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_abs_log_norm_gaussianXi_canonical_bound
