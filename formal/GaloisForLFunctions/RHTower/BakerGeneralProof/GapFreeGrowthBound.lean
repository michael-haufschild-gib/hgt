import GaloisForLFunctions.RHTower.BakerGeneralProof.ExponentialPolynomialInterpolation
import GaloisForLFunctions.RHTower.BakerProof.MultipointSchwarz
import GaloisForLFunctions.HTGeometry.SphereMaxModulus
import Mathlib.Analysis.Complex.Liouville

/-!
# Gap-free growth bounds for exponential polynomials

Uniform prescribed zeros force lower growth between concentric circles by multipoint Schwarz.
Contour Hermite interpolation and Cauchy's derivative estimate give the complementary upper
growth bound without a pairwise frequency-separation constant.
-/

open scoped Classical
open Complex Metric
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

theorem analyticAt_exponentialPolynomial {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (z : ℂ) :
    AnalyticAt ℂ (exponentialPolynomial P mu) z := by
  unfold exponentialPolynomial
  exact Finset.analyticAt_fun_sum Finset.univ fun i _ =>
    analyticOnNhd_polyExpC (P i) (mu i) z (Set.mem_univ z)

theorem differentiable_exponentialPolynomial {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) :
    Differentiable ℂ (exponentialPolynomial P mu) :=
  fun z => (analyticAt_exponentialPolynomial P mu z).differentiableAt

theorem norm_zeroFactor_le {points : Finset ℂ} {n : ℕ} {R : ℝ}
    {z : ℂ} (hz : ‖z‖ ≤ R)
    (hpoints : ∀ c ∈ points, ‖c‖ ≤ R) :
    ‖∏ c ∈ points, (z - c) ^ n‖ ≤
      (2 * R) ^ (n * points.card) := by
  rw [norm_prod]
  simp only [norm_pow]
  calc
    ∏ c ∈ points, ‖z - c‖ ^ n ≤ ∏ _c ∈ points, (2 * R) ^ n := by
      apply Finset.prod_le_prod
      · intro c hc
        exact pow_nonneg (norm_nonneg _) n
      · intro c hc
        apply pow_le_pow_left₀ (norm_nonneg _) _ n
        calc
          ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add hz (hpoints c hc)
          _ = 2 * R := by ring
    _ = (2 * R) ^ (n * points.card) := by
      rw [Finset.prod_const]
      exact (pow_mul (2 * R) n points.card).symm

theorem zeroFactor_ge_on_four_sphere {points : Finset ℂ} {n : ℕ} {R : ℝ}
    (hR : 0 < R) {w : ℂ} (hw : ‖w‖ = 4 * R)
    (hpoints : ∀ c ∈ points, ‖c‖ ≤ R) :
    (3 * R) ^ (n * points.card) ≤
      ‖∏ c ∈ points, (w - c) ^ n‖ := by
  rw [norm_prod]
  simp only [norm_pow]
  calc
    (3 * R) ^ (n * points.card) = ∏ _c ∈ points, (3 * R) ^ n := by
      rw [Finset.prod_const]
      exact pow_mul (3 * R) n points.card
    _ ≤ ∏ c ∈ points, ‖w - c‖ ^ n := by
      apply Finset.prod_le_prod
      · intro c hc
        positivity
      · intro c hc
        apply pow_le_pow_left₀ (by positivity) _ n
        have htri : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
          calc
            ‖w‖ = ‖(w - c) + c‖ := by ring_nf
            _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
        linarith [hpoints c hc]

/-- Uniform prescribed zeros force growth between radii `R` and `4R`. -/
theorem multipoint_four_radius_growth
    (F : ℂ → ℂ) (hF : ∀ z, AnalyticAt ℂ F z)
    (points : Finset ℂ) (n : ℕ)
    {R : ℝ} (hR : 0 < R)
    (hpoints : ∀ c ∈ points, ‖c‖ ≤ R)
    (horder : ∀ c ∈ points, n ≤ analyticOrderAt F c)
    {zR z4 : ℂ} (hzR : ‖zR‖ = R)
    (hmax4 : ∀ w : ℂ, ‖w‖ ≤ 4 * R → ‖F w‖ ≤ ‖F z4‖) :
    (3 * R) ^ (n * points.card) * ‖F zR‖ ≤
      (2 * R) ^ (n * points.card) * ‖F z4‖ := by
  have hD : 0 < (3 * R) ^ (n * points.card) := by positivity
  have houter : 0 < 4 * R := by positivity
  have hboundaryF : ∀ w ∈ sphere (0 : ℂ) (4 * R), ‖F w‖ ≤ ‖F z4‖ := by
    intro w hw
    apply hmax4 w
    simpa [mem_sphere_iff_norm] using (show ‖w‖ = 4 * R by
      simpa [mem_sphere_iff_norm] using hw).le
  have hboundaryFactor : ∀ w ∈ sphere (0 : ℂ) (4 * R),
      (3 * R) ^ (n * points.card) ≤
        ‖∏ c ∈ points, (w - c) ^ n‖ := by
    intro w hw
    apply zeroFactor_ge_on_four_sphere hR
    · simpa [mem_sphere_iff_norm] using hw
    · exact hpoints
  have hzRclosed : zR ∈ closedBall (0 : ℂ) (4 * R) := by
    rw [mem_closedBall, dist_zero_right, hzR]
    linarith
  have hschwarz :=
    GaloisForLFunctions.RHTower.BakerProof.multipoint_schwarz_bound
      F hF points n horder houter hD hboundaryF hboundaryFactor hzRclosed
  have hfactor := norm_zeroFactor_le (n := n) hzR.le hpoints
  have hquotNonneg : 0 ≤ ‖F z4‖ / (3 * R) ^ (n * points.card) := by positivity
  have hcoarse : ‖F zR‖ ≤
      (2 * R) ^ (n * points.card) *
        (‖F z4‖ / (3 * R) ^ (n * points.card)) :=
    hschwarz.trans (mul_le_mul_of_nonneg_right hfactor hquotNonneg)
  calc
    (3 * R) ^ (n * points.card) * ‖F zR‖ ≤
        (3 * R) ^ (n * points.card) *
          ((2 * R) ^ (n * points.card) *
            (‖F z4‖ / (3 * R) ^ (n * points.card))) :=
      mul_le_mul_of_nonneg_left hcoarse hD.le
    _ = (2 * R) ^ (n * points.card) * ‖F z4‖ := by
      field_simp [ne_of_gt hD]

/-- The contour interpolant gives a fixed-range jet representation, convenient for estimates. -/
theorem exponentialPolynomial_eq_contourHermite_full_jet_sum
    {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K : ℕ)
    (hP : ∀ i, (P i).natDegree < K)
    (Q : Polynomial ℂ) {rho delta : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hden : ∀ zeta ∈ sphere (0 : ℂ) rho, delta ≤ ‖Q.eval zeta‖)
    (hdvd : ∀ i, (Polynomial.X - Polynomial.C (mu i)) ^ K ∣ Q)
    (hmu : ∀ i, mu i ∈ ball (0 : ℂ) rho)
    (z : ℂ) :
    exponentialPolynomial P mu z =
      ∑ m ∈ Finset.range (Q.natDegree + 1),
        contourHermiteCoeff Q rho z m *
          iteratedDeriv m (exponentialPolynomial P mu) 0 := by
  let L := frequencyJetLinearMap P mu K
  calc
    exponentialPolynomial P mu z = L (contourHermitePolynomial Q rho z) := by
      symm
      exact frequencyJet_contourHermitePolynomial_eq_exponentialPolynomial
        P mu K hP Q hrho hdelta hden hdvd hmu z
    _ = L (∑ m ∈ Finset.range (Q.natDegree + 1),
        contourHermiteCoeff Q rho z m • Polynomial.X ^ m) := by
      congr 1
      unfold contourHermitePolynomial
      apply Finset.sum_congr rfl
      intro m hm
      rw [Polynomial.smul_eq_C_mul]
    _ = ∑ m ∈ Finset.range (Q.natDegree + 1),
        contourHermiteCoeff Q rho z m * L (Polynomial.X ^ m) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ m ∈ Finset.range (Q.natDegree + 1),
        contourHermiteCoeff Q rho z m *
          iteratedDeriv m (exponentialPolynomial P mu) 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [iteratedDeriv_exponentialPolynomial_zero_eq_frequencyJet P mu K m hP]

/-- Gap-free upper growth bound from contour interpolation and Cauchy's derivative estimate. -/
theorem norm_exponentialPolynomial_le_contourHermite
    {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K : ℕ)
    (hP : ∀ i, (P i).natDegree < K)
    (Q : Polynomial ℂ) {rho C delta R M : ℝ}
    (hrho : 1 ≤ rho) (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hcoeff : coeffNormSum Q ≤ C)
    (hden : ∀ zeta ∈ sphere (0 : ℂ) rho, delta ≤ ‖Q.eval zeta‖)
    (hdvd : ∀ i, (Polynomial.X - Polynomial.C (mu i)) ^ K ∣ Q)
    (hmu : ∀ i, mu i ∈ ball (0 : ℂ) rho)
    (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere (0 : ℂ) R,
      ‖exponentialPolynomial P mu w‖ ≤ M)
    (z : ℂ) :
    ‖exponentialPolynomial P mu z‖ ≤
      (rho * (Real.exp (‖z‖ * rho) * (rho ^ Q.natDegree * C) / delta)) *
        ∑ m ∈ Finset.range (Q.natDegree + 1),
          (m.factorial : ℝ) * M / R ^ m := by
  have hrho0 : 0 ≤ rho := le_trans zero_le_one hrho
  let A : ℝ := rho *
    (Real.exp (‖z‖ * rho) * (rho ^ Q.natDegree * C) / delta)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdiff : DiffContOnCl ℂ (exponentialPolynomial P mu) (ball 0 R) :=
    (differentiable_exponentialPolynomial P mu).diffContOnCl
  have hrep := exponentialPolynomial_eq_contourHermite_full_jet_sum
    P mu K hP Q (lt_of_lt_of_le zero_lt_one hrho) hdelta hden hdvd hmu z
  rw [hrep]
  calc
    ‖∑ m ∈ Finset.range (Q.natDegree + 1),
        contourHermiteCoeff Q rho z m *
          iteratedDeriv m (exponentialPolynomial P mu) 0‖
        ≤ ∑ m ∈ Finset.range (Q.natDegree + 1),
          ‖contourHermiteCoeff Q rho z m *
            iteratedDeriv m (exponentialPolynomial P mu) 0‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (Q.natDegree + 1),
          A * ((m.factorial : ℝ) * M / R ^ m) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      apply mul_le_mul
      · exact norm_contourHermiteCoeff_le Q hrho hC hdelta hcoeff hden z m
      · exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
          m hR hdiff hboundary
      · exact norm_nonneg _
      · exact hA
    _ = A * ∑ m ∈ Finset.range (Q.natDegree + 1),
          (m.factorial : ℝ) * M / R ^ m := by
      rw [Finset.mul_sum]

end GaloisForLFunctions.RHTower.BakerGeneralProof
