import GaloisForLFunctions.CompletedArithmeticForms.GaussianJetConvolution
import GaloisForLFunctions.CompletedArithmeticForms.GeometricContraction
import GaloisForLFunctions.CompletedArithmeticForms.HermiteContractionPayment
import GaloisForLFunctions.CompletedArithmeticForms.HermiteSourceBound

/-!
# Quadratic complete-form payment from Gaussian contraction

One source-relative Cauchy contour and the exact contraction formula give a
geometric majorant of the normalized Hermite entries. Its row mass is bounded
independently of dimension, leaving a quadratic source cost for the full form.
-/

noncomputable section

open Finset Matrix Metric

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- One common contour, four times the top Gaussian derivative scale. -/
def gaussianContractionRadius (N : ℕ) : ℝ := 4 * hermiteContourRadius N

theorem gaussianContractionRadius_pos (N : ℕ) : 0 < gaussianContractionRadius N :=
  mul_pos (by norm_num) (hermiteContourRadius_pos N)

theorem gaussianContractionRadius_sq (N : ℕ) :
    gaussianContractionRadius N ^ 2 = 2 * ((N : ℝ) + 1) := by
  rw [gaussianContractionRadius, mul_pow, hermiteContourRadius_sq]
  ring

theorem gaussianContractionRadius_fourth (N : ℕ) :
    gaussianContractionRadius N ^ 4 = 4 * ((N : ℝ) + 1) ^ 2 := by
  calc
    _ = (gaussianContractionRadius N ^ 2) ^ 2 := by ring
    _ = _ := by rw [gaussianContractionRadius_sq]; ring

/-- A bounded source-relative multiplier has a dimension-free geometric entry majorant. -/
theorem gaussianMultiplier_geometric_entry_le {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z ∈ sphere (0 : ℂ) (gaussianContractionRadius N), ‖h z‖ ≤ B)
    (i j : Fin N) :
    ‖mixedKernelJet (gaussianMultiplierKernel h) i.val j.val‖ ≤
      B * geometricContraction N (1 / 2) i j *
        Real.sqrt (hermiteGaussianNormSq i.val) * Real.sqrt (hermiteGaussianNormSq j.val) := by
  have hjet (k : ℕ) : ‖iteratedDeriv k h 0‖ ≤
      (k.factorial : ℝ) * B / gaussianContractionRadius N ^ k :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
      (gaussianContractionRadius_pos N) hh.diffContOnCl hb
  rw [mixedKernelJet_gaussianMultiplier hh]
  calc
    _ ≤ ∑ r ∈ range (min i.val j.val + 1),
        ‖(i.val.choose r : ℂ) * (j.val.choose r : ℂ) * (8 : ℂ) ^ r * (r.factorial : ℂ) *
          iteratedDeriv ((i.val - r) + (j.val - r)) h 0‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ range (min i.val j.val + 1),
        B * (1 / 2 : ℝ) ^ ((i.val - r) + (j.val - r)) *
          Real.sqrt (hermiteGaussianNormSq i.val) * Real.sqrt (hermiteGaussianNormSq j.val) := by
      apply Finset.sum_le_sum
      intro r hr
      have hri : r ≤ i.val := by have := Finset.mem_range.mp hr; omega
      have hrj : r ≤ j.val := by have := Finset.mem_range.mp hr; omega
      have hc := hermiteContractionCoefficient_le hri hrj
        (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt)
      simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_ofNat]
      calc
        _ ≤ (i.val.choose r : ℝ) * (j.val.choose r : ℝ) * (8 : ℝ) ^ r *
            (r.factorial : ℝ) *
            ((((i.val - r) + (j.val - r)).factorial : ℝ) * B /
              gaussianContractionRadius N ^ ((i.val - r) + (j.val - r))) :=
          mul_le_mul_of_nonneg_left (hjet _) (by positivity)
        _ = B * ((i.val.choose r : ℝ) * (j.val.choose r : ℝ) * hermiteGaussianNormSq r *
            (((i.val - r) + (j.val - r)).factorial : ℝ) /
              (4 * hermiteContourRadius N) ^ ((i.val - r) + (j.val - r))) := by
          unfold hermiteGaussianNormSq gaussianContractionRadius
          ring
        _ ≤ B * ((1 / 2 : ℝ) ^ ((i.val - r) + (j.val - r)) *
            Real.sqrt (hermiteGaussianNormSq i.val) * Real.sqrt (hermiteGaussianNormSq j.val)) :=
          mul_le_mul_of_nonneg_left hc hB
        _ = _ := by ring
    _ = _ := by
      rw [geometricContraction_eq_sum]
      simp only [Finset.mul_sum, Finset.sum_mul]

private theorem gaussianContractionRadius_domain (N : ℕ) {q : ℝ}
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ q) :
    3 ≤ q ∧ 1 ≤ gaussianContractionRadius N ∧
      4 * gaussianContractionRadius N ^ 2 ≤ q ∧ gaussianContractionRadius N ^ 4 ≤ q := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hR2 := gaussianContractionRadius_sq N
  have hR4 := gaussianContractionRadius_fourth N
  have hR0 := (gaussianContractionRadius_pos N).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hq, hN, sq_nonneg (N : ℝ)]
  · nlinarith only [hR2, hR0, hN]
  · nlinarith only [hq, hR2, hN, sq_nonneg (N : ℝ)]
  · nlinarith only [hq, hR4, hN, sq_nonneg (N : ℝ)]

/-- Literal first-atom entries obey the complete Gaussian contraction majorant. -/
theorem firstAtomHermiteError_geometric_entry_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (i j : Fin N) :
    |firstAtomHermiteError N x i j| ≤
      (gaussianRelativeErrorConstant * gaussianContractionRadius N ^ 4 /
        thetaCuspSingleAtomReflectionScale 1 x) * geometricContraction N (1 / 2) i j *
          Real.sqrt (hermiteGaussianNormSq i.val) * Real.sqrt (hermiteGaussianNormSq j.val) := by
  obtain ⟨hq3, hR, hRq, hR4q⟩ := gaussianContractionRadius_domain N hq
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq3]
  have hD := gaussianRelativeErrorConstant_pos
  have hb : ∀ z ∈ sphere (0 : ℂ) (gaussianContractionRadius N),
      ‖gaussianProfileError (thetaCuspSingleAtomReflectionScale 1 x) z‖ ≤
        gaussianRelativeErrorConstant * gaussianContractionRadius N ^ 4 /
          thetaCuspSingleAtomReflectionScale 1 x := by
    intro z hz
    have hzn : ‖z‖ = gaussianContractionRadius N := by
      simpa only [mem_sphere_iff_norm, sub_zero] using hz
    exact gaussianRelativeProfile_error_le hq3 hR hRq hR4q hzn.le
  have h := gaussianMultiplier_geometric_entry_le (gaussianProfileError_entire _)
    N (by positivity) hb i j
  rw [← firstAtomWickError_eq_gaussianMultiplier hq3] at h
  exact (Complex.abs_re_le_norm _).trans h

/-- Quadratic source numerator for the complete physical first-atom form. -/
def firstAtomQuadraticFormCost (N : ℕ) : ℝ :=
  16 * gaussianRelativeErrorConstant * ((N : ℝ) + 1) ^ 2

theorem firstAtomQuadraticFormCost_pos (N : ℕ) : 0 < firstAtomQuadraticFormCost N := by
  have hD := gaussianRelativeErrorConstant_pos
  unfold firstAtomQuadraticFormCost
  positivity

/-- The complete first-atom form has a quadratic rank payment in its exact Gaussian norm. -/
theorem firstAtomHermiteHead_quadratic_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (realWickJetMatrix (firstAtomNormalizedRotatedPair x) N -
      hermiteGaussianHead N) *ᵥ v| ≤
      (firstAtomQuadraticFormCost N / thetaCuspSingleAtomReflectionScale 1 x) *
        (v ⬝ᵥ hermiteGaussianHead N *ᵥ v) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hD := gaussianRelativeErrorConstant_pos
  have he := geometricContraction_form_bound (firstAtomHermiteError N x)
    (fun i => Real.sqrt (hermiteGaussianNormSq i.val)) (fun i => Real.sqrt_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by positivity : 0 ≤ gaussianRelativeErrorConstant * gaussianContractionRadius N ^ 4 /
      thetaCuspSingleAtomReflectionScale 1 x)
    (firstAtomHermiteError_geometric_entry_le N hq) v
  rw [firstAtomHermiteError_eq, show ((1 - (1 / 2 : ℝ))⁻¹) ^ 2 = 4 by norm_num] at he
  simp only [Real.sq_sqrt (hermiteGaussianNormSq_pos _).le] at he
  have hg : v ⬝ᵥ hermiteGaussianHead N *ᵥ v =
      ∑ i, hermiteGaussianNormSq i.val * v i ^ 2 := by
    simp only [hermiteGaussianHead, dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hg]
  convert he using 1
  rw [gaussianContractionRadius_fourth]
  unfold firstAtomQuadraticFormCost
  ring

#print axioms gaussianMultiplier_geometric_entry_le
#print axioms firstAtomHermiteError_geometric_entry_le
#print axioms firstAtomHermiteHead_quadratic_error_le

end GaloisForLFunctions.CompletedArithmeticForms
