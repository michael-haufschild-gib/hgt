import GaloisForLFunctions.HilbertMetric.Spectral.ClippedTrace
import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.HermitianPosPart

/-!
# Attainment of clipped spectral duality

The optimal dual certificate clips each eigenvalue. The centered certificate
measures the nonorthogonality of a correlation matrix and will survive diagonal
weights between one and two.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem specMap_constant {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) :
    specMap hA (fun _ => c) = (c : ℂ) • (1 : Matrix ι ι ℂ) := by
  unfold specMap
  have hv : (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := Unitary.coe_mul_star_self _
  rw [Unitary.conjStarAlgAut_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hv]
  simp

/-- Eigenvalue clipping gives an admissible Hermitian dual certificate. -/
def certificate {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) : Matrix ι ι ℂ :=
  specMap hA (fun x => min x c)

theorem certificate_hermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) :
    (certificate hA c).IsHermitian := specMap_isHermitian hA _

theorem certificate_cap {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) :
    ((c : ℂ) • (1 : Matrix ι ι ℂ) - certificate hA c).PosSemidef := by
  rw [certificate, ← specMap_constant hA c, ← specMap_sub]
  exact specMap_posSemidef hA fun i => sub_nonneg.mpr (min_le_right _ _)

/-- The clipped certificate attains the complete spectral energy. -/
theorem certificate_attains {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) :
    2 * (trace (certificate hA c * A)).re -
      (trace (certificate hA c * certificate hA c)).re = energy c A := by
  have hp : (trace (certificate hA c * A)).re =
      ∑ i, min (hA.eigenvalues i) c * hA.eigenvalues i := by
    conv_lhs => arg 1; arg 1; arg 2; rw [← specMap_id hA]
    change rtrace (specMap hA (fun x => min x c) * specMap hA id) = _
    rw [← specMap_mul, rtrace_specMap]
    rfl
  have hq : (trace (certificate hA c * certificate hA c)).re =
      ∑ i, (min (hA.eigenvalues i) c) ^ 2 := by
    change rtrace (specMap hA (fun x => min x c) * specMap hA (fun x => min x c)) = _
    rw [← specMap_mul, rtrace_specMap]
    simp only [Pi.mul_apply, pow_two]
  rw [hp, hq, energy, spectralSum_eq hA]
  simp only [quadratic_eq_dual, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- Centered clipping retains exactly the defect energy as a dual trace pairing. -/
theorem centered_certificate {U : Matrix ι ι ℂ} (hU : U.IsHermitian) (τ : ℝ) :
    let C := specMap hU (fun x => min (x - 1) τ)
    C.IsHermitian ∧ ((τ : ℂ) • (1 : Matrix ι ι ℂ) - C).PosSemidef ∧
      2 * (trace (C * (U - 1))).re - (trace (C * C)).re = defectEnergy τ U := by
  dsimp only
  refine ⟨specMap_isHermitian hU _, ?_, ?_⟩
  · rw [← specMap_constant hU τ, ← specMap_sub]
    exact specMap_posSemidef hU fun i => sub_nonneg.mpr (min_le_right _ _)
  · have hu : U - 1 = specMap hU (fun x => x - 1) := by
      rw [show (fun x : ℝ => x - 1) = id - (fun _ => 1) from rfl,
        specMap_sub, specMap_id, specMap_constant]
      simp
    rw [hu, ← specMap_mul, ← specMap_mul]
    change 2 * rtrace (specMap hU _) - rtrace (specMap hU _) = _
    rw [rtrace_specMap, rtrace_specMap, defectEnergy, spectralSum_eq hU]
    simp only [defect, quadratic_eq_dual, Pi.mul_apply,
      Finset.sum_sub_distrib, Finset.mul_sum, pow_two, mul_assoc]

end
end GaloisForLFunctions.HilbertMetric.Clipped
