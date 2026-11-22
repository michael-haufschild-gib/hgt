import GaloisForLFunctions.HTGeometry.ComplexPolynomialRealParameterGenericity
import GaloisForLFunctions.HTGeometry.GaussianSignedPermutationInvariance
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity

/-! # Polynomial nonvanishing on a real Gaussian shell -/
open MvPolynomial MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- A single nonzero value at real parameters certifies almost-sure
nonvanishing for every positive Gaussian variance. -/
theorem gaussian_ae_of_real_witness {n : ℕ} {R : Type*} [CommSemiring R]
    (φ : R →+* ℂ) (P : MvPolynomial (Fin n) R) {v : NNReal} (hv : v≠0)
    (hw : ∃ x : Fin n → ℝ, eval₂Hom φ (fun i => (x i:ℂ)) P ≠ 0) :
    ∀ᵐ x ∂centredProductGaussian (Fin n) v, eval₂Hom φ (fun i => (x i:ℂ)) P ≠ 0 := by
  let Q := MvPolynomial.map φ P
  have he (x : Fin n → ℝ) : eval₂ (RingHom.id ℂ) (fun i => (x i:ℂ)) Q =
      eval₂Hom φ (fun i => (x i:ℂ)) P := eval_map _ _ _
  obtain ⟨z,hz⟩ := hw
  have hnull := (complexPolynomialRealAvoidanceSet_dense_residual_fullMeasure (fun _ => Q)
    (fun _ => ⟨z,(he z).symm ▸ hz⟩)).2.2
  have hac : centredProductGaussian (Fin n) v ≪ volume := productGaussian_absolutelyContinuous n hv _
  have ha : ∀ᵐ x ∂centredProductGaussian (Fin n) v,
      x ∈ complexPolynomialRealAvoidanceSet (fun _ => Q) := ae_iff.mpr (hac hnull)
  filter_upwards [ha] with x hx
  rw [←he]
  exact hx 0

end
end GaloisForLFunctions.HTGeometry.SpectralJets
