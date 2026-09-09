import GaloisForLFunctions.HTGeometry.GomesFockSpectralWindowMatrix

/-!
Reconstruction of the internal unitary gauge from complete spectral-window data,
applying Gomes, arXiv:2404.10461 and arXiv:2607.24901v1. Scalar window observations
and their reconstructed matrices characterize the same gauge exactly; the full
window supplies the identity anchor needed for the converse.
-/
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- All spectral-window masses are jointly gauge-invariant exactly for unitary internal changes. -/
theorem gomesFockWindowMass_unitary_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ S : Set ℝ, ∀ x,
      gomesFockWindowMass (gomesFockConjugatedData U B) S (U*ᵥx) = gomesFockWindowMass B S x) ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff
      (gomesCompletedFockGenerators (0 : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) U).mp
    intro x
    simpa only [gomesFockWindowMass,gomesFockSpectralMeasure_totalMass,freeFockVectorMoment_zero]
      using h 0 Set.univ x
  · intro hu B S x
    exact congrArg (fun μ : MeasureTheory.Measure ℝ => (μ S).toReal)
      ((gomesFockSpectralMeasure_unitary_gauge_iff U).mpr hu B x)

/-- The entire spectral-window tensor menu transforms by conjugation exactly for unitary internal changes. -/
theorem gomesFockWindowMatrix_unitary_covariance_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ S : Set ℝ,
      gomesFockWindowMatrix (gomesFockConjugatedData U B) S =
        gomesFockConjugate U (gomesFockWindowMatrix B S)) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    have h0 := h 0 Set.univ
    have hh : U*Uᴴ = 1 := by
      simpa [gomesFockWindowMatrix_univ,gomesFockConjugate] using h0.symm
    exact mul_eq_one_comm.mp hh
  · intro hu B S
    have huh : U*Uᴴ = 1 := mul_eq_one_comm.mp hu
    have hs : Uᴴ*gomesFockWindowMatrix (gomesFockConjugatedData U B) S*U = gomesFockWindowMatrix B S := by
      apply matrix_eq_of_quadraticForm_eq
      intro x
      rw [← gomesFock_quadratic_transport U (gomesFockWindowMatrix (gomesFockConjugatedData U B) S) x,
        gomesFockWindowMatrix_quadratic,gomesFockWindowMatrix_quadratic]
      exact congrArg (fun r : ℝ => (r : ℂ)) ((gomesFockWindowMass_unitary_gauge_iff U).mpr hu B S x)
    calc
      gomesFockWindowMatrix (gomesFockConjugatedData U B) S =
          (U*Uᴴ)*gomesFockWindowMatrix (gomesFockConjugatedData U B) S*(U*Uᴴ) := by
        rw [huh,one_mul,mul_one]
      _ = gomesFockConjugate U (Uᴴ*gomesFockWindowMatrix (gomesFockConjugatedData U B) S*U) := by
        simp only [gomesFockConjugate,Matrix.mul_assoc]
      _ = gomesFockConjugate U (gomesFockWindowMatrix B S) := congrArg (gomesFockConjugate U) hs

end GaloisForLFunctions.HTGeometry
