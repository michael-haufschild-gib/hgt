import GaloisForLFunctions.HTGeometry.GomesFockSpectralPOVM

/-! Internal frames act on complete spectral measures, not merely their moments
or individual effects. This applies the frame viewpoint of arXiv:2404.10461 to
countably additive Fock measurements. Arbitrary conjugations preserve positivity;
normalization and simultaneous data covariance classify the unitary subgroup. -/

open scoped Matrix Classical ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- Conjugation is additive for every internal matrix, without invertibility assumptions. -/
def gomesFockConjugationAddHom {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →+ Matrix (Fin d) (Fin d) ℂ where
  toFun M := gomesFockConjugate U M
  map_zero' := by simp [gomesFockConjugate]
  map_add' M N := by simp [gomesFockConjugate,Matrix.mul_add,Matrix.add_mul]

/-- Finite-dimensional matrix conjugation is continuous. -/
theorem gomesFockConjugationAddHom_continuous {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (gomesFockConjugationAddHom U) := by
  change Continuous (fun M : Matrix (Fin d) (Fin d) ℂ => U*M*Uᴴ)
  fun_prop

/-- Push every spectral effect through an arbitrary internal frame matrix. -/
def gomesFockConjugatedSpectralPOVM {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    VectorMeasure ℝ (Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :=
  (gomesFockSpectralPOVM B).mapRange (gomesFockConjugationAddHom U)
    (gomesFockConjugationAddHom_continuous U)

/-- The transformed measure evaluates by ordinary matrix conjugation. -/
theorem gomesFockConjugatedSpectralPOVM_apply {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    gomesFockConjugatedSpectralPOVM U B S = gomesFockConjugate U (gomesFockSpectralPOVM B S) := rfl

/-- Positivity survives every internal matrix, including singular ones. -/
theorem gomesFockConjugatedSpectralPOVM_posSemidef {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (gomesFockConjugatedSpectralPOVM U B S).PosSemidef :=
  (gomesFockSpectralPOVM_posSemidef B S).mul_mul_conjTranspose_same U

/-- The entire normalization defect is the frame's left Gram matrix. -/
theorem gomesFockConjugatedSpectralPOVM_univ {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    gomesFockConjugatedSpectralPOVM U B Set.univ = U*Uᴴ := by
  simp [gomesFockConjugatedSpectralPOVM_apply,gomesFockSpectralPOVM_univ,gomesFockConjugate]

/-- Normalization holds exactly for unitary internal frames. -/
theorem gomesFockConjugatedSpectralPOVM_normalized_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    gomesFockConjugatedSpectralPOVM U B Set.univ = 1 ↔ Uᴴ*U = 1 := by
  rw [gomesFockConjugatedSpectralPOVM_univ]
  exact mul_eq_one_comm

/-- An arbitrary transformed effect observes the original vector measure at the adjoint-transformed state. -/
theorem gomesFockConjugatedSpectralPOVM_quadratic {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    star x ⬝ᵥ (gomesFockConjugatedSpectralPOVM U B S *ᵥ x) =
      ((gomesFockSpectralMeasure B (Uᴴ*ᵥx)).toSignedMeasure S : ℂ) := by
  rw [gomesFockConjugatedSpectralPOVM_apply]
  have h := gomesFock_quadratic_transport Uᴴ (gomesFockSpectralPOVM B S) x
  simp only [Matrix.conjTranspose_conjTranspose] at h
  change star x ⬝ᵥ ((U*gomesFockSpectralPOVM B S*Uᴴ)*ᵥx) = _
  rw [← h,gomesFockSpectralPOVM_quadratic]

/-- Simultaneous generator transport agrees with operator-measure conjugation exactly for unitary frames. -/
theorem gomesFockSpectralPOVM_unitary_covariance_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      gomesFockSpectralPOVM (gomesFockConjugatedData U B) = gomesFockConjugatedSpectralPOVM U B) ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    have h0 := congrArg (fun μ : VectorMeasure ℝ (Matrix (Fin (d+1)) (Fin (d+1)) ℂ) => μ Set.univ) (h 0)
    simp only [gomesFockSpectralPOVM_univ,gomesFockConjugatedSpectralPOVM_univ] at h0
    exact mul_eq_one_comm.mp h0.symm
  · intro hu B
    apply VectorMeasure.ext
    intro S hS
    simp only [gomesFockConjugatedSpectralPOVM_apply,gomesFockSpectralPOVM_apply,if_pos hS]
    exact (gomesFockWindowMatrix_unitary_covariance_iff U).mpr hu B S

end GaloisForLFunctions.HTGeometry
