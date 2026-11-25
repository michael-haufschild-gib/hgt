import GaloisForLFunctions.HTGeometry.KroneckerSumSpectrum

/-! # A determinant whose spectral factors are all ordered energy gaps -/

open Matrix
open scoped Matrix Kronecker
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The two-copy generator whose spectrum consists of all differences of energies. -/
def gapOperator (H : Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ :=
  H ⊗ₖ (1:Matrix I I ℂ) - (1:Matrix I I ℂ) ⊗ₖ H

omit [Fintype I] in
theorem gapOperator_affine (A Z : Matrix I I ℂ) (y : ℂ) :
    gapOperator (A+y • Z)=gapOperator A+y • gapOperator Z := by
  ext ⟨i,j⟩ ⟨u,v⟩
  simp only [gapOperator,Matrix.kronecker_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- All ordered gaps occur with their multiplicity, including the zero
diagonal gaps. The formula holds also for a degenerate spectrum. -/
theorem gap_determinant (H : Matrix I I ℂ) (h : H.IsHermitian) (b : ℝ) :
    (Matrix.scalar (I × I) (b:ℂ)-gapOperator H).det =
      ∏ p : I × I, ((b:ℂ)-((h.eigenvalues p.1:ℂ)-(h.eigenvalues p.2:ℂ))) := by
  classical
  let U := (h.eigenvectorUnitary : Matrix I I ℂ)
  let V := U ⊗ₖ U
  let E := Matrix.diagonal (fun i => (h.eigenvalues i:ℂ))
  have hU : U*Uᴴ=1 := eigenvectorUnitary_mul_conjTranspose h
  have hV : V*Vᴴ=1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker,←Matrix.mul_kronecker_mul,hU,Matrix.one_kronecker_one]
  have hH : H=U*E*Uᴴ := h.spectral_theorem
  have hgap : gapOperator H=V*gapOperator E*Vᴴ := by
    dsimp only [V,gapOperator]
    rw [Matrix.conjTranspose_kronecker,Matrix.mul_sub,Matrix.sub_mul]
    congr 1 <;> rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.mul_one,hU,←hH]
  have hdiag : Matrix.scalar (I × I) (b:ℂ)-gapOperator E =
      Matrix.diagonal (fun p : I × I => (b:ℂ)-((h.eigenvalues p.1:ℂ)-(h.eigenvalues p.2:ℂ))) := by
    ext ⟨i,j⟩ ⟨u,v⟩
    by_cases hi : i=u <;> by_cases hj : j=v
    · subst u; subst v; simp [gapOperator,E,Matrix.scalar_apply]
    · subst u; simp [gapOperator,E,Matrix.scalar_apply,hj]
    · subst v; simp [gapOperator,E,Matrix.scalar_apply,hi]
    · simp [gapOperator,E,Matrix.scalar_apply,hi,hj]
  have hshift : Matrix.scalar (I × I) (b:ℂ)-gapOperator H =
      V*(Matrix.scalar (I × I) (b:ℂ)-gapOperator E)*Vᴴ := by
    rw [hgap,Matrix.mul_sub,Matrix.sub_mul]
    congr 1
    rw [scalar_eq_smul_one,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hV]
  have hdet : V.det*Vᴴ.det=1 := by rw [←Matrix.det_mul,hV,Matrix.det_one]
  rw [hshift,hdiag,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal]
  rw [mul_right_comm,hdet,one_mul]

#print axioms gap_determinant
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
