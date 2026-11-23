import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance

/-! # Squared displacement of two spectral lists in their overlap coupling -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat := Matrix I I ℂ

/-- Unitary changes of row and column bases preserve squared Frobenius norm. -/
theorem translate_frob (U A V : Mat (I:=I)) (hu : Uᴴ*U=1) (hv : V*Vᴴ=1) :
    hsNormSq (U*A*V)=hsNormSq A := by
  have he : (U*A*V)ᴴ*(U*A*V)=Vᴴ*(Aᴴ*A)*V := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul]
    simp only [mul_assoc]
    rw [←mul_assoc Uᴴ U,hu,one_mul]
  apply Complex.ofReal_injective
  rw [hsNormSq_matrix_eq_trace,hsNormSq_matrix_eq_trace,he,Matrix.trace_mul_comm (Vᴴ*(Aᴴ*A)) V,←mul_assoc,hv,one_mul]

/-- In the two eigenbases, each squared spectral displacement is
weighted by the squared modulus of the overlap of the corresponding
eigenvectors. Both marginals of the weight matrix have unit mass. -/
theorem spectral_displacement (U V : Mat (I:=I)) (hu : U∈unitary _) (hv : V∈unitary _)
    (x y : I → ℂ) :
    hsNormSq (U*diagonal x*Uᴴ-V*diagonal y*Vᴴ)=
      ∑ j, ∑ i, ‖x i-y j‖^2*‖(Uᴴ*V) i j‖^2 := by
  let M := U*diagonal x*Uᴴ-V*diagonal y*Vᴴ
  let Q := Uᴴ*V
  have hU : Uᴴ*U=1 := (Unitary.mem_iff.mp hu).1
  have hV : Vᴴ*V=1 := (Unitary.mem_iff.mp hv).1
  have h : Uᴴ*M*V=diagonal x*Q-Q*diagonal y := by
    dsimp only [M,Q]
    rw [mul_sub,sub_mul]
    simp only [mul_assoc,hV,mul_one]
    rw [←mul_assoc Uᴴ U,hU,one_mul]
  have he (i j : I) : (diagonal x*Q-Q*diagonal y) i j=(x i-y j)*Q i j := by
    rw [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,sub_mul,mul_comm (y j)]
  change hsNormSq M=_
  rw [←translate_frob Uᴴ M V (by simpa only [Matrix.conjTranspose_conjTranspose] using
    (Unitary.mem_iff.mp hu).2) (Unitary.mem_iff.mp hv).2,h,hsNormSq]
  simp only [he,norm_mul,mul_pow,Q]

/-- A scalar Lipschitz estimate transfers to Frobenius distance with
the same constant, even when the two spectral bases differ. -/
theorem spectral_lipschitz (U V : Mat (I:=I)) (hu : U∈unitary _) (hv : V∈unitary _)
    (x y : I → ℂ) (f g : I → ℂ) {L : ℝ} (hL : 0≤L)
    (h : ∀ i j, ‖f i-g j‖≤L*‖x i-y j‖) :
    hsNormSq (U*diagonal f*Uᴴ-V*diagonal g*Vᴴ) ≤
      L^2*hsNormSq (U*diagonal x*Uᴴ-V*diagonal y*Vᴴ) := by
  rw [spectral_displacement U V hu hv,spectral_displacement U V hu hv,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr (h i j)
  rw [mul_pow] at hh
  exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (mul_assoc ..)

#print axioms spectral_displacement
#print axioms spectral_lipschitz
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
