import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

/-! # What an approximating unitary must distinguish at the spectral endpoints -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat := Matrix I I ℂ

/-- Every column overlap controls the squared operator error between unitaries. -/
theorem column_overlap (X Y : Mat (I:=I)) (hX : X∈unitary _) (hY : Y∈unitary _) (j : I) :
    2-2*((Xᴴ*Y) j j).re ≤ ‖X-Y‖^2 := by
  let C := Xᴴ*Y
  have hx : Xᴴ*X=1 := (Unitary.mem_iff.mp hX).1
  have hy : Yᴴ*Y=1 := (Unitary.mem_iff.mp hY).1
  have he : (X-Y)ᴴ*(X-Y)=1+1-(C+Cᴴ) := by
    simp only [C,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      sub_mul,mul_sub,hx,hy]
    abel
  have h₁ := (Complex.re_le_norm (((X-Y)ᴴ*(X-Y)) j j)).trans
    (norm_entry_le_l2_opNorm ((X-Y)ᴴ*(X-Y)) j j)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self,he] at h₁
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply_eq,Matrix.conjTranspose_apply,
    Complex.sub_re,Complex.add_re,Complex.one_re,Complex.star_def,Complex.conj_re] at h₁
  dsimp only [C] at h₁
  linarith only [h₁]

/-- To improve the scalar midpoint, one gate must distinguish the two
endpoint eigenvectors in its imaginary diagonal expectations. This
necessary excess holds regardless of the spectator eigenphases. -/
theorem endpoint_contrast (u : I → ℂ) (hU : diagonal u∈unitary _) (V : Mat (I:=I))
    (hV : V∈unitary _) (a b : I) (hb : u b=star (u a)) (hc : 0 ≤ (u a).re) :
    2-2*(u a).re-‖diagonal u-V‖^2 ≤ (u a).im*((V a a).im-(V b b).im) := by
  letI : Nonempty I := ⟨a⟩
  have h₁ := column_overlap _ _ hU hV a
  have h₂ := column_overlap _ _ hU hV b
  simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul,Function.comp_apply,
    hb,star_star,Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im] at h₁ h₂
  have hreal (k : I) : (V k k).re ≤ 1 := (Complex.re_le_norm _).trans
    ((norm_entry_le_l2_opNorm V k k).trans_eq (CStarRing.norm_of_mem_unitary hV))
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (hreal a) (hreal b)) hc
  linarith only [h₁,h₂,hsum]

#print axioms column_overlap
#print axioms endpoint_contrast
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation
