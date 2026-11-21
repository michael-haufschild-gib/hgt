import GaloisForLFunctions.HTGeometry.DirectionalVandermondeQuantitativePhaseJet

/-! # Integer mode bounds from a cleared derivative matrix -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- The scale uses upper bounds for the cleared entries and column factors. -/
def responseScale {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (s : Fin D → ℂ) : ℝ :=
  (1+∑ j, ‖s j‖) * D.factorial * (1+∑ i, ∑ j, ‖(A*diagonal s) i j‖)^D

/-- For every nonzero integral mode the sum of its responses controls the
cleared determinant. Only upper bounds on column factors enter the scale. -/
theorem cleared_det_le_integer_response {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (s : Fin D → ℂ) (hs : ∀ j, s j ≠ 0) (m : Fin D → ℤ) (hm : m ≠ 0) :
    ‖A.det * ∏ j, s j‖ ≤ responseScale A s * ∑ i, ‖∑ j, A i j * (m j : ℂ)‖ := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra! h
    exact hm (funext h)
  let C := A * diagonal s
  let v (i : Fin D) := (m i : ℂ)/s i
  let y := C.mulVec v
  let S := 1+∑ i, ‖s i‖
  let M := 1+∑ i, ∑ l, ‖C i l‖
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hentry (i l) : ‖C i l‖ ≤ M := by
    have h₁ := Finset.single_le_sum (f := fun a => ‖C i a‖) (fun a _ => norm_nonneg _) (Finset.mem_univ l)
    have h₂ := Finset.single_le_sum (f := fun a => ∑ b, ‖C a b‖)
      (fun a _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    exact (h₁.trans h₂).trans (by dsimp [M]; linarith)
  have hz : 1 ≤ S*‖v j‖ := by
    have hnorm : (1:ℝ) ≤ ‖(m j : ℂ)‖ := by rw [Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hj
    have he : (m j : ℂ) = s j * v j := by dsimp [v]; field_simp [hs j]
    rw [he,norm_mul] at hnorm
    have hsj := Finset.single_le_sum (f := fun i => ‖s i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    exact hnorm.trans (mul_le_mul_of_nonneg_right (hsj.trans (by dsimp [S]; linarith)) (norm_nonneg _))
  have hy (i) : y i = ∑ l, A i l * (m l : ℂ) := by
    change ∑ l, C i l*v l = _
    apply Finset.sum_congr rfl
    intro l _
    simp only [C,Matrix.mul_diagonal,v,mul_assoc,mul_div_cancel₀ _ (hs l)]
  have hc : C.adjugate.mulVec y = C.det • v := by
    change C.adjugate.mulVec (C.mulVec v) = _
    rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
  have hcoord : C.det * v j = ∑ i, C.adjugate j i * y i := (congrFun hc j).symm
  have hcr : ‖C.det‖*‖v j‖ ≤ (D.factorial:ℝ)*M^D * ∑ i, ‖y i‖ := by
    rw [← norm_mul,hcoord,Finset.mul_sum]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_adjugate_apply_le_factorial_mul_pow C hM hentry j i) (norm_nonneg _)
  change _ ≤ (S * D.factorial * M^D) * _
  rw [← Matrix.det_diagonal,← Matrix.det_mul]
  calc ‖C.det‖ ≤ ‖C.det‖ * (S*‖v j‖) := le_mul_of_one_le_right (norm_nonneg _) hz
       _ = S*(‖C.det‖*‖v j‖) := by ring
       _ ≤ S*((D.factorial:ℝ)*M^D * ∑ i, ‖y i‖) := mul_le_mul_of_nonneg_left hcr hS
       _ = _ := by simp only [hy]; ring

/-- Some row attains the determinant lower bound divided by the dimension
and the explicit response scale. -/
theorem exists_cleared_det_response {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (s : Fin D → ℂ) (hs : ∀ j, s j ≠ 0) (m : Fin D → ℤ) (hm : m ≠ 0) :
    ∃ i, ‖A.det * ∏ j, s j‖ ≤ responseScale A s * D * ‖∑ j, A i j * (m j : ℂ)‖ := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra! h
    exact hm (funext h)
  let v (i : Fin D) := ‖∑ j, A i j * (m j : ℂ)‖
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ v ⟨j,Finset.mem_univ j⟩
  have hsum : ∑ l, v l ≤ D*v i := by
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul Finset.univ v (v i) hi
  have hS : 0 ≤ responseScale A s := by unfold responseScale; positivity
  refine ⟨i,(cleared_det_le_integer_response A s hs m hm).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hsum hS

#print axioms exists_cleared_det_response
#print axioms cleared_det_le_integer_response
end
end GaloisForLFunctions.HTGeometry.SpectralJets
