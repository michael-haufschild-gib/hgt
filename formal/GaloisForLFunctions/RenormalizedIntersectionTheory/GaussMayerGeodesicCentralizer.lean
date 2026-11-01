import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerGeodesicFlow

/-! A nontrivial diagonal modular flow has precisely the signed diagonal
centralizer. Consequently two real frames with the same nonzero integral
return differ only by flow phase on the modular quotient. -/

open Matrix
open scoped MatrixGroups UpperHalfPlane
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicFlow
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicCentralizer

theorem diagonalFlow_injective : Function.Injective diagonalFlow := by
  intro s t h
  have he := congrArg (fun A : Frame => A 0 0) h
  change Real.exp (s/2)=Real.exp (t/2) at he
  have hst := Real.exp_injective he
  linarith only [hst]

theorem diagonalFlow_nat_mul (t : ℝ) (n : ℕ) :
    diagonalFlow ((n : ℝ)*t)=(diagonalFlow t)^n := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul,pow_zero] using diagonalFlow_zero
  | succ n ih =>
    rw [Nat.cast_succ,add_mul,one_mul,diagonalFlow_add,ih,pow_succ]

/-- Commuting with one nonzero diagonal time forces both off-diagonal entries to vanish. -/
theorem commuting_offdiagonal_zero (A : Frame) {t : ℝ} (ht : t ≠ 0)
    (h : A*diagonalFlow t=diagonalFlow t*A) : A 0 1=0 ∧ A 1 0=0 := by
  have hgap : Real.exp (t/2) ≠ Real.exp (-t/2) := by
    intro he
    have he' := Real.exp_injective he
    apply ht
    linarith only [he']
  have h01 := congrArg (fun B : Frame => B 0 1) h
  have h10 := congrArg (fun B : Frame => B 1 0) h
  change ((A : Matrix (Fin 2) (Fin 2) ℝ)*(diagonalFlow t : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 =
    ((diagonalFlow t : Matrix (Fin 2) (Fin 2) ℝ)*(A : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 at h01
  change ((A : Matrix (Fin 2) (Fin 2) ℝ)*(diagonalFlow t : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 =
    ((diagonalFlow t : Matrix (Fin 2) (Fin 2) ℝ)*(A : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 at h10
  simp only [Matrix.mul_apply,Fin.sum_univ_two] at h01 h10
  change A 0 0*0+A 0 1*Real.exp (-t/2)=Real.exp (t/2)*A 0 1+0*A 1 1 at h01
  change A 1 0*Real.exp (t/2)+A 1 1*0=0*A 0 0+Real.exp (-t/2)*A 1 0 at h10
  have hp01 : (Real.exp (t/2)-Real.exp (-t/2))*A 0 1=0 := by nlinarith only [h01]
  have hp10 : (Real.exp (t/2)-Real.exp (-t/2))*A 1 0=0 := by nlinarith only [h10]
  exact ⟨(mul_eq_zero.mp hp01).resolve_left (sub_ne_zero.mpr hgap),
    (mul_eq_zero.mp hp10).resolve_left (sub_ne_zero.mpr hgap)⟩

private theorem positive_diagonal_repr (A : Frame) (h01 : A 0 1=0) (h10 : A 1 0=0)
    (ha : 0 < A 0 0) : A=diagonalFlow (2*Real.log (A 0 0)) := by
  have hdet := A.property
  rw [Matrix.det_fin_two] at hdet
  change A 0 0*A 1 1-A 0 1*A 1 0=1 at hdet
  rw [h01,h10,mul_zero,sub_zero] at hdet
  have hd : A 1 1=(A 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · change A 0 0=Real.exp ((2*Real.log (A 0 0))/2)
    rw [show (2*Real.log (A 0 0))/2=Real.log (A 0 0) by ring,Real.exp_log ha]
  · exact h01
  · exact h10
  · change A 1 1=Real.exp (-(2*Real.log (A 0 0))/2)
    rw [show -(2*Real.log (A 0 0))/2= -Real.log (A 0 0) by ring,
      Real.exp_neg,Real.exp_log ha]
    exact hd

/-- The full real centralizer consists of diagonal times and their central negatives. -/
theorem centralizer_diagonalFlow (A : Frame) {t : ℝ} (ht : t ≠ 0)
    (h : A*diagonalFlow t=diagonalFlow t*A) :
    ∃ u : ℝ, A=diagonalFlow u ∨ A= -diagonalFlow u := by
  obtain ⟨h01,h10⟩ := commuting_offdiagonal_zero A ht h
  have ha0 : A 0 0 ≠ 0 := by
    intro ha
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    change A 0 0*A 1 1-A 0 1*A 1 0=1 at hd
    simp only [ha,h10,zero_mul,mul_zero,sub_zero] at hd
    norm_num at hd
  rcases lt_or_gt_of_ne ha0 with hn | hp
  · have hm01 : (-A) 0 1=0 := by change -A 0 1=0; rw [h01,neg_zero]
    have hm10 : (-A) 1 0=0 := by change -A 1 0=0; rw [h10,neg_zero]
    have hmpos : 0 < (-A) 0 0 := neg_pos.mpr hn
    have hm := positive_diagonal_repr (-A) hm01 hm10 hmpos
    refine ⟨2*Real.log ((-A) 0 0),Or.inr ?_⟩
    simpa only [neg_neg] using congrArg (fun B : Frame => -B) hm
  · exact ⟨2*Real.log (A 0 0),Or.inl (positive_diagonal_repr A h01 h10 hp)⟩

/-- Positive trace excludes the negative component of the centralizer. -/
theorem positive_trace_centralizer (A : Frame) {t : ℝ} (ht : t ≠ 0)
    (h : A*diagonalFlow t=diagonalFlow t*A) (htr : 0 < A 0 0+A 1 1) :
    ∃ u : ℝ, A=diagonalFlow u := by
  obtain ⟨u,hu | hu⟩ := centralizer_diagonalFlow A ht h
  · exact ⟨u,hu⟩
  · have he : A 0 0+A 1 1= -(Real.exp (u/2)+Real.exp (-u/2)) := by
      rw [hu]
      change -Real.exp (u/2)+ -Real.exp (-u/2)= _
      ring
    have h1 := Real.exp_pos (u/2)
    have h2 := Real.exp_pos (-u/2)
    linarith only [htr,he,h1,h2]

private theorem integralMap_neg (A : IntegralFrame) : integralMap (-A)= -integralMap A :=
  SpecialLinearGroup.coe_int_neg A

/-- The integral central element identifies the two real frames with identical projective action. -/
theorem frame_neg (C : Frame) : frame (-C)=frame C := by
  apply (frame_eq_iff (-C) C).mpr
  refine ⟨-1,?_⟩
  rw [integralMap_neg,map_one,neg_mul_neg,one_mul]

/-- Equal nonzero integral returns determine a unique modular geodesic up to time shift. -/
theorem common_return_phase (C D : Frame) {t : ℝ} (ht : t ≠ 0) (γ : IntegralFrame)
    (hC : integralMap γ*C=C*diagonalFlow t)
    (hD : integralMap γ*D=D*diagonalFlow t) :
    ∃ u : ℝ, frame D=flow u (frame C) := by
  let E : Frame := C⁻¹*D
  have hCE : C*E=D := by dsimp only [E]; rw [mul_inv_cancel_left]
  have hE : E*diagonalFlow t=diagonalFlow t*E := by
    apply mul_left_cancel (a := C)
    calc
      C*(E*diagonalFlow t)=(C*E)*diagonalFlow t := (mul_assoc _ _ _).symm
      _ = D*diagonalFlow t := by rw [hCE]
      _ = integralMap γ*D := hD.symm
      _ = integralMap γ*(C*E) := by rw [hCE]
      _ = (integralMap γ*C)*E := (mul_assoc _ _ _).symm
      _ = C*(diagonalFlow t*E) := by rw [hC,mul_assoc]
  obtain ⟨u,hu | hu⟩ := centralizer_diagonalFlow E ht hE
  · refine ⟨u,?_⟩
    rw [← hCE,hu,flow_frame]
  · refine ⟨u,?_⟩
    rw [← hCE,hu,mul_neg,frame_neg,flow_frame]

#print axioms diagonalFlow_injective
#print axioms diagonalFlow_nat_mul
#print axioms commuting_offdiagonal_zero
#print axioms centralizer_diagonalFlow
#print axioms positive_trace_centralizer
#print axioms frame_neg
#print axioms common_return_phase

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicCentralizer
