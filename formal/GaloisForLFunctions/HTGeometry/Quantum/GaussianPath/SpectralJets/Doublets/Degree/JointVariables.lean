import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.FieldSpecialization

/-! # A common polynomial grading for the background and differentiated fields -/
open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {ρ κ R : Type*} [CommRing R]

def backgroundSlot (j : ρ) : Option (ρ ⊕ κ) := some (.inl j)
def fieldSlot : Option κ → Option (ρ ⊕ κ) := Option.map Sum.inr

private theorem fieldSlot_injective : Function.Injective (fieldSlot (ρ := ρ) (κ := κ)) := by
  intro i j
  cases i <;> cases j <;> simp [fieldSlot]

private theorem separate_slots (i : ρ) (j : Option κ) : backgroundSlot i ≠ fieldSlot j := by
  cases j <;> simp [backgroundSlot,fieldSlot]

/-- Flatten polynomial coefficients in the background variables without identifying any
background, energy, or perturbation variable. -/
def joint : MvPolynomial (Option κ) (MvPolynomial ρ R) →+* MvPolynomial (Option (ρ ⊕ κ)) R :=
  eval₂Hom (rename (R := R) backgroundSlot).toRingHom (fun i => X (fieldSlot i))

@[simp] theorem joint_C (q : MvPolynomial ρ R) :
    joint (κ := κ) (C q) = rename backgroundSlot q := eval₂Hom_C ..

@[simp] theorem joint_X (i : Option κ) :
    joint (R := R) (ρ := ρ) (X i) = X (fieldSlot i) := eval₂Hom_X' ..

private theorem pderiv_background (q : MvPolynomial ρ R) (i : Option κ) :
    pderiv (fieldSlot i) (rename backgroundSlot q) = 0 := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add a b ha hb => simp only [map_add,ha,hb,add_zero]
  | mul_X a j ha =>
    rw [map_mul,rename_X,Derivation.leibniz,pderiv_X_of_ne (separate_slots j i),ha]
    simp

/-- Formal differentiation with respect to a non-background variable survives flattening. -/
theorem joint_pderiv (i : Option κ) (q : MvPolynomial (Option κ) (MvPolynomial ρ R)) :
    joint (pderiv i q) = pderiv (fieldSlot i) (joint q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C c => rw [pderiv_C,map_zero,joint_C,pderiv_background]
  | add a b ha hb => simp only [map_add,ha,hb]
  | mul_X a j ha =>
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,map_add,map_mul,joint_X,ha]
    by_cases h : j=i
    · subst j; simp
    · rw [pderiv_X_of_ne h,pderiv_X_of_ne (fieldSlot_injective.ne h),map_zero]

private theorem joint_numerator (p : MvPolynomial (Option κ) (MvPolynomial ρ R)) (w : List κ) :
    joint (numerator p w) = numerator (joint p) (w.map (Sum.inr : κ → ρ ⊕ κ)) := by
  induction w with
  | nil => simp only [numerator,List.map_nil,joint_X]; rfl
  | cons i w ih =>
    simp only [List.map_cons,numerator,tangent,map_mul,map_sub,map_nsmul,joint_pderiv,ih,List.length_map]
    rfl

theorem joint_fieldJet (p : MvPolynomial (Option κ) (MvPolynomial ρ R)) (L : ℕ) (w : List κ) :
    joint (jetRow p L (some w)) =
      jetRow (joint p) L (some (w.map (Sum.inr : κ → ρ ⊕ κ))) := by
  simp only [jetRow,cleared,map_mul,map_pow,joint_pderiv,joint_numerator,List.length_map]
  rfl

end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
