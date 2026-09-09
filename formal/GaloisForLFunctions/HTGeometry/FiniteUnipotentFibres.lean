import GaloisForLFunctions.HTGeometry.FiniteRingSl2

/-!
# Exact upper–lower–upper collision fibres over commutative rings

Every parameter collision is an annihilator translation (a+t,c-t), with b*t=0.
The sum of the two outer parameters is conserved. An explicit fibre equivalence
therefore gives exact multiplicity over composite residue rings, retaining nonunits
and the zero ring without a field or cancellation assumption.
-/

namespace GaloisForLFunctions.HTGeometry.FiniteUnipotentFibres
open FiniteRingSl2
noncomputable section
variable {R : Type*} [CommRing R]

/-- The actual three elementary factors in the determinant-one group. -/
def triple (a b c : R) : Matrix.SpecialLinearGroup (Fin 2) R := upper a*lower b*upper c

/-- The first diagonal entry of the actual three-factor word. -/
theorem triple_entry00 (a b c : R) : triple a b c 0 0=1+a*b := by
  simp [triple,upper,lower,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

/-- The complete upper-right entry, retaining its mixed product. -/
theorem triple_entry01 (a b c : R) : triple a b c 0 1=a+c+a*b*c := by
  simp [triple,upper,lower,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  ring

/-- The lower entry recovers the middle parameter exactly. -/
theorem triple_entry10 (a b c : R) : triple a b c 1 0=b := by
  simp [triple,upper,lower,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

/-- The second diagonal entry of the actual three-factor word. -/
theorem triple_entry11 (a b c : R) : triple a b c 1 1=1+b*c := by
  simp [triple,upper,lower,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  ring

/-- Complete collision classification at any fixed middle parameter, including nonunits. -/
theorem triple_collision (a b c a' c' : R) :
    triple a' b c'=triple a b c ↔ b*(a'-a)=0 ∧ a'+c'=a+c := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) R => M 0 0) h
    have h01 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) R => M 0 1) h
    have h11 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) R => M 1 1) h
    rw [triple_entry00,triple_entry00] at h00
    rw [triple_entry01,triple_entry01] at h01
    rw [triple_entry11,triple_entry11] at h11
    constructor
    · linear_combination h00
    · linear_combination h01-c'*h00-a*h11
  · rintro ⟨hb,hs⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · change triple a' b c' 0 0=triple a b c 0 0
      rw [triple_entry00,triple_entry00]
      linear_combination hb
    · change triple a' b c' 0 1=triple a b c 0 1
      rw [triple_entry01,triple_entry01]
      linear_combination (1+a*b)*hs+(c'-a)*hb
    · change triple a' b c' 1 0=triple a b c 1 0
      rw [triple_entry10,triple_entry10]
    · change triple a' b c' 1 1=triple a b c 1 1
      rw [triple_entry11,triple_entry11]
      linear_combination b*hs-hb

/-- Every annihilator translation preserves the actual three-factor word. -/
theorem triple_translate (a b c t : R) (ht : b*t=0) :
    triple (a+t) b (c-t)=triple a b c := by
  apply (triple_collision a b c (a+t) (c-t)).mpr
  constructor
  · simpa using ht
  · ring

/-- The full parameter fibre is explicitly equivalent to the middle-parameter annihilator. -/
def fibreEquiv (a b c : R) :
    {t : R // b*t=0} ≃ {u : R×R // triple u.1 b u.2=triple a b c} where
  toFun t := ⟨(a+t.1,c-t.1),triple_translate a b c t.1 t.2⟩
  invFun u := ⟨u.1.1-a,((triple_collision a b c u.1.1 u.1.2).mp u.2).1⟩
  left_inv t := by apply Subtype.ext; simp
  right_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · have hs := ((triple_collision a b c u.1.1 u.1.2).mp u.2).2
      dsimp
      linear_combination -hs

/-- The exact fibre multiplicity is the cardinality of the annihilator. -/
theorem fibre_card (a b c : R) :
    Nat.card {u : R×R // triple u.1 b u.2=triple a b c}=Nat.card {t : R // b*t=0} :=
  (Nat.card_congr (fibreEquiv a b c)).symm


/-- Every full collision fixes the middle parameter and conserves the outer sum. -/
theorem triple_collision_full (a b c a' b' c' : R) :
    triple a' b' c'=triple a b c ↔ b'=b ∧ b*(a'-a)=0 ∧ a'+c'=a+c := by
  constructor
  · intro h
    have hb := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) R => M 1 0) h
    rw [triple_entry10,triple_entry10] at hb
    subst b'
    exact ⟨rfl,(triple_collision a b c a' c').mp h⟩
  · rintro ⟨hb,h⟩
    rw [hb]
    exact (triple_collision a b c a' c').mpr h

end
end GaloisForLFunctions.HTGeometry.FiniteUnipotentFibres
