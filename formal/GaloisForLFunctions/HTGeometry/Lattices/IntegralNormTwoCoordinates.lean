import GaloisForLFunctions.HTGeometry.Lattices.IntegralFourEnergy
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Fintype.Sigma

/-!
# The norm-two shells in the classical coordinate lattices

An unrestricted integer vector of Euclidean squared norm two has two
coordinates with independent signs. Imposing coordinate sum zero forces
opposite signs and orders the two endpoints. These are the coordinate
models for the D and A root systems, respectively.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.IntegralZeroSum
variable {J : Type*} [Fintype J]

abbrev TwoShell (J : Type*) [Fintype J] := {x : J → ℤ // energy x=2}
abbrev ZeroShell (J : Type*) [Fintype J] := {x : J → ℤ // (∑ i, x i)=0 ∧ energy x=2}
abbrev SignedPair (J : Type*) := Σ S : Set.powersetCard J 2, S.val → Bool

/-- Squared energy and coordinate sum have the same parity. -/
theorem energy_sub_sum_even (x : J → ℤ) :
    Even (energy x-∑ i, x i) := by
  have h (i) : Even ((x i)^2-x i) := by convert Int.even_mul_pred_self (x i) using 1 <;> ring
  choose k hk using h
  refine ⟨∑ i,k i,?_⟩
  rw [energy,← sum_sub_distrib,← sum_add_distrib]
  exact sum_congr rfl fun i _ => hk i

/-- The two signs of a nonzero coordinate. -/
def unitSign (b : Bool) : ℤ := if b then -1 else 1

private theorem sign_sq (b : Bool) : unitSign b^2=1 := by cases b <;> norm_num [unitSign]

private theorem unitSign_injective : Function.Injective unitSign := by
  intro a b h
  cases a <;> cases b <;> norm_num [unitSign] at h ⊢

private def support₂ (x : J → ℤ) : Finset J := univ.filter fun i => x i≠0

private theorem coord_values (x : TwoShell J) (i : J) :
    x.val i=0 ∨ x.val i=1 ∨ x.val i= -1 := by
  have hx := (single_le_sum (f:=fun j => (x.val j)^2) (fun j _ => sq_nonneg _) (mem_univ i)).trans_eq x.property
  by_cases h : x.val i < -1
  · have hh : x.val i≤ -2 := by omega
    nlinarith only [hx,hh]
  by_cases h' : 1 < x.val i
  · have hh : 2≤x.val i := by omega
    nlinarith only [hx,hh]
  omega

private theorem support_two (x : TwoShell J) : (support₂ x.val).card=2 := by
  have e : (∑ j, if x.val j≠0 then (1:ℤ) else 0)=2 := by
    rw [← x.property]
    exact sum_congr rfl fun i _ => by
      rcases coord_values x i with h|h|h <;> simp [h]
  simpa [support₂] using e

/-- Synthesis from the unordered support and the signs at its two endpoints. -/
def fromPair (p : SignedPair J) : TwoShell J := by
  classical
  let x := fun j => if h : j∈p.1.val then unitSign (p.2 ⟨j,h⟩) else 0
  refine ⟨x,?_⟩
  have sq (i) : (x i)^2=if i∈p.1.val then (1:ℤ) else 0 := by
    by_cases h : i∈p.1.val <;> simp [x,h,sign_sq]
  simp only [energy,sq]
  simp [p.1.property]

private theorem support_fromPair (p : SignedPair J) : support₂ (fromPair p).val=p.1.val := by
  classical
  ext i
  by_cases h : i∈p.1.val
  · cases e : p.2 ⟨i,h⟩ <;> simp [support₂,fromPair,h,unitSign,e]
  · simp [support₂,fromPair,h]

/-- All independent signs occur, including equal signs on the support. -/
def twoShellEquiv : SignedPair J ≃ TwoShell J := by
  classical
  apply Equiv.ofBijective fromPair
  constructor
  · rintro ⟨S,f⟩ ⟨T,g⟩ h
    have e : S=T := Subtype.ext ((support_fromPair ⟨S,f⟩).symm.trans
      ((congrArg (fun x : TwoShell J => support₂ x.val) h).trans (support_fromPair ⟨T,g⟩)))
    subst T
    apply congrArg (Sigma.mk S)
    funext i
    apply unitSign_injective
    simpa only [fromPair,dif_pos i.property] using congrArg (fun x : TwoShell J => x.val i.val) h
  · intro x
    let S : Set.powersetCard J 2 := ⟨support₂ x.val,support_two x⟩
    let b := fun j : S.val => decide (x.val j.val<0)
    refine ⟨⟨S,b⟩,Subtype.ext (funext fun i => ?_)⟩
    rcases coord_values x i with e|e|e <;> simp [fromPair,S,b,support₂,unitSign,e]

instance twoShellFinite : Finite (TwoShell J) := Finite.of_equiv _ (twoShellEquiv (J:=J))

theorem card_twoShell : Nat.card (TwoShell J)=4*(Fintype.card J).choose 2 := by
  classical
  rw [← Nat.card_congr (twoShellEquiv (J:=J)),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,Set.powersetCard.card_eq]
  rw [sum_const,card_univ,← Nat.card_eq_fintype_card,Set.powersetCard.card,Nat.card_eq_fintype_card]
  simp [Nat.mul_comm]

/-- Opposite signs select exactly one ordered pair of distinct endpoints. -/
def zeroShellEquiv : (Σ a : J, {b : J // b≠a}) ≃ ZeroShell J := by
  classical
  let f (p : Σ a : J, {b : J // b≠a}) : ZeroShell J :=
    ⟨root p.1 p.2.val,sum_root _ _,by rw [energy_root,if_neg p.2.property.symm]⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    obtain ⟨e,e'⟩ := root_injective b.property.symm d.property.symm (congrArg Subtype.val h)
    subst c
    exact congrArg (Sigma.mk a) (Subtype.ext e')
  · intro x
    obtain ⟨a,b,h,e⟩ := exists_root_of_energy_two x.property.1 x.property.2
    exact ⟨⟨a,⟨b,h.symm⟩⟩,Subtype.ext e.symm⟩

theorem card_zeroShell : Nat.card (ZeroShell J)=(Fintype.card J)*(Fintype.card J-1) := by
  classical
  rw [← Nat.card_congr (zeroShellEquiv (J:=J)),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp [Fintype.card_subtype_compl]

#print axioms twoShellEquiv
#print axioms card_twoShell
#print axioms zeroShellEquiv
#print axioms card_zeroShell
end GaloisForLFunctions.HTGeometry.IntegralZeroSum
