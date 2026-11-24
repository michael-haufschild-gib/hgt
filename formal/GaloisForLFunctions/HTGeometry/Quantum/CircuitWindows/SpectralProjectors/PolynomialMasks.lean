import GaloisForLFunctions.HTGeometry.PolynomialCircuitReplicaHilbertLaw

/-! # Boolean spectral masks in the algebraic closure of a polynomial image -/

open Finset MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralProjectors
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {k d : ℕ}

/-- Membership in the affine algebraic closure of the parametrized image:
every polynomial relation on the parameters vanishes at the specified point. -/
def inImageClosure (F : I→MvPolynomial (Fin k) ℂ) (x : I→ℂ) : Prop :=
  ∀ p : MvPolynomial I ℂ, aeval F p=0 → aeval x p=0

def mask (A : Finset I) (i : I) : ℂ := if i∈A then 1 else 0

private theorem mask_product {A B : Finset I} (hcard : A.card=B.card) :
    (∏ i∈A, mask B i)=if A=B then 1 else 0 := by
  classical
  by_cases h : A=B
  · subst B
    rw [if_pos rfl]
    exact prod_eq_one fun i hi => if_pos hi
  rw [if_neg h]
  have hsub : ¬A⊆B := fun hh => h (eq_of_subset_of_card_le hh hcard.ge)
  obtain ⟨i,hi,hb⟩ := not_subset.mp hsub
  exact prod_eq_zero hi (if_neg hb)

private theorem coordinate_product_degree (F : I→MvPolynomial (Fin k) ℂ)
    (hd : ∀ i, F i∈degreesLE ℂ (Fin k) (multilinearDegreeBound k d)) (A : Finset I) :
    (∏ i∈A, F i)∈degreesLE ℂ (Fin k) (multilinearDegreeBound k (A.card*d)) := by
  induction A using Finset.induction_on with
  | empty => simp [multilinearDegreeBound]
  | @insert i A hi ih =>
    rw [prod_insert hi,card_insert_of_notMem hi]
    change _ ≤ _
    apply degrees_mul_le.trans
    have h := add_le_add (hd i) ih
    simpa only [multilinearDegreeBound,Nat.succ_mul,add_nsmul,add_comm] using h

/-- The squarefree monomial of a mask singles it out among masks of the
same size. Consequently, even the algebraic closure of a k-parameter,
degree-d coordinate family contains at most (hd+1)^k masks of size h. -/
theorem card_masks_le (F : I→MvPolynomial (Fin k) ℂ)
    (hd : ∀ i, F i∈degreesLE ℂ (Fin k) (multilinearDegreeBound k d))
    (T : Finset (Finset I)) (h : ℕ) (hsize : ∀ A∈T, A.card=h)
    (hcap : ∀ A∈T, inImageClosure F (mask A)) : T.card≤(h*d+1)^k := by
  classical
  let W := degreesLE ℂ (Fin k) (multilinearDegreeBound k (h*d))
  let v (A : T) : W := ⟨∏ i∈A.val, F i,by
    have hm := coordinate_product_degree F hd A.val
    rwa [hsize A.val A.property] at hm⟩
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc A
    let P : MvPolynomial I ℂ := ∑ B : T, C (c B) * ∏ i∈B.val, X i
    have he : aeval F P=0 := by
      have hh := congrArg Subtype.val hc
      simpa only [P,map_sum,map_mul,map_prod,aeval_X,aeval_C,algebraMap_eq,
        Submodule.coe_sum,SetLike.val_smul,ZeroMemClass.coe_zero,v,smul_eq_C_mul] using hh
    have hz := hcap A.val A.property P he
    have hdelta (B : T) : (∏ i∈B.val, mask A.val i)=if B=A then 1 else 0 := by
      rw [mask_product ((hsize B B.property).trans (hsize A A.property).symm)]
      simp only [Subtype.val_inj]
    simpa only [P,map_sum,map_mul,map_prod,aeval_X,aeval_C,Algebra.algebraMap_self_apply,hdelta,
      mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,if_true] using hz
  let L := multilinearBoundedCoeffLinearMap k (h*d)
  letI : Module.Finite ℂ W := Module.Finite.of_injective L (multilinearBoundedCoeffLinearMap_injective k (h*d))
  have hb := hv.fintype_card_le_finrank
  rw [Fintype.card_coe] at hb
  exact hb.trans (finrank_multilinearDegreesLE_le_pow k (h*d))

#print axioms card_masks_le
end
end GaloisForLFunctions.HTGeometry.SpectralProjectors
