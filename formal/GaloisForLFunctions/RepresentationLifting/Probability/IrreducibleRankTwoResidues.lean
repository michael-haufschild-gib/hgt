import GaloisForLFunctions.RepresentationLifting.Probability.QuadraticMatrixFibres
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Sym.Card

/-!
# Elliptic residues in rank two

A split monic quadratic corresponds to its unordered pair of roots,
including repetitions. The trace–determinant count supplies the matrix
weight of each remaining quadratic. This is the irreducible-reduction
part of the elliptic density in Lapid and Shusterman, Proposition C.2.
-/

open Finset Polynomial Matrix
namespace GaloisForLFunctions.RepresentationLifting
noncomputable section
open scoped Classical

/-- The two elementary symmetric functions determine an unordered pair
over every field, including characteristic two. -/
def quadraticCoefficients (K : Type*) [Field K] : Sym2 K ↪ K × K where
  toFun := Sym2.lift ⟨fun x y => (x+y,x*y),fun x y => Prod.ext (add_comm _ _) (mul_comm _ _)⟩
  inj' := by
    intro s t
    induction s using Sym2.inductionOn with | _ x y =>
      induction t using Sym2.inductionOn with | _ a b =>
        intro h
        have hsum : x+y=a+b := congrArg Prod.fst h
        have hprod : x*y=a*b := congrArg Prod.snd h
        have hz : (x-a)*(x-b)=0 := by linear_combination x*hsum-hprod
        rcases mul_eq_zero.mp hz with h₁|h₂
        · exact Sym2.eq_iff.mpr (Or.inl ⟨sub_eq_zero.mp h₁,by linear_combination hsum-h₁⟩)
        · exact Sym2.eq_iff.mpr (Or.inr ⟨sub_eq_zero.mp h₂,by linear_combination hsum-h₂⟩)

variable (K : Type*) [Field K] [Fintype K]

/-- Coefficient pairs omitted by the unordered-pair map. -/
def nonsplitQuadraticPairs : Finset (K × K) := univ \ univ.map (quadraticCoefficients K)

theorem mem_nonsplitQuadraticPairs (t d : K) :
    (t,d) ∈ nonsplitQuadraticPairs K ↔ ∀ x : K, x*(t-x) ≠ d := by
  simp only [nonsplitQuadraticPairs,mem_sdiff,mem_univ,true_and,mem_map]
  constructor
  · intro h x hx
    apply h
    refine ⟨Sym2.mk x (t-x),Prod.ext ?_ hx⟩
    change x+(t-x)=t
    abel
  · rintro h ⟨s,he⟩
    induction s using Sym2.inductionOn with | _ x y =>
      have hsum : x+y=t := congrArg Prod.fst he
      have hprod : x*y=d := congrArg Prod.snd he
      exact h x (by linear_combination hprod-x*hsum)

private theorem square_triangles (q : ℕ) : q.choose 2 + (q+1).choose 2 = q^2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h₁ := Nat.choose_succ_succ q 1
    have h₂ := Nat.choose_succ_succ (q+1) 1
    simp only [Nat.choose_one_right,Nat.succ_eq_add_one] at h₁ h₂
    nlinarith only [ih,h₁,h₂]

/-- Exactly q choose 2 monic quadratics have no root in a q-element field. -/
theorem card_nonsplitQuadraticPairs :
    (nonsplitQuadraticPairs K).card = (Fintype.card K).choose 2 := by
  rw [nonsplitQuadraticPairs,card_sdiff_of_subset (subset_univ _),card_map,
    card_univ,card_univ,Fintype.card_prod,Sym2.card]
  have h := square_triangles (Fintype.card K)
  rw [sq] at h
  omega

theorem irreducible_charpoly_iff_nonsplit (A : Matrix (Fin 2) (Fin 2) K) :
    Irreducible A.charpoly ↔ (A.trace,A.det) ∈ nonsplitQuadraticPairs K := by
  have hd : A.charpoly.natDegree=2 := by simp [charpoly_natDegree_eq_dim]
  rw [A.charpoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem,mem_nonsplitQuadraticPairs]
  refine forall_congr' fun x => not_congr ?_
  rw [mem_roots A.charpoly_monic.ne_zero,Polynomial.IsRoot,Matrix.charpoly_fin_two]
  simp only [eval_add,eval_sub,eval_pow,eval_X,eval_mul,eval_C]
  constructor <;> intro h <;> linear_combination -h

/-- Number of matrices with irreducible characteristic polynomial. In Haar
probability it contributes (q-1)²/(2q²) before ramified lifts are counted. -/
theorem card_irreducible_rankTwo :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // Irreducible A.charpoly} =
      (Fintype.card K).choose 2 * (Fintype.card K * (Fintype.card K-1)) := by
  let U := nonsplitQuadraticPairs K
  let F (t : U) := {A : Matrix (Fin 2) (Fin 2) K // A.trace=t.val.1 ∧ A.det=t.val.2}
  let e : {A : Matrix (Fin 2) (Fin 2) K // Irreducible A.charpoly} ≃ (t : U) × F t :=
    { toFun := fun A => ⟨⟨(A.val.trace,A.val.det),(irreducible_charpoly_iff_nonsplit K A.val).mp A.property⟩,
          ⟨A.val,rfl,rfl⟩⟩
      invFun := fun ⟨t,A⟩ => ⟨A.val,(irreducible_charpoly_iff_nonsplit K A.val).mpr
          (by rw [A.property.1,A.property.2]; exact t.property)⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨t,d⟩,ht⟩,⟨A,ha,hd⟩⟩
        subst t
        subst d
        rfl }
  have hcard (t : U) : Fintype.card (F t) = Fintype.card K * (Fintype.card K-1) := by
    letI : IsEmpty (traceDetRoot t.val.1 t.val.2) :=
      ⟨fun x => (mem_nonsplitQuadraticPairs K ..).mp t.property x.val x.property⟩
    rw [← Nat.card_eq_fintype_card]
    change Nat.card {A : Matrix (Fin 2) (Fin 2) K // A.trace=t.val.1 ∧ A.det=t.val.2} = _
    rw [card_traceDetFibre,Nat.card_of_isEmpty,add_zero,Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card,Fintype.card_congr e,Fintype.card_sigma]
  simp only [hcard,sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,U,card_nonsplitQuadraticPairs]

#print axioms card_nonsplitQuadraticPairs
#print axioms irreducible_charpoly_iff_nonsplit
#print axioms card_irreducible_rankTwo
end
end GaloisForLFunctions.RepresentationLifting
