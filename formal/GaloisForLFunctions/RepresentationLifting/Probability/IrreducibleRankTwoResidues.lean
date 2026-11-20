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

/-- Partitioning a family of matrices by its two coefficients preserves the
whole trace–determinant fibre above each pair. -/
private theorem rankTwo_over_constant_fibres (S : Finset (K×K)) (c : ℕ)
    (hc : ∀ z ∈ S, Nat.card {A : Matrix (Fin 2) (Fin 2) K // A.trace=z.1 ∧ A.det=z.2}=c) :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // (A.trace,A.det)∈S} = S.card*c := by
  let F (z : S) := {A : Matrix (Fin 2) (Fin 2) K // A.trace=z.val.1 ∧ A.det=z.val.2}
  let e : {A : Matrix (Fin 2) (Fin 2) K // (A.trace,A.det)∈S} ≃ (z : S) × F z :=
    { toFun := fun A => ⟨⟨(A.val.trace,A.val.det),A.property⟩,⟨A.val,rfl,rfl⟩⟩
      invFun := fun ⟨z,A⟩ => ⟨A.val,by rw [A.property.1,A.property.2]; exact z.property⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨t,d⟩,ht⟩,⟨A,ha,hd⟩⟩
        change A.trace=t at ha
        change A.det=d at hd
        subst t
        subst d
        rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  have h (z : S) : Nat.card (F z)=c := hc z z.property
  simp only [h,sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id]

/-- Number of matrices with irreducible characteristic polynomial. In Haar
probability it contributes (q-1)²/(2q²) before ramified lifts are counted. -/
theorem card_irreducible_rankTwo :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // Irreducible A.charpoly} =
      (Fintype.card K).choose 2 * (Fintype.card K * (Fintype.card K-1)) := by
  simp_rw [irreducible_charpoly_iff_nonsplit K]
  rw [← card_nonsplitQuadraticPairs K]
  apply rankTwo_over_constant_fibres
  rintro ⟨t,d⟩ h
  letI : IsEmpty (traceDetRoot t d) :=
    ⟨fun x => (mem_nonsplitQuadraticPairs K t d).mp h x.val x.property⟩
  rw [card_traceDetFibre,Nat.card_of_isEmpty (α := traceDetRoot t d),add_zero,Nat.card_eq_fintype_card]

/-- Coefficients of quadratics with two distinct roots. -/
def distinctSplitPairs : Finset (K×K) :=
  univ.map ((Function.Embedding.subtype (fun s : Sym2 K => ¬s.IsDiag)).trans (quadraticCoefficients K))

theorem mem_distinctSplitPairs (t d : K) :
    (t,d)∈distinctSplitPairs K ↔ ∃ u v : K, u≠v ∧ (t,d)=(u+v,u*v) := by
  simp only [distinctSplitPairs,mem_map,mem_univ,true_and]
  constructor
  · rintro ⟨⟨s,hs⟩,he⟩
    induction s using Sym2.inductionOn with | _ u v =>
      exact ⟨u,v,fun h => hs (Sym2.mk_isDiag_iff.mpr h),he.symm⟩
  · rintro ⟨u,v,hne,he⟩
    exact ⟨⟨Sym2.mk u v,fun hh => hne (Sym2.mk_isDiag_iff.mp hh)⟩,he.symm⟩

/-- The same number of monic quadratics lie in the split-distinct and the
irreducible branches. Matrix fibres weight the two branches differently. -/
theorem card_distinctSplitPairs : (distinctSplitPairs K).card = (Fintype.card K).choose 2 := by
  rw [distinctSplitPairs,card_map,card_univ,Sym2.card_subtype_not_diag]

theorem card_split_distinct_rankTwo :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // ∃ u v : K, u≠v ∧ (A.trace,A.det)=(u+v,u*v)} =
      (Fintype.card K).choose 2 * (Fintype.card K * (Fintype.card K+1)) := by
  simp_rw [← mem_distinctSplitPairs K]
  rw [← card_distinctSplitPairs K]
  apply rankTwo_over_constant_fibres
  rintro ⟨t,d⟩ h
  obtain ⟨u,v,hne,he⟩ := (mem_distinctSplitPairs K t d).mp h
  have ht := congrArg Prod.fst he
  have hd := congrArg Prod.snd he
  change t=u+v at ht
  change d=u*v at hd
  subst t
  subst d
  simpa only [Nat.card_eq_fintype_card] using card_traceDetFibre_distinct hne

/-- Coefficients of quadratics with one repeated root. -/
def repeatedQuadraticPairs : Finset (K×K) :=
  univ.map ((⟨Sym2.diag,Sym2.diag_injective⟩ : K ↪ Sym2 K).trans (quadraticCoefficients K))

theorem mem_repeatedQuadraticPairs (t d : K) :
    (t,d)∈repeatedQuadraticPairs K ↔ ∃ u : K, (t,d)=(2*u,u^2) := by
  simp only [repeatedQuadraticPairs,mem_map,mem_univ,true_and]
  constructor
  · rintro ⟨u,hu⟩
    change (u+u,u*u)=(t,d) at hu
    exact ⟨u,by simpa only [two_mul,sq] using hu.symm⟩
  · rintro ⟨u,he⟩
    refine ⟨u,?_⟩
    change (u+u,u*u)=(t,d)
    simpa only [two_mul,sq] using he.symm

/-- Exactly q³ rank-two matrices have a repeated characteristic root,
including the scalars. This branch is insensitive to residue characteristic. -/
theorem card_repeated_rankTwo :
    Nat.card {A : Matrix (Fin 2) (Fin 2) K // ∃ u : K, (A.trace,A.det)=(2*u,u^2)} =
      (Fintype.card K)^3 := by
  have hc : (repeatedQuadraticPairs K).card=Fintype.card K := by
    rw [repeatedQuadraticPairs,card_map,card_univ]
  simp_rw [← mem_repeatedQuadraticPairs K]
  rw [show (Fintype.card K)^3=(repeatedQuadraticPairs K).card*(Fintype.card K)^2 by rw [hc]; ring]
  apply rankTwo_over_constant_fibres
  rintro ⟨t,d⟩ h
  obtain ⟨u,he⟩ := (mem_repeatedQuadraticPairs K t d).mp h
  have ht := congrArg Prod.fst he
  have hd := congrArg Prod.snd he
  change t=2*u at ht
  change d=u^2 at hd
  subst t
  subst d
  simpa only [Nat.card_eq_fintype_card] using card_traceDetFibre_repeated u

#print axioms card_split_distinct_rankTwo
#print axioms card_repeated_rankTwo
#print axioms card_nonsplitQuadraticPairs
#print axioms irreducible_charpoly_iff_nonsplit
#print axioms card_irreducible_rankTwo
end
end GaloisForLFunctions.RepresentationLifting
