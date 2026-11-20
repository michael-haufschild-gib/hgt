import GaloisForLFunctions.RepresentationLifting.Probability.IrreducibleRankTwoResidues
import Mathlib.Data.Nat.Choose.Cast

/-!
# Replica counts of the trace and determinant

The spectral label of a rank-two matrix is its characteristic polynomial.
Its collision moments are power sums of its fibre sizes. Counting each of
the three quadratic branches separately gives every replica count and the
exact excess over the uniform collision probability.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset Matrix
noncomputable section
open scoped Classical
variable (K : Type*) [Field K] [Fintype K]

abbrev RankTwoSpectralFibre (z : K×K) := {A : Matrix (Fin 2) (Fin 2) K // A.trace=z.1 ∧ A.det=z.2}

/-- A collection of matrices, all with the trace and determinant of its
first member. There is at least one matrix, so its label is determined. -/
abbrev SpectralReplicas (n : ℕ) :=
  {f : Fin (n+1) → Matrix (Fin 2) (Fin 2) K //
    ∀ i, ((f i).trace,(f i).det)=((f 0).trace,(f 0).det)}

private def replicaEquiv (n : ℕ) :
    SpectralReplicas K n ≃ (z : K×K) × (Fin (n+1) → RankTwoSpectralFibre K z) := by
  let label (f : SpectralReplicas K n) := ((f.val 0).trace,(f.val 0).det)
  refine (Equiv.sigmaFiberEquiv label).symm.trans (Equiv.sigmaCongrRight fun z => ?_)
  refine { toFun := fun f i => ⟨f.val.val i,congrArg Prod.fst ((f.val.property i).trans f.property),
             congrArg Prod.snd ((f.val.property i).trans f.property)⟩
           invFun := fun f => ⟨⟨fun i => (f i).val,fun i =>
             Prod.ext ((f i).property.1.trans (f 0).property.1.symm)
               ((f i).property.2.trans (f 0).property.2.symm)⟩,Prod.ext (f 0).property.1 (f 0).property.2⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl }

/-- Ordered or repeated roots exhaust the split quadratics, in every
characteristic. Their trace–determinant branches are disjoint. -/
private theorem split_label_partition :
    (univ : Finset (Sym2 K)).map (quadraticCoefficients K) =
      distinctSplitPairs K ∪ repeatedQuadraticPairs K ∧
      Disjoint (distinctSplitPairs K) (repeatedQuadraticPairs K) := by
  constructor
  · ext z
    rw [mem_union]
    rcases z with ⟨t,d⟩
    rw [mem_distinctSplitPairs,mem_repeatedQuadraticPairs]
    simp only [mem_map,mem_univ,true_and]
    constructor
    · rintro ⟨s,he⟩
      induction s using Sym2.inductionOn with | _ u v =>
        by_cases h : u=v
        · subst v
          exact Or.inr ⟨u,by simpa only [two_mul,sq] using he.symm⟩
        · exact Or.inl ⟨u,v,h,he.symm⟩
    · rintro (⟨u,v,_,he⟩|⟨u,he⟩)
      · exact ⟨Sym2.mk u v,he.symm⟩
      · refine ⟨Sym2.mk u u,?_⟩
        change (u+u,u*u)=(t,d)
        simpa only [two_mul,sq] using he.symm
  · apply disjoint_left.mpr
    rintro ⟨t,d⟩ hx hy
    obtain ⟨u,v,hne,h₁⟩ := (mem_distinctSplitPairs K t d).mp hx
    obtain ⟨w,h₂⟩ := (mem_repeatedQuadraticPairs K t d).mp hy
    have hpair : quadraticCoefficients K (Sym2.mk u v)=quadraticCoefficients K (Sym2.mk w w) := by
      change (u+v,u*v)=(w+w,w*w)
      simpa only [two_mul,sq] using h₁.symm.trans h₂
    rcases Sym2.eq_iff.mp ((quadraticCoefficients K).injective hpair) with h|h <;>
      exact hne (h.1.trans h.2.symm)

/-- Every spectral power sum, including all positive integral replica
moments, with the finite-field matrix weight of each branch. -/
theorem rankTwo_spectral_power_sum (m : ℕ) :
    ∑ z : K×K, (Nat.card (RankTwoSpectralFibre K z))^m =
      (Fintype.card K).choose 2*(Fintype.card K*(Fintype.card K-1))^m +
      ((Fintype.card K).choose 2*(Fintype.card K*(Fintype.card K+1))^m +
        Fintype.card K*((Fintype.card K)^2)^m) := by
  let P := univ.map (quadraticCoefficients K)
  let N := nonsplitQuadraticPairs K
  let D := distinctSplitPairs K
  let R := repeatedQuadraticPairs K
  let q := Fintype.card K
  let a (z : K×K) := (Nat.card (RankTwoSpectralFibre K z))^m
  obtain ⟨hP,hdis⟩ := split_label_partition K
  have cover : N ∪ P = univ := sdiff_union_of_subset (subset_univ P)
  have nd : Disjoint N P := disjoint_left.mpr fun _ h => (mem_sdiff.mp h).2
  have hn (z : K×K) (hz : z∈N) : a z=(q*(q-1))^m := by
    rcases z with ⟨t,d⟩
    letI : IsEmpty (traceDetRoot t d) := ⟨fun x =>
      (mem_nonsplitQuadraticPairs K t d).mp hz x.val x.property⟩
    simp only [a,RankTwoSpectralFibre,card_traceDetFibre,Nat.card_of_isEmpty (α:=traceDetRoot t d),
      Nat.add_zero,Nat.card_eq_fintype_card,q]
  have hd (z : K×K) (hz : z∈D) : a z=(q*(q+1))^m := by
    obtain ⟨u,v,hne,he⟩ := (mem_distinctSplitPairs K z.1 z.2).mp hz
    change z=(u+v,u*v) at he
    subst z
    simp only [a,RankTwoSpectralFibre,card_traceDetFibre_distinct hne,Nat.card_eq_fintype_card,q]
  have hr (z : K×K) (hz : z∈R) : a z=(q^2)^m := by
    obtain ⟨u,he⟩ := (mem_repeatedQuadraticPairs K z.1 z.2).mp hz
    change z=(2*u,u^2) at he
    subst z
    simp only [a,RankTwoSpectralFibre,card_traceDetFibre_repeated,Nat.card_eq_fintype_card,q]
  have hc : R.card=q := by rw [show R=repeatedQuadraticPairs K from rfl,repeatedQuadraticPairs,card_map,card_univ]
  change ∑ z ∈ univ, a z = _
  rw [← cover,sum_union nd,show P=D∪R from hP,sum_union hdis,sum_congr rfl hn,sum_congr rfl hd,sum_congr rfl hr]
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,N,D,card_nonsplitQuadraticPairs,card_distinctSplitPairs,hc,q]

/-- Number of independently chosen matrix replicas with a common spectral
label. The first member determines the common label. -/
theorem card_rankTwo_spectral_replicas (n : ℕ) :
    Nat.card (SpectralReplicas K n) =
      (Fintype.card K).choose 2*(Fintype.card K*(Fintype.card K-1))^(n+1) +
      ((Fintype.card K).choose 2*(Fintype.card K*(Fintype.card K+1))^(n+1) +
        Fintype.card K*((Fintype.card K)^2)^(n+1)) := by
  rw [Nat.card_congr (replicaEquiv K n),Nat.card_sigma]
  simp only [Nat.card_fun,Nat.card_fin]
  exact rankTwo_spectral_power_sum K (n+1)

/-- Collision probability of two independent uniform rank-two matrices.
The excess over the uniform coefficient collision rate is (q−1)/q⁵. -/
theorem rankTwo_pair_collision_probability :
    (Nat.card (SpectralReplicas K 1) : ℝ)/(Fintype.card K:ℝ)^8 =
      1/(Fintype.card K:ℝ)^2 + ((Fintype.card K:ℝ)-1)/(Fintype.card K:ℝ)^5 := by
  have hq : 1≤Fintype.card K := Fintype.card_pos
  have hn : (Fintype.card K:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  rw [card_rankTwo_spectral_replicas]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hq,Nat.cast_one,Nat.cast_choose_two]
  field_simp [hn] <;> ring

#print axioms rankTwo_pair_collision_probability
#print axioms rankTwo_spectral_power_sum
#print axioms card_rankTwo_spectral_replicas
end
end GaloisForLFunctions.RepresentationLifting
