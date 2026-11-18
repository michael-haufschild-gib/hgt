import GaloisForLFunctions.HTGeometry.Quantum.EdgePhasesOfAnIntegerCharge

/-!
# Finite determination of integer-charge phases

Normalize the occupied charge gaps by their gcd. When their absolute
values are at most Q, the observations through max(2,2Q−1) copies
determine every observation of a phase twist. Unequal magnitudes cost
at most 2Q−1. Equal magnitudes need only two edges.
-/

noncomputable section
open Finset Matrix
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation
open CollectiveDiophantineGeometry.Simplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bound for all copy counts, uniform in the number of states and
the second family of phase labels. -/
theorem finite_determination (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian)
    (z w : Circle) (Q : ℕ)
    (hQ : ∀ e : Edge A, (edgeGap q e / content (edgeGap q (A:=A))).natAbs≤Q) :
    (∀ n≤max 2 (2*Q-1), observe q (twist b z A) n=observe q (twist b w A) n) ↔
      ∀ n, observe q (twist b z A) n=observe q (twist b w A) n := by
  refine ⟨fun h => ?_,fun h n _ => h n⟩
  apply (all_copies_iff_gauge q b ha z w).2
  apply (finite_pair_iff (edgeGap q) (fun e : Edge A => (z/w)^(edgeGap b e)) Q hQ).1
  intro e f u v hc hk
  have hf := pair_frequency q b ha e f u v hc
  have hh := (indistinguishable_iff q b A _ z w).1 (h _ hk) _ hf
  have he : (z/w)^(u*edgeGap b e+v*edgeGap b f)=1 := by rwa [div_zpow,div_eq_one]
  simpa only [_root_.zpow_add,mul_comm u (edgeGap b e),mul_comm v (edgeGap b f),_root_.zpow_mul] using he

/-- With a nonzero diagonal entry all shorter balanced words can be
padded. One observation at the universal bound therefore suffices. -/
theorem single_observation (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian)
    (i : ι) (hi : A i i≠0) (z w : Circle) (Q : ℕ)
    (hQ : ∀ e : Edge A, (edgeGap q e / content (edgeGap q (A:=A))).natAbs≤Q) :
    let N := max 2 (2*Q-1)
    observe q (twist b z A) N=observe q (twist b w A) N ↔
      ∀ n, observe q (twist b z A) n=observe q (twist b w A) n := by
  intro N
  constructor
  · intro h
    apply (finite_determination q b ha z w Q hQ).1
    have hm : Monotone (frequencies q b A) :=
      monotone_nat_of_le_succ fun k => frequencies_mono q b A i hi k
    intro n hn
    apply (indistinguishable_iff q b A n z w).2
    exact fun d hd => (indistinguishable_iff q b A N z w).1 h d (hm hn hd)
  · exact fun h => h N

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.finite_determination
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.single_observation
