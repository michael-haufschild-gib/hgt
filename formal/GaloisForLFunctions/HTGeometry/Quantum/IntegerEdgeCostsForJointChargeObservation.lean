import GaloisForLFunctions.HTGeometry.Quantum.ResonancesOfTensorChargeObservations

/-!
# Integer edge costs for total-charge observations

A nonzero tensor entry is a word in the nonzero entries of the one-copy
matrix. For a Hermitian matrix, reversing an edge realizes its negative
displacement at the same cost. Thus the first copy count detecting a given
phase frequency is an exact integer minimization with two linear equations.
-/

noncomputable section
open Finset Matrix
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Edge (A : Matrix ι ι ℂ) := {e : ι × ι // A e.1 e.2 ≠ 0}

def edgeGap (f : ι → ℤ) {A : Matrix ι ι ℂ} (e : Edge A) := f e.val.1-f e.val.2

/-- A nonzero word, before imposing the charge constraint. -/
def Word (q b : ι → ℤ) (A : Matrix ι ι ℂ) (n : ℕ) (a d : ℤ) : Prop :=
  ∃ u v : Fin n → ι, (∀ k, A (u k) (v k)≠0) ∧ displacement q u v=a ∧ displacement b u v=d

theorem balanced_word (q b : ι → ℤ) (A : Matrix ι ι ℂ) (n : ℕ) (d : ℤ) :
    Word q b A n 0 d ↔ d ∈ frequencies q b A n := by
  rw [frequency_iff]
  constructor
  · rintro ⟨u,v,ha,hq,hb⟩
    refine ⟨u,v,?_,hb⟩
    rw [observe_entry,if_pos hq]
    exact prod_ne_zero_iff.mpr fun i _ => ha i
  · rintro ⟨u,v,h,hb⟩
    rw [observe_entry] at h
    split at h <;> rename_i he
    · exact ⟨u,v,fun i => (prod_ne_zero_iff.mp h) i (mem_univ i),he,hb⟩
    · exact (h rfl).elim

private theorem append_word {q b : ι → ℤ} {A : Matrix ι ι ℂ} {n m : ℕ} {a d a' d' : ℤ}
    (h : Word q b A n a d) (h' : Word q b A m a' d') :
    Word q b A (n+m) (a+a') (d+d') := by
  obtain ⟨u,v,hu,rfl,rfl⟩ := h
  obtain ⟨u',v',hu',rfl,rfl⟩ := h'
  refine ⟨Fin.addCases u u',Fin.addCases v v',?_,?_,?_⟩
  · intro k
    exact Fin.addCases (fun i => by simpa only [Fin.addCases_left] using hu i)
      (fun i => by simpa only [Fin.addCases_right] using hu' i) k
  all_goals simp only [displacement,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]

private theorem repeat_edge (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian)
    (e : Edge A) (m : ℤ) :
    Word q b A m.natAbs (m*edgeGap q e) (m*edgeGap b e) := by
  have hrev : A e.val.2 e.val.1≠0 := by
    intro he
    exact e.property (by rw [← ha.apply,he,star_zero])
  cases m with
  | ofNat j =>
    refine ⟨fun _ => e.val.1,fun _ => e.val.2,fun _ => e.property,?_,?_⟩ <;>
      simp [displacement,edgeGap,nsmul_eq_mul]
  | negSucc j =>
    refine ⟨fun _ => e.val.2,fun _ => e.val.1,fun _ => hrev,?_,?_⟩ <;>
      simp only [displacement,edgeGap,sum_const,card_univ,Fintype.card_fin,Int.natAbs_negSucc,
        nsmul_eq_mul,Int.negSucc_eq,Int.natCast_succ] <;> ring

/-- Each signed edge multiplicity can be realized with exactly its absolute
value in copies, simultaneously across both gradings. -/
theorem word_of_coefficients (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian)
    (c : Edge A → ℤ) :
    Word q b A (∑ e, (c e).natAbs) (∑ e, c e*edgeGap q e) (∑ e, c e*edgeGap b e) := by
  have h (s : Finset (Edge A)) :
      Word q b A (∑ e ∈ s, (c e).natAbs) (∑ e ∈ s, c e*edgeGap q e) (∑ e ∈ s, c e*edgeGap b e) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [sum_empty]
      exact ⟨Fin.elim0,Fin.elim0,Fin.elim0,by simp [displacement],by simp [displacement]⟩
    | insert i s hi ih =>
      simp only [sum_insert hi]
      exact append_word (repeat_edge q b ha i (c i)) ih
  exact h univ

/-- Counting the occurrences of each oriented edge realizes a word as
nonnegative coefficients whose sum is its exact length. -/
theorem coefficients_of_word {q b : ι → ℤ} {A : Matrix ι ι ℂ} {n : ℕ} {a d : ℤ}
    (h : Word q b A n a d) :
    ∃ c : Edge A → ℕ, (∑ e, c e)=n ∧ (∑ e, (c e : ℤ)*edgeGap q e)=a ∧
      (∑ e, (c e : ℤ)*edgeGap b e)=d := by
  obtain ⟨u,v,ha,rfl,rfl⟩ := h
  let E (k : Fin n) : Edge A := ⟨(u k,v k),ha k⟩
  let c (e : Edge A) := (univ.filter (fun k => E k=e)).card
  have count (f : ι → ℤ) : (∑ e, (c e : ℤ)*edgeGap f e)=displacement f u v := by
    simpa [c,E,edgeGap,displacement,nsmul_eq_mul] using
      sum_fiberwise_eq_sum_filter' univ univ E (edgeGap f)
  refine ⟨c,?_,count q,count b⟩
  simpa only [card_univ,Fintype.card_fin] using
    (card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := E) (fun k _ => mem_univ (E k))).symm

/-- A frequency occurs through N copies iff an integral relation balances
the charges, produces the frequency and has total absolute edge cost at most N. -/
theorem copy_cost_iff (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian) (N : ℕ) (d : ℤ) :
    (∃ n≤N, d∈frequencies q b A n) ↔
      ∃ c : Edge A → ℤ, (∑ e, c e*edgeGap q e)=0 ∧ (∑ e, c e*edgeGap b e)=d ∧
        (∑ e, (c e).natAbs)≤N := by
  constructor
  · rintro ⟨n,hn,hd⟩
    obtain ⟨m,hm,hq,hb⟩ := coefficients_of_word ((balanced_word q b A n d).2 hd)
    exact ⟨fun e => (m e : ℤ),hq,hb,by simpa only [Int.natAbs_natCast,hm] using hn⟩
  · rintro ⟨c,hq,hb,hN⟩
    refine ⟨_,hN,(balanced_word q b A _ d).1 ?_⟩
    simpa only [hq,hb] using word_of_coefficients q b ha c

/-- Across arbitrarily many copies all integral balanced edge relations,
and only those relations, are observed. -/
theorem some_copy_iff (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian) (d : ℤ) :
    (∃ n, d∈frequencies q b A n) ↔
      ∃ c : Edge A → ℤ, (∑ e, c e*edgeGap q e)=0 ∧ (∑ e, c e*edgeGap b e)=d := by
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨c,hq,hb,_⟩ := (copy_cost_iff q b ha n d).1 ⟨n,le_rfl,hn⟩
    exact ⟨c,hq,hb⟩
  · rintro ⟨c,hq,hb⟩
    obtain ⟨m,_,hm⟩ := (copy_cost_iff q b ha _ d).2 ⟨c,hq,hb,le_rfl⟩
    exact ⟨m,hm⟩

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.balanced_word
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.word_of_coefficients
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.coefficients_of_word
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.copy_cost_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.some_copy_iff
