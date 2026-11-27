import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Zeros.Expansion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Radicals.Temperature

/-! # Finiteness and local isolation of blind temperatures on a fixed packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Zeros

open Finset Real Set Metric
open GaloisForLFunctions.HTGeometry (VanishesTo IsZeroList signChanges laguerre_zeroList_length_le signChanges_add_one_le expSum)

variable {I : Type*} [Fintype I]

private theorem odd_negative (E : I → ℝ) (t : ℝ) : oddTrace E (-t) = -oddTrace E t := by
  simp only [oddTrace,oddTerm,neg_neg,← sum_neg_distrib,neg_sub]

/-- Reflection supplies both signs of each positive zero. The origin contributes three
entries because the spectrum is centered. -/
private theorem zero_list (E : I → ℝ) (mean : ∑ i, E i=0) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, 0<t ∧ oddTrace E t=0) :
    ∃ l : List ℝ, IsZeroList (oddTrace E) l ∧ l.length=2*Z.card+3 := by
  classical
  let neg := Z.image (fun t => -t)
  let T := Z ∪ neg
  have hn {r : ℝ} (h : r∈neg) : r<0 ∧ oddTrace E r=0 := by
    obtain ⟨t,ht,rfl⟩ := mem_image.mp h
    exact ⟨neg_neg_of_pos (hZ t ht).1,by rw [odd_negative,(hZ t ht).2,neg_zero]⟩
  have dis : Disjoint Z neg := Finset.disjoint_left.mpr fun _ h₁ h₂ => (hn h₂).1.not_gt (hZ _ h₁).1
  have nmem : 0∉T := fun h => (mem_union.mp h).elim (fun h₁ => (lt_irrefl _ (hZ 0 h₁).1))
    (fun h₂ => lt_irrefl _ (hn h₂).1)
  have size : T.card=2*Z.card := by
    change (Z ∪ neg).card=2*Z.card
    rw [card_union_eq_card_add_card.mpr dis,show neg.card=Z.card from card_image_of_injective _ neg_injective,two_mul]
  let M := T.val+Multiset.replicate 3 (0 : ℝ)
  let l := M.sort (· ≤ ·)
  have count (x : ℝ) : l.count x = M.count x := by
    rw [← Multiset.coe_count,show (↑l : Multiset ℝ)=M from Multiset.sort_eq _ _]
  refine ⟨l,⟨Multiset.pairwise_sort _ _,fun x => ?_⟩,?_⟩
  · rw [count]
    by_cases hx : x=0
    · subst x
      simpa only [M,Multiset.count_add,Multiset.count_eq_zero_of_notMem nmem,
        Multiset.count_replicate_self,zero_add] using triple_zero mean
    · have hcount : M.count x = T.val.count x := by simp [M,hx]
      rw [hcount]
      by_cases mem : x∈T
      · have atx : oddTrace E x=0 := (mem_union.mp mem).elim (fun h => (hZ x h).2) (fun h => (hn h).2)
        intro j hj
        have le := Multiset.nodup_iff_count_le_one.mp T.nodup x
        obtain rfl : j=0 := by omega
        rwa [iteratedDeriv_zero]
      · rw [Multiset.count_eq_zero_of_notMem mem]
        intro j hj; omega
  · change (M.sort (· ≤ ·)).length=_
    rw [Multiset.length_sort]
    simp only [M,Multiset.card_add,Multiset.card_replicate,← Finset.card_def,size]

/-- The bound counts sign changes after combining equal exponents and deleting all
cancelled levels. It applies to every distinct list of positive blind temperatures. -/
theorem sign_bound {E : I → ℝ} (mean : ∑ i, E i=0) {u : ℝ} (detected : oddTrace E u≠0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Z, 0<t ∧ oddTrace E t=0) :
    2*Z.card+3 ≤ signChanges (fun i => imbalance E (radius E i)) := by
  obtain ⟨l,hl,length⟩ := zero_list E mean Z hZ
  rw [← as_expSum] at hl
  have rule {m : ℕ} (hm : 0 < m) (c a : Fin m → ℝ) (ha : StrictMono a) (hc : ∀ i, c i≠0)
      (h : IsZeroList (expSum c a) l) : l.length ≤ signChanges c := by
    cases m with
    | zero => omega
    | succ m => exact laguerre_zeroList_length_le m c a ha hc l h
  exact length ▸ rule (active_pos detected) _ _ (ordered E) (survives E) hl

theorem size_bound {E : I → ℝ} (mean : ∑ i, E i=0) {u : ℝ} (detected : oddTrace E u≠0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Z, 0<t ∧ oddTrace E t=0) : Z.card+2 ≤ Fintype.card I := by
  have h := sign_bound mean detected Z hZ
  have c := signChanges_add_one_le (active_pos detected) (fun i => imbalance E (radius E i))
  have r := active_bound E
  omega

def blind (S : Finset Nat.Primes) := {t : ℝ | 0<t ∧ Coincides (elementary (S := S)) t}

/-- An arbitrary but fixed packet of three or more primes has finitely many positive
blind temperatures, with at most two fewer than the number of prime labels. -/
theorem fixed_packet (S : Finset Nat.Primes) (hs : 2<S.card) :
    (blind S).Finite ∧ ∀ Z : Finset ℝ, (↑Z : Set ℝ) ⊆ blind S → Z.card+2≤S.card := by
  let E := centered (labelEnergy (elementary (S := S)))
  have read (t : ℝ) : oddTrace E t=0 ↔ Coincides (elementary (S := S)) t := by
    rw [oddTrace_eq,sub_eq_zero]; exact eq_comm
  have detected : oddTrace E 1≠0 := by
    intro h
    have hit := (prime_packet_iff S 1).mp (by simpa only [Nat.cast_one] using (read 1).mp h)
    omega
  have bound (Z : Finset ℝ) (inc : (↑Z : Set ℝ) ⊆ blind S) : Z.card+2≤S.card := by
    simpa only [Fintype.card_coe] using size_bound (sum_centered _) detected Z
      (fun t ht => ⟨(inc ht).1,(read t).mpr (inc ht).2⟩)
  refine ⟨?_,bound⟩
  by_contra infinite
  obtain ⟨Z,inc,size⟩ := Set.Infinite.exists_subset_card_eq infinite S.card
  have := bound Z inc
  omega

private theorem right_gap (S : Finset Nat.Primes) (hs : 2<S.card) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t ∈ Ioo (0 : ℝ) δ, ¬Coincides (elementary (S := S)) t := by
  have zero : (0 : ℝ)∈(blind S)ᶜ := fun h => (lt_irrefl _ h.1)
  obtain ⟨δ,pos,ball⟩ := Metric.mem_nhds_iff.mp ((fixed_packet S hs).1.isClosed.isOpen_compl.mem_nhds zero)
  refine ⟨δ,pos,fun t ht eq => ball (a := t) ?_ ⟨ht.1,eq⟩⟩
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1] using ht.2

/-- On either side of the critical line, a fixed prime packet has a neighborhood
in which the single comparison detects exactly zero damping. -/
theorem fixed_gap (S : Finset Nat.Primes) (hs : 2<S.card) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, |t|<δ → (Coincides (elementary (S := S)) t ↔ t=0) := by
  obtain ⟨δ,pos,safe⟩ := right_gap S hs
  refine ⟨δ,pos,fun t ht => ?_⟩
  rcases lt_trichotomy t 0 with neg | rfl | positive
  · have no := safe (-t) ⟨neg_pos.mpr neg,by simpa only [abs_of_neg neg] using ht⟩
    exact iff_of_false (fun eq => no (by simpa only [Coincides,neg_neg] using eq.symm)) neg.ne
  · simp only [Coincides,neg_zero]
  · exact iff_of_false (safe t ⟨positive,by simpa only [abs_of_pos positive] using ht⟩) positive.ne'

#print axioms sign_bound
#print axioms size_bound
#print axioms fixed_packet
#print axioms fixed_gap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Zeros
