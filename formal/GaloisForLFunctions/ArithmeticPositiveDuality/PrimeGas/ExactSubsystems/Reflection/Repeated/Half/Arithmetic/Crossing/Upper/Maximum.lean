import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Upper.Reflection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Schedule.Alternation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Zeros.Bound

/-! # Exact maximum number of irrational blind temperatures for distinct primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper

open Finset Real Set

private theorem ordered_bound {n : ℕ} (S : Finset Nat.Primes) (size : S.card=n+1) (hs : 2 < S.card)
    (Z : Finset ℝ) (sub : (↑Z : Set ℝ) ⊆ Zeros.blind S) : Z.card+1 ≤ n/2 := by
  letI : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective
  let e := S.orderIsoOfFin size
  let E := centered (labelEnergy (elementary (S := S)))
  let A (i : Fin (n+1)) := E (e i)
  have mono : StrictMono A := by
    intro i j lt
    change log (((e i).val.val : ℕ) : ℝ)-_ < log (((e j).val.val : ℕ) : ℝ)-_
    apply sub_lt_sub_right
    apply Real.log_lt_log (Nat.cast_pos.mpr (e i).val.property.pos)
    exact Nat.cast_lt.mpr (show (e i).val.val < (e j).val.val from e.strictMono lt)
  have mean : (∑ i, A i)=0 := (e.toEquiv.sum_comp E).trans (sum_centered _)
  have read (t : ℝ) : oddTrace A t=0 ↔ Coincides (elementary (S := S)) t := by
    have h : oddTrace A t=oddTrace E t := e.toEquiv.sum_comp (fun i => oddTerm t (E i))
    rw [h,oddTrace_eq,sub_eq_zero]
    exact eq_comm
  have known : oddTrace A 1 ≠ 0 := by
    intro hz
    have h := (prime_packet_iff S 1).mp (by simpa only [Nat.cast_one] using (read 1).mp hz)
    omega
  exact reflected_bound A mono mean known Z (fun t ht => ⟨(sub ht).1,(read t).mpr (sub ht).2⟩)

/-- Exact count criterion, with arbitrary lower bound on prime labels and arbitrary
upper bound on the positive damping where all designated coincidences occur. -/
theorem attainable_iff (n q M : ℕ) (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (∃ (S : Finset Nat.Primes) (Z : Finset ℝ), S.card=n ∧ (∀ p ∈ S, M < p.val) ∧ Z.card=q ∧
      ∀ z ∈ Z, z∈Ioo (0 : ℝ) ε ∧ Irrational z ∧ Coincides (elementary (S := S)) z) ↔
    2*q+3 ≤ n := by
  refine ⟨?_,fun h => Schedule.many_crossings n q M h hε⟩
  rintro ⟨S,Z,size,_,count,zeros⟩
  cases n with
  | zero => omega
  | succ m =>
    have bound := ordered_bound S size (by omega) Z (fun z hz => ⟨(zeros z hz).1.1,(zeros z hz).2.2⟩)
    omega

/-- Every fixed elementary packet satisfies the same upper bound, including all
its positive blind temperatures regardless of their size. -/
theorem packet_bound (S : Finset Nat.Primes) (hs : 2 < S.card) (Z : Finset ℝ)
    (sub : (↑Z : Set ℝ) ⊆ Zeros.blind S) : 2*Z.card+3 ≤ S.card := by
  cases h : S.card with
  | zero => omega
  | succ n =>
    have bound := ordered_bound S h hs Z sub
    omega

/-- At nonzero damping, any distinct positive probe orders that all give coincidences
consume the same cardinal bound. The bound is independent of the choice of orders. -/
theorem simultaneous_orders (S : Finset Nat.Primes) (hs : 2 < S.card) (T : Finset ℝ) (d : ℝ)
    (positive : ∀ t ∈ T, 0 < t) (pass : ∀ t ∈ T, Coincides (elementary (S := S)) (t*d)) :
    d=0 ∨ 2*T.card+3 ≤ S.card := by
  classical
  by_cases zero : d=0
  · exact Or.inl zero
  · let f (t : ℝ) := t*|d|
    have pos := abs_pos.mpr zero
    have inj : Function.Injective f := fun _ _ eq => mul_right_cancel₀ pos.ne' eq
    have tested : (↑(T.image f) : Set ℝ) ⊆ Zeros.blind S := by
      intro w hw
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hw
      refine ⟨mul_pos (positive t ht) pos,?_⟩
      rcases lt_or_gt_of_ne zero with neg | greater
      · simpa only [f,abs_of_neg neg,mul_neg,Coincides,neg_neg] using (pass t ht).symm
      · simpa only [f,abs_of_pos greater] using pass t ht
    exact Or.inr (by simpa only [card_image_of_injective _ inj] using packet_bound S hs (T.image f) tested)

#print axioms simultaneous_orders
#print axioms attainable_iff
#print axioms packet_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper
