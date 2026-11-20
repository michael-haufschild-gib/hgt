import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeListsInsideAHalfOrderObservation
import Mathlib.NumberTheory.PrimeCounting

/-!
# Exact fibers of the integer prime midpoint

Equal prices determine equal signed prime lists. Bertrand's theorem puts
two centers with equal nonzero price within one octave. No prime can then
cross all three moving endpoints. Equality of the two lists forces every
cutoff to be unchanged. Thus a price never returns after it has changed.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Total number of prime crossings at the three endpoints, counted
with multiplicity when several endpoints cross at the same step. -/
def primeMidpointClock (n : ℕ) : ℕ :=
  Nat.primeCounting (2*n)+Nat.primeCounting (3*n)+Nat.primeCounting (4*n)

theorem monotone_prime_midpoint_clock : Monotone primeMidpointClock := by
  intro n m h
  have hp (k : ℕ) := Nat.monotone_primeCounting (Nat.mul_le_mul_left k h)
  exact Nat.add_le_add (Nat.add_le_add (hp 2) (hp 3)) (hp 4)

private theorem mem_window {a b : ℕ} {p : Nat.Primes} :
    p ∈ primeWindow a b ↔ a < (p:ℕ) ∧ (p:ℕ) ≤ b := mem_subtype.trans mem_Ioc

private theorem window_membership {a b c d : ℕ} (h : primeWindow a b = primeWindow c d) (p : Nat.Primes) :
    (a < (p:ℕ) ∧ (p:ℕ) ≤ b) ↔ c < (p:ℕ) ∧ (p:ℕ) ≤ d := by
  exact mem_window.symm.trans ((Finset.ext_iff.mp h p).trans mem_window)

private theorem equal_cutoffs_of_equal_midpoints {n m : ℕ} (hnm : n ≤ m)
    (h : primeMidpointPrice n=primeMidpointPrice m) :
    ∀ k : ℕ, 2≤k → k≤4 → ∀ p : Nat.Primes, (p:ℕ)≤k*n ↔ (p:ℕ)≤k*m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · by_cases hm : m=0
    · subst m
      exact fun _ _ _ _ => Iff.rfl
    · have hz := (separated_half_order_readings (Nat.pos_of_ne_zero hm) (m:=2*m) le_rfl).1
      rw [halfOrderMidpointRead_price,←h] at hz
      exact (hz (by simp [primeMidpointPrice])).elim
  have hsep : m<2*n := by
    by_contra! hfar
    exact (separated_half_order_readings hn hfar).2 (by simpa only [halfOrderMidpointRead_price] using h)
  obtain ⟨hL,hU⟩ := (equal_prime_midpoints_iff_lists n m).mp h
  intro k hk hl p
  have h₂ := window_membership hL p
  have h₃ := window_membership hU p
  rcases (by omega : k=2 ∨ k=3 ∨ k=4) with rfl | rfl | rfl <;> omega

private theorem equal_price_of_equal_cutoffs {n m : ℕ}
    (h : ∀ k : ℕ, 2≤k → k≤4 → ∀ p : Nat.Primes, (p:ℕ)≤k*n ↔ (p:ℕ)≤k*m) :
    primeMidpointPrice n=primeMidpointPrice m := by
  apply (equal_prime_midpoints_iff_lists n m).mpr
  have same (a b : ℕ) (ha : 2≤a) (ha' : a≤4) (hb : 2≤b) (hb' : b≤4) :
      primeWindow (a*n) (b*n)=primeWindow (a*m) (b*m) := by
    ext p
    simp only [mem_window,←Nat.not_le]
    exact and_congr (not_congr (h a ha ha' p)) (h b hb hb' p)
  exact ⟨same 2 3 le_rfl (by decide) (by decide) (by decide),same 3 4 (by decide) (by decide) (by decide) le_rfl⟩

/-- Equality of two observations is equivalent to simultaneous equality
of the three prime cutoffs, including nonconsecutive and zero centers. -/
theorem prime_midpoint_has_the_same_cutoffs (n m : ℕ) :
    primeMidpointPrice n=primeMidpointPrice m ↔
      ∀ k : ℕ, 2≤k → k≤4 → ∀ p : Nat.Primes, (p:ℕ)≤k*n ↔ (p:ℕ)≤k*m := by
  refine ⟨fun h => ?_,equal_price_of_equal_cutoffs⟩
  rcases le_total n m with hm | hm
  · exact equal_cutoffs_of_equal_midpoints hm h
  · exact fun k hk hl p => (equal_cutoffs_of_equal_midpoints hm h.symm k hk hl p).symm

private theorem prime_count_equality {a b : ℕ} (hab : a≤b) :
    Nat.primeCounting a=Nat.primeCounting b ↔ ∀ p : Nat.Primes, (p:ℕ)≤a ↔ (p:ℕ)≤b := by
  rw [←Nat.primesLE_card_eq_primeCounting,←Nat.primesLE_card_eq_primeCounting]
  constructor
  · intro h
    have he := eq_of_subset_of_card_le (Nat.primesLE_mono hab) h.ge
    intro p
    simpa only [Nat.mem_primesLE,p.property,and_true] using (Finset.ext_iff.mp he (p:ℕ))
  · intro h
    apply congrArg Finset.card
    ext p
    simp only [Nat.mem_primesLE]
    by_cases hp : p.Prime
    · simpa only [hp,and_true] using h ⟨p,hp⟩
    · simp [hp]

private theorem ordered_midpoint_clock {n m : ℕ} (h : n ≤ m) :
    primeMidpointClock n=primeMidpointClock m ↔ primeMidpointPrice n=primeMidpointPrice m := by
  rw [prime_midpoint_has_the_same_cutoffs]
  have hp (k : ℕ) := Nat.monotone_primeCounting (Nat.mul_le_mul_left k h)
  have he (k : ℕ) := prime_count_equality (Nat.mul_le_mul_left k h)
  constructor
  · intro hsum k hk hl
    apply (he k).mp
    dsimp only [primeMidpointClock] at hsum
    have h₂ := hp 2
    have h₃ := hp 3
    have h₄ := hp 4
    rcases (by omega : k=2 ∨ k=3 ∨ k=4) with rfl | rfl | rfl <;> omega
  · intro hf
    unfold primeMidpointClock
    rw [(he 2).mpr (hf 2 le_rfl (by decide)),(he 3).mpr (hf 3 (by decide) (by decide)),
      (he 4).mpr (hf 4 (by decide) le_rfl)]

/-- A single monotone integer observable has exactly the same fibers as
the oscillating signed prime price. -/
theorem prime_midpoint_equivalence_of_clock (n m : ℕ) :
    primeMidpointPrice n=primeMidpointPrice m ↔ primeMidpointClock n=primeMidpointClock m := by
  rcases le_total n m with hm | hm
  · exact (ordered_midpoint_clock hm).symm
  · exact ⟨fun h => ((ordered_midpoint_clock hm).mpr h.symm).symm,
      fun h => ((ordered_midpoint_clock hm).mp h.symm).symm⟩

/-- No price can recur after a different observation intervenes. -/
theorem intervening_midpoints_are_equal {n j m : ℕ} (hnj : n≤j) (hjm : j ≤ m)
    (he : primeMidpointPrice n=primeMidpointPrice m) : primeMidpointPrice n=primeMidpointPrice j := by
  have hnm := (prime_midpoint_equivalence_of_clock n m).mp he
  apply (prime_midpoint_equivalence_of_clock n j).mpr
  exact le_antisymm (monotone_prime_midpoint_clock hnj) ((monotone_prime_midpoint_clock hjm).trans_eq hnm.symm)

/-- Distinct readings are counted by the initial value and the occupied
crossing times. A simultaneous crossing contributes a single new reading. -/
theorem number_of_distinct_midpoint_readings (N : ℕ) :
    ((range (N+1)).image primeMidpointPrice).card=
      1+((range N).filter fun n => primeMidpointClock n<primeMidpointClock (n+1)).card := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    have hold : primeMidpointPrice (N+1) ∈ (range (N+1)).image primeMidpointPrice ↔
        primeMidpointClock N=primeMidpointClock (N+1) := by
      constructor
      · rintro h
        obtain ⟨r,hr,he⟩ := mem_image.mp h
        have hrN : r≤N := Nat.lt_succ_iff.mp (mem_range.mp hr)
        have hh := intervening_midpoints_are_equal hrN (Nat.le_succ N) he
        exact (prime_midpoint_equivalence_of_clock _ _).mp (hh.symm.trans he)
      · intro h
        exact mem_image.mpr ⟨N,mem_range.mpr (Nat.lt_succ_self _),(prime_midpoint_equivalence_of_clock _ _).mpr h⟩
    have hm := monotone_prime_midpoint_clock (Nat.le_succ N)
    rw [range_add_one (n := N+1),image_insert]
    conv_rhs => rw [range_add_one (n := N),filter_insert]
    by_cases he : primeMidpointClock N=primeMidpointClock (N+1)
    · rw [if_neg (not_lt.mpr he.ge),insert_eq_of_mem (hold.mpr he),ih]
    · rw [if_pos (lt_of_le_of_ne hm he),card_insert_of_notMem (fun h => he (hold.mp h)),
        card_insert_of_notMem (fun h => (Nat.lt_irrefl N) (mem_range.mp (mem_filter.mp h).1)),ih] <;> omega

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
