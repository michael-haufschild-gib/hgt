import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

/-! Arithmetic visibility words for the literal fifth and sixth sieve moment arrays. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
set_option autoImplicit false

/-- Adding finite-order frequencies cannot introduce prime support outside their orders. -/
theorem prime_card_add_le {G : Type*} [AddCommGroup G] [Finite G] (x y : G) :
    (addOrderOf (x+y)).primeFactors.card ≤
      (addOrderOf x).primeFactors.card+(addOrderOf y).primeFactors.card := by
  have hx : addOrderOf x ≠ 0 := (addOrderOf_pos x).ne'
  have hy : addOrderOf y ≠ 0 := (addOrderOf_pos y).ne'
  have hcomm : AddCommute x y := add_comm x y
  have hd : addOrderOf (x+y) ∣ addOrderOf x*addOrderOf y :=
    hcomm.addOrderOf_add_dvd_lcm.trans (Nat.lcm_dvd_mul _ _)
  calc
    _ ≤ (addOrderOf x*addOrderOf y).primeFactors.card :=
      card_le_card (Nat.primeFactors_mono hd (mul_ne_zero hx hy))
    _ = ((addOrderOf x).primeFactors ∪ (addOrderOf y).primeFactors).card := by
      rw [Nat.primeFactors_mul hx hy]
    _ ≤ _ := card_union_le _ _

/-- Prime-factor width is subadditive under finite frequency sums. -/
theorem prime_card_sum_le {G ι : Type*} [AddCommGroup G] [Finite G] [DecidableEq ι]
    (s : Finset ι) (r : ι → G) :
    (addOrderOf (∑ i ∈ s, r i)).primeFactors.card ≤
      ∑ i ∈ s, (addOrderOf (r i)).primeFactors.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (prime_card_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- Coprime additive orders multiply across an arbitrary finite family. -/
theorem order_sum_of_pairwise_coprime {G ι : Type*} [AddCommGroup G] [DecidableEq ι]
    (s : Finset ι) (r : ι → G)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (addOrderOf (r i)).Coprime (addOrderOf (r j))) :
    addOrderOf (∑ i ∈ s, r i) = ∏ i ∈ s, addOrderOf (r i) := by
  revert hc
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hc
    have hs : addOrderOf (∑ i ∈ s, r i) = ∏ i ∈ s, addOrderOf (r i) :=
      ih (fun i hi j hj hij => hc i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    have hp : (addOrderOf (r a)).Coprime (addOrderOf (∑ i ∈ s, r i)) := by
      rw [hs]
      apply Nat.coprime_prod_right_iff.mpr
      intro i hi
      exact hc a (mem_insert_self _ _) i (mem_insert_of_mem hi)
        (fun hai => ha (by simpa only [hai] using hi))
    rw [sum_insert ha, prod_insert ha]
    have hcomm : AddCommute (r a) (∑ i ∈ s, r i) := add_comm _ _
    rw [hcomm.addOrderOf_add_eq_mul_addOrderOf_of_coprime hp, hs]

/-- Embed a short family into five slots, using zero frequencies in unused positions. -/
theorem pad_five {ι G : Type*} [Fintype ι] [AddCommMonoid G]
    (r : ι → G) (hc : Fintype.card ι ≤ 5) :
    ∃ g : Fin 5 → G, (∑ j, g j) = ∑ i, r i ∧ ∀ j, g j = 0 ∨ ∃ i, g j = r i := by
  classical
  obtain ⟨f : ι ↪ Fin 5⟩ := Function.Embedding.nonempty_of_card_le
    (α := ι) (β := Fin 5) (by simpa using hc)
  let g : Fin 5 → G := Function.extend f r (fun _ => 0)
  have hg (i : ι) : g (f i) = r i := f.injective.extend_apply r _ i
  have hz (j : Fin 5) (hj : ¬∃ i, f i = j) : g j = 0 :=
    Function.extend_apply' r (fun _ => 0) j hj
  refine ⟨g, ?_, ?_⟩
  · calc
      _ = ∑ j ∈ univ.map f, g j := by
        symm
        apply sum_subset (subset_univ _)
        intro j _ hj
        apply hz
        rintro ⟨i, rfl⟩
        exact hj (mem_map.mpr ⟨i, mem_univ i, rfl⟩)
      _ = ∑ i, g (f i) := by rw [sum_map]
      _ = _ := sum_congr rfl (fun i _ => hg i)
  · intro j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      exact Or.inr ⟨i, hg i⟩
    · exact Or.inl (hz j hj)

/-- A missing coordinate occurs linearly in an observed resonant product. -/
def Visible (N : ℕ) (S : Finset ℕ) (q : ℕ) : Prop :=
  ∃ m : ℕ, (m = 5 ∨ m = 6) ∧ ∃ r : Fin m → ZMod N.factorial,
    (∑ j, r j) = 0 ∧ ∃ i : Fin m, addOrderOf (r i) = q ∧
      ∀ j, j ≠ i → addOrderOf (r j) ∈ S

/-- Admitted order one and admitted prime powers, expressed by prime-factor width. -/
def primePowerOrders (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun q => q.primeFactors.card ≤ 1)

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Five companion frequencies of prime-power order cover at most five primes. -/
theorem width_le_five_of_visible (N q : ℕ) (hv : Visible N (primePowerOrders N) q) :
    q.primeFactors.card ≤ 5 := by
  classical
  obtain ⟨m, hm, r, hz, i, hi, hr⟩ := hv
  let s : Finset (Fin m) := univ.erase i
  have hsum : r i+(∑ j ∈ s, r j) = 0 :=
    (Finset.add_sum_erase univ r (mem_univ i)).trans hz
  have hq : q = addOrderOf (∑ j ∈ s, r j) := by
    rw [← hi, eq_neg_of_add_eq_zero_left hsum, addOrderOf_neg]
  have hcard : s.card ≤ 5 := by
    have hs : s.card = m-1 := by simp [s]
    rcases hm with rfl | rfl <;> omega
  rw [hq]
  calc
    _ ≤ ∑ j ∈ s, (addOrderOf (r j)).primeFactors.card := prime_card_sum_le s r
    _ ≤ ∑ _j ∈ s, 1 := by
      apply sum_le_sum
      intro j hj
      exact (mem_filter.mp (hr j (mem_erase.mp hj).1)).2
    _ = s.card := by simp
    _ ≤ 5 := hcard

/-- A short family with prescribed sum order yields a sixth-moment visibility word. -/
theorem visible_from_small_family (N q : ℕ) (S : Finset ℕ) (h1 : 1 ∈ S)
    {ι : Type*} [Fintype ι] (r : ι → ZMod N.factorial) (hc : Fintype.card ι ≤ 5)
    (hq : addOrderOf (∑ i, r i) = q) (hr : ∀ i, addOrderOf (r i) ∈ S) :
    Visible N S q := by
  obtain ⟨g, hsum, hg⟩ := pad_five r hc
  have hgs (j : Fin 5) : addOrderOf (g j) ∈ S := by
    rcases hg j with hz | ⟨i, hi⟩
    · simpa only [hz, addOrderOf_zero] using h1
    · simpa only [hi] using hr i
  refine ⟨6, Or.inr rfl, Fin.cons (-(∑ j, g j)) g, ?_, 0, ?_, ?_⟩
  · simp [Fin.sum_univ_succ]
  · simpa only [Fin.cons_zero, addOrderOf_neg, hsum] using hq
  · intro j hj
    refine Fin.cases (fun h => False.elim (h rfl)) (fun k _ => ?_) j hj
    simpa only [Fin.cons_succ] using hgs k

/-- Every primary factor of an admitted order is itself in the prime-power support. -/
theorem primary_order_mem (N q : ℕ) (hq : q ∈ Icc 1 N) (p : q.primeFactors) :
    (p : ℕ)^q.factorization p ∈ primePowerOrders N := by
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  have hq0 : 0 < q := (mem_Icc.mp hq).1
  have hk : 0 < q.factorization p :=
    hp.factorization_pos_of_dvd hq0.ne' (Nat.dvd_of_mem_primeFactors p.property)
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨pow_pos hp.pos _, ?_⟩, ?_⟩
  · exact (Nat.le_of_dvd hq0 (Nat.ordProj_dvd q p)).trans (mem_Icc.mp hq).2
  · simp only [Nat.primeFactors_prime_pow hk.ne' hp, card_singleton, le_refl]

/-- This support is exactly order one together with the admitted prime powers. -/
theorem mem_primePowerOrders (N q : ℕ) :
    q ∈ primePowerOrders N ↔ q ∈ Icc 1 N ∧ (q = 1 ∨ IsPrimePow q) := by
  constructor
  · intro h
    obtain ⟨hq, hw⟩ := mem_filter.mp h
    refine ⟨hq, ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hw with h0 | h1
    · left
      rcases Nat.primeFactors_eq_empty.mp (card_eq_zero.mp h0) with hz | hq1
      · have := (mem_Icc.mp hq).1
        omega
      · exact hq1
    · exact Or.inr (isPrimePow_iff_card_primeFactors_eq_one.mpr h1)
  · rintro ⟨hq, h⟩
    refine mem_filter.mpr ⟨hq, ?_⟩
    rcases h with rfl | hp
    · simp
    · rw [isPrimePow_iff_card_primeFactors_eq_one.mp hp]

/-- The admitted primary orders determine divisibility by every admitted order. -/
theorem all_orders_dvd_of_primary_orders (N h : ℕ)
    (hh : ∀ q ∈ primePowerOrders N, q ∣ h) : ∀ q ∈ Icc 1 N, q ∣ h := by
  intro q hq
  apply (Nat.dvd_iff_prime_pow_dvd_dvd h q).mpr
  intro p k hp hpk
  apply hh (p^k)
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨pow_pos hp.pos _, ?_⟩, ?_⟩
  · exact (Nat.le_of_dvd (mem_Icc.mp hq).1 hpk).trans (mem_Icc.mp hq).2
  · by_cases hk : k = 0
    · simp [hk]
    · simp [Nat.primeFactors_prime_pow hk hp]

/-- Keeping every prime-power coordinate preserves the full cutoff lcm. -/
theorem primePowerOrders_lcm (N : ℕ) :
    (primePowerOrders N).lcm id = (Icc 1 N).lcm id := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro q hq
    exact Finset.dvd_lcm (f := id) (mem_filter.mp hq).1
  · apply Finset.lcm_dvd
    exact all_orders_dvd_of_primary_orders N _
      (fun q hq => Finset.dvd_lcm (f := id) hq)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
