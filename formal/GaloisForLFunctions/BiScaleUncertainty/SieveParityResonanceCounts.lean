import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgeResonance
import GaloisForLFunctions.BiScaleUncertainty.SieveHalfPeriodTranslation

/-! Multiplicity obstructions for parity-neighborhood resonances. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false
variable {ι G : Type*} [Fintype ι] [AddCommGroup G]

def orderCount (r : ι → G) (q : ℕ) : ℕ := (univ.filter fun i => addOrderOf (r i) = q).card

theorem orderCount_eq_zero_iff (r : ι → G) (q : ℕ) :
    orderCount r q = 0 ↔ ∀ i, addOrderOf (r i) ≠ q := by
  classical
  constructor
  · intro hc i hi
    have hp : 0 < orderCount r q := Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    omega
  · intro h
    have he : (univ.filter fun i => addOrderOf (r i) = q) = (∅ : Finset ι) := by
      ext i
      simp [h i]
    simp only [orderCount, he, card_empty]

theorem orderCount_eq_one_witness (r : ι → G) (q : ℕ) (hc : orderCount r q = 1) :
    ∃ j, addOrderOf (r j) = q ∧ ∀ i, i ≠ j → addOrderOf (r i) ≠ q := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  have hjm : j ∈ (univ.filter fun i => addOrderOf (r i) = q) := by rw [hj]; simp
  refine ⟨j, (mem_filter.mp hjm).2, ?_⟩
  intro i hij hi
  have him : i ∈ (univ.filter fun i => addOrderOf (r i) = q) := by simp [hi]
  rw [hj] at him
  exact hij (mem_singleton.mp him)

/-- A prime factor confined to one order forbids that order appearing exactly once. -/
theorem orderCount_ne_one_of_coprime (r : ι → G) (hz : (∑ i, r i) = 0)
    (q p : ℕ) (hp : 1 < p) (hpq : p ∣ q)
    (hcoprime : ∀ i, addOrderOf (r i) ≠ q → Nat.Coprime p (addOrderOf (r i))) :
    orderCount r q ≠ 1 := by
  classical
  intro hc
  obtain ⟨j, hj, hrest⟩ := orderCount_eq_one_witness r q hc
  exact no_exclusive_coprime_block r hz j p hp (by rwa [hj])
    (fun i hi => hcoprime i (hrest i hi))

private theorem singleton_order_dvd (r : ι → G) (hz : (∑ i, r i) = 0) (j : ι) (B : ℕ)
    (hj : ∀ i, i ≠ j → addOrderOf (r i) ∣ B) : addOrderOf (r j) ∣ B := by
  classical
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
  have ht : (∑ i, B • r i) = B • r j := by
    apply Finset.sum_eq_single j
    · intro i _ hi
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hj i hi)
    · simp
  rw [← Finset.smul_sum, hz, smul_zero] at ht
  exact ht.symm

theorem orderCount_ne_one_of_annihilator (r : ι → G) (hz : (∑ i, r i) = 0)
    (q B : ℕ) (hq : ¬q ∣ B)
    (hrest : ∀ i, addOrderOf (r i) ≠ q → addOrderOf (r i) ∣ B) :
    orderCount r q ≠ 1 := by
  intro hc
  obtain ⟨j, hj, hother⟩ := orderCount_eq_one_witness r q hc
  have hh := singleton_order_dvd r hz j B (fun i hi => hrest i (hother i hi))
  rw [hj] at hh
  exact hq hh

variable {P : ℕ} [NeZero P]

private theorem phase_eq_one_iff (x : ZMod P) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    exact ZMod.injective_stdAddChar (by simpa using hx)
  · rintro rfl
    simp

theorem halfperiod_phase (r : ZMod P) (h : ℕ) (h2 : addOrderOf r ∣ 2*h) :
    ZMod.stdAddChar ((h : ZMod P)*r) = if addOrderOf r ∣ h then 1 else -1 := by
  classical
  have hr (t : ℕ) : (t : ZMod P)*r = 0 ↔ addOrderOf r ∣ t := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    simp only [nsmul_eq_mul]
  by_cases hh : addOrderOf r ∣ h
  · rw [if_pos hh, (hr h).mpr hh]
    simp
  · rw [if_neg hh]
    have he : (h : ZMod P)*r+(h : ZMod P)*r = ((2*h : ℕ) : ZMod P)*r := by
      push_cast
      ring
    have hs : ZMod.stdAddChar ((h : ZMod P)*r)*ZMod.stdAddChar ((h : ZMod P)*r) = 1 := by
      rw [← AddChar.map_add_eq_mul, he, (hr (2*h)).mpr h2]
      simp
    have hn : ZMod.stdAddChar ((h : ZMod P)*r) ≠ 1 :=
      fun hx => hh ((hr h).mp ((phase_eq_one_iff _).mp hx))
    exact (mul_self_eq_one_iff.mp hs).resolve_left hn

private theorem prod_phase {κ : Type*} (r : κ → ZMod P) (h : ℕ) (s : Finset κ) :
    (∏ i ∈ s, ZMod.stdAddChar ((h : ZMod P)*r i)) =
      ZMod.stdAddChar ((h : ZMod P)*∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_add, AddChar.map_add_eq_mul, ih]

/-- A zero-sum tuple contains an even number of modes reversed by any common half-period. -/
theorem even_halfperiod_count (r : ι → ZMod P) (hz : (∑ i, r i) = 0) (h : ℕ)
    (h2 : ∀ i, addOrderOf (r i) ∣ 2*h) :
    Even ((univ.filter fun i => ¬addOrderOf (r i) ∣ h).card) := by
  classical
  have hh : (∏ i, ZMod.stdAddChar ((h : ZMod P)*r i)) = 1 := by
    rw [prod_phase, hz]
    simp
  have he : (∏ i, ZMod.stdAddChar ((h : ZMod P)*r i)) =
      (-1 : ℂ)^((univ.filter fun i => ¬addOrderOf (r i) ∣ h).card) := by
    simp_rw [halfperiod_phase _ h (h2 _)]
    rw [Finset.prod_ite]
    simp
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp (he.symm.trans hh)

def smallCount (r : ι → G) : ℕ := (univ.filter fun i => addOrderOf (r i) ≠ 2).card

theorem count_three_lower (r : ι → G) (hz : (∑ i, r i) = 0)
    (hs : ∀ i, addOrderOf (r i) = 2 ∨ addOrderOf (r i) = 3)
    (ho : Odd (orderCount r 3)) : 3 ≤ smallCount r := by
  classical
  have hn := orderCount_ne_one_of_coprime r hz 3 3 (by decide) (by decide) (by
    intro i hi
    rcases hs i with h2 | h3
    · rw [h2]; norm_num
    · exact False.elim (hi h3))
  have he : smallCount r = orderCount r 3 := by
    apply congrArg Finset.card
    ext i
    rcases hs i with hh | hh <;> simp [hh]
  obtain ⟨j, hj⟩ := ho
  omega

theorem count_five_lower (r : ι → ZMod P) (hz : (∑ i, r i) = 0)
    (hs : ∀ i, addOrderOf (r i) = 2 ∨ addOrderOf (r i) = 8 ∨ addOrderOf (r i) = 12)
    (ho : Odd (orderCount r 12)) : 5 ≤ smallCount r := by
  classical
  have hn12 := orderCount_ne_one_of_coprime r hz 12 3 (by decide) (by decide) (by
    intro i hi
    rcases hs i with h2 | h8 | h12
    · rw [h2]; norm_num
    · rw [h8]; norm_num
    · exact False.elim (hi h12))
  have hn8 := orderCount_ne_one_of_annihilator r hz 8 12 (by decide) (by
    intro i hi
    rcases hs i with h2 | h8 | h12
    · rw [h2]; norm_num
    · exact False.elim (hi h8)
    · rw [h12])
  have hn80 : orderCount r 8 ≠ 0 := by
    intro hc
    have hno8 := (orderCount_eq_zero_iff r 8).mp hc
    have h2 : ∀ i, addOrderOf (r i) ∣ 2*6 := by
      intro i
      rcases hs i with h2 | h8 | h12
      · rw [h2]; norm_num
      · exact False.elim (hno8 i h8)
      · rw [h12]
    have hh := even_halfperiod_count r hz 6 h2
    have hf : (univ.filter fun i => ¬addOrderOf (r i) ∣ 6) =
        (univ.filter fun i => addOrderOf (r i) = 12) := by
      ext i
      rcases hs i with h2 | h8 | h12
      · simp [h2]
      · exact False.elim (hno8 i h8)
      · simp [h12]
    rw [hf] at hh
    exact (Nat.not_even_iff_odd.mpr ho) hh
  have he : smallCount r = orderCount r 8+orderCount r 12 := by
    unfold smallCount orderCount
    simp_rw [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hs i with h2 | h8 | h12 <;> simp [*]
  obtain ⟨j, hj⟩ := ho
  omega

theorem count_six_lower (r : ι → ZMod P) (hz : (∑ i, r i) = 0)
    (hs : ∀ i, addOrderOf (r i) = 2 ∨ addOrderOf (r i) = 12 ∨ addOrderOf (r i) = 20)
    (ho : Odd (orderCount r 20)) : 6 ≤ smallCount r := by
  classical
  have hn20 := orderCount_ne_one_of_coprime r hz 20 5 (by decide) (by decide) (by
    intro i hi
    rcases hs i with h2 | h12 | h20
    · rw [h2]; norm_num
    · rw [h12]; norm_num
    · exact False.elim (hi h20))
  have hn12 := orderCount_ne_one_of_coprime r hz 12 3 (by decide) (by decide) (by
    intro i hi
    rcases hs i with h2 | h12 | h20
    · rw [h2]; norm_num
    · exact False.elim (hi h12)
    · rw [h20]; norm_num)
  have h2 : ∀ i, addOrderOf (r i) ∣ 2*30 := by
    intro i
    rcases hs i with h2 | h12 | h20 <;> simp [*]
  have hh := even_halfperiod_count r hz 30 h2
  have hf : (univ.filter fun i => ¬addOrderOf (r i) ∣ 30) =
      (univ.filter fun i => addOrderOf (r i) ≠ 2) := by
    ext i
    rcases hs i with h2 | h12 | h20 <;> simp [*]
  rw [hf] at hh
  have he : smallCount r = orderCount r 12+orderCount r 20 := by
    unfold smallCount orderCount
    simp_rw [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hs i with h2 | h12 | h20 <;> simp [*]
  change Even (smallCount r) at hh
  obtain ⟨j, hj⟩ := ho
  obtain ⟨k, hk⟩ := hh
  omega

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
