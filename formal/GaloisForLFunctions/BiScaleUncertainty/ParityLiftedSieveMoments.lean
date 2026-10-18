import GaloisForLFunctions.BiScaleUncertainty.SieveTripleFourier

/-!
# Parity-lifted divisor weights with invisible odd moments

Explicit weights have precisely two incomparable even-order coordinates.
Changing their relative sign preserves all affine quadratic observations.
Their literal responses reverse sign under translation by fifteen, forcing
every odd-length translated moment to vanish for every parameter value.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

private def atom (p : ℕ) (w : ℂ) (d : ℕ) : ℂ := if d = p then w else 0

private theorem coordinate_atom (N p : ℕ) (hp : p ∈ Finset.Icc 1 N) (w : ℂ) (q : ℕ) :
    coordinate N (atom p w) q = if q ∣ p then w/(p : ℂ) else 0 := by
  unfold coordinate atom
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, if d = p then (if q ∣ p then w/(p : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d = p
      · subst d; simp
      · simp [hd]
    _ = _ := by simp [hp]

private theorem coordinate_add (N : ℕ) (c e : ℕ → ℂ) (q : ℕ) :
    coordinate N (c+e) q = coordinate N c q + coordinate N e q := by
  unfold coordinate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : q ∣ d <;> simp [hd, add_div]

private theorem dvd_prime_product {p r : ℕ} (hp : Nat.Prime p) (hr : Nat.Prime r) (q : ℕ) :
    q ∣ p*r ↔ q = 1 ∨ q = p ∨ q = r ∨ q = p*r := by
  constructor
  · intro h
    obtain ⟨a,b,ha,hb,hq⟩ := exists_dvd_and_dvd_of_dvd_mul h
    rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
      rcases (Nat.dvd_prime hr).mp hb with rfl | rfl <;> simp_all
  · rintro (rfl | rfl | rfl | rfl) <;> simp

/-- Explicit divisor weights realizing the two even modes six and ten. -/
def parityWeight (t : ℂ) : ℕ → ℂ :=
  atom 1 (1+t) + atom 2 (-2*(1+t)) + atom 3 (-3) +
    atom 5 (-5*t) + atom 6 6 + atom 10 (10*t)

/-- The multiples-coordinate profile is supported exactly at six and ten. -/
theorem coordinate_parityWeight (N : ℕ) (t : ℂ) (q : ℕ) :
    coordinate (N+10) (parityWeight t) q = if q = 6 then 1 else if q = 10 then t else 0 := by
  rw [parityWeight, coordinate_add, coordinate_add, coordinate_add, coordinate_add, coordinate_add,
    coordinate_atom _ 1 (by simp), coordinate_atom _ 2 (by simp),
    coordinate_atom _ 3 (by simp), coordinate_atom _ 5 (by simp),
    coordinate_atom _ 6 (by simp), coordinate_atom _ 10 (by simp)]
  by_cases h1 : q = 1
  · subst q; norm_num; ring
  by_cases h2 : q = 2
  · subst q; norm_num; ring
  by_cases h3 : q = 3
  · subst q; norm_num
  by_cases h5 : q = 5
  · subst q; norm_num; ring
  by_cases h6 : q = 6
  · subst q; norm_num
  by_cases h10 : q = 10
  · subst q; norm_num
  have hd6 : q ∣ 6 ↔ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 6 := by
    simpa using dvd_prime_product Nat.prime_two Nat.prime_three q
  have hd10 : q ∣ 10 ↔ q = 1 ∨ q = 2 ∨ q = 5 ∨ q = 10 := by
    simpa using dvd_prime_product Nat.prime_two Nat.prime_five q
  simp [hd6, hd10, Nat.dvd_one, Nat.dvd_prime Nat.prime_two,
    Nat.dvd_prime Nat.prime_three, Nat.dvd_prime Nat.prime_five, h1,h2,h3,h5,h6,h10]

/-- Flipping the mode-ten sign preserves every affine quadratic observation. -/
theorem parityWeight_allDataEqual (N : ℕ) :
    AllDataEqual (N+10) (parityWeight 1) (parityWeight (-1)) := by
  apply ((allData_iff_finiteData_iff_comparableProducts _ _ _).1).mpr
  apply ((allData_iff_finiteData_iff_comparableProducts _ _ _).2).mpr
  intro q _ d hd
  have hdq := Nat.dvd_of_mem_divisors hd
  simp only [coordinate_parityWeight]
  by_cases hq6 : q = 6
  · subst q
    have hd10 : d ≠ 10 := by intro he; subst d; norm_num at hdq
    by_cases hd6 : d = 6 <;> simp [hd6,hd10]
  by_cases hq10 : q = 10
  · subst q
    have hd6 : d ≠ 6 := by intro he; subst d; norm_num at hdq
    by_cases hd10 : d = 10 <;> simp [hd6,hd10]
  simp [hq6,hq10]

private theorem residueSignal_atom (N p : ℕ) (hp : p ∈ Finset.Icc 1 N)
    (w : ℂ) (k : ℕ) :
    residueSignal N (atom p w) (k : ZMod N.factorial) = if p ∣ k then w else 0 := by
  rw [residueSignal_natCast]
  unfold atom
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, if d = p then (if p ∣ k then w else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d = p
      · subst d; simp
      · simp [hd]
    _ = _ := by simp [hp]

private theorem residueSignal_add (N : ℕ) (c e : ℕ → ℂ) (k : ZMod N.factorial) :
    residueSignal N (c+e) k = residueSignal N c k + residueSignal N e k := by
  simp only [residueSignal, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem six_dvd_iff (k : ℕ) : 6 ∣ k ↔ 2 ∣ k ∧ 3 ∣ k := by
  constructor
  · intro h
    exact ⟨dvd_trans (by norm_num : 2 ∣ 6) h, dvd_trans (by norm_num : 3 ∣ 6) h⟩
  · rintro ⟨h2,h3⟩
    exact (by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3

private theorem ten_dvd_iff (k : ℕ) : 10 ∣ k ↔ 2 ∣ k ∧ 5 ∣ k := by
  constructor
  · intro h
    exact ⟨dvd_trans (by norm_num : 2 ∣ 10) h, dvd_trans (by norm_num : 5 ∣ 10) h⟩
  · rintro ⟨h2,h5⟩
    exact (by norm_num : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2 h5

/-- The actual response factors into a parity sign and an odd-prime pair. -/
theorem residueSignal_parityWeight (N : ℕ) (t : ℂ) (k : ℕ) :
    residueSignal (N+10) (parityWeight t) (k : ZMod (N+10).factorial) =
      (if 2 ∣ k then (1 : ℂ) else -1) *
        (-(1+t) + (if 3 ∣ k then 3 else 0) + (if 5 ∣ k then 5*t else 0)) := by
  rw [parityWeight, residueSignal_add, residueSignal_add, residueSignal_add,
    residueSignal_add, residueSignal_add,
    residueSignal_atom _ 1 (by simp), residueSignal_atom _ 2 (by simp),
    residueSignal_atom _ 3 (by simp), residueSignal_atom _ 5 (by simp),
    residueSignal_atom _ 6 (by simp), residueSignal_atom _ 10 (by simp)]
  simp only [one_dvd, if_true, six_dvd_iff, ten_dvd_iff]
  by_cases h2 : 2 ∣ k <;> by_cases h3 : 3 ∣ k <;> by_cases h5 : 5 ∣ k <;>
    simp [h2,h3,h5] <;> ring

/-- Translation by fifteen reverses the literal residue response. -/
theorem residueSignal_parityWeight_antiperiod (N : ℕ) (t : ℂ) (n : ZMod (N+10).factorial) :
    residueSignal (N+10) (parityWeight t) (n+15) =
      -residueSignal (N+10) (parityWeight t) n := by
  have hf0 := residueSignal_parityWeight N t n.val
  rw [ZMod.natCast_zmod_val] at hf0
  have hf15 := residueSignal_parityWeight N t (n.val+15)
  push_cast at hf15
  rw [ZMod.natCast_zmod_val] at hf15
  rw [hf15,hf0]
  have h2 : 2 ∣ n.val+15 ↔ ¬2 ∣ n.val := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  have h3 : 3 ∣ n.val+15 ↔ 3 ∣ n.val := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  have h5 : 5 ∣ n.val+15 ↔ 5 ∣ n.val := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  simp only [h2,h3,h5]
  by_cases hp : 2 ∣ n.val <;> simp [hp]

/-- Every odd-length translated moment vanishes throughout the explicit weight family. -/
theorem translationMoment_parityWeight (N : ℕ) (t : ℂ) (m : ℕ)
    (h : Fin (2*m+1) → ZMod (N+10).factorial) :
    translationMoment (residueSignal (N+10) (parityWeight t)) h = 0 := by
  exact translationMoment_of_antiperiodic _ 15 (residueSignal_parityWeight_antiperiod N t) m h

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
