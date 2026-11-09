import GaloisForLFunctions.SignFreePurityMechanisms.SimultaneousInseparabilityCostsThePrimorial

/-!
# The Fermat quotient is the derivative at a prime

An integer is a function on `Spec ℤ`: its value at `p` is its residue, its order at `p` the
`p`-adic valuation, its degree `log |a|`. By Fermat's theorem the identity of `ℤ` is a Frobenius
lift at every prime, with `p`-derivation `δ_p a = (a − a ^ p) / p`.

* `ℤ` has no other ring endomorphism (`ringHom_int_eq_id`).
* `δ_p` is the derivative at `p`: on multiples of `p` it lowers the `p`-adic order by exactly one
  (`padicValInt_fermatQuotient_add_one`), and `a` vanishes to `δ_p`-order `m` at `p` exactly when
  `p ^ m ∣ a` (`forall_dvd_iterate_fermatQuotient_iff`).
* The constants of `δ_p` are `0` and `±1` (`fermatQuotient_eq_zero_iff`,
  `eq_zero_or_eq_one_or_eq_neg_one_of_pow_eq_self`): there are no nonconstant integers of zero
  derivative to play the part of the `q`-th powers in Stepanov's auxiliary.
* Order `m` at every prime of `S` costs degree at least `m ∑_{p ∈ S} log p`
  (`mul_sum_log_le_log_abs`), with equality for `∏ p ^ m` (`log_prod_pow_eq`): the product formula
  leaves no slack.
-/

open Finset

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-- The identity is the only ring endomorphism of `ℤ`. -/
theorem ringHom_int_eq_id (φ : ℤ →+* ℤ) : φ = RingHom.id ℤ :=
  RingHom.ext_int _ _

/-- The `p`-derivation of `ℤ`: the Fermat quotient `(a − a ^ p) / p`. -/
def fermatQuotient (p : ℕ) (a : ℤ) : ℤ := (a - a ^ p) / p

variable (p : ℕ) [Fact p.Prime]

/-- Fermat: the identity of `ℤ` is a Frobenius lift at `p`. -/
theorem natCast_dvd_sub_pow (a : ℤ) : (p : ℤ) ∣ a - a ^ p := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

theorem mul_fermatQuotient (a : ℤ) : (p : ℤ) * fermatQuotient p a = a - a ^ p :=
  Int.mul_ediv_cancel' (natCast_dvd_sub_pow p a)

private theorem natCast_prime_ne_zero : (p : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-! ### Constants -/

/-- The constants of `δ_p` are the solutions of `a ^ p = a`. -/
theorem fermatQuotient_eq_zero_iff (a : ℤ) : fermatQuotient p a = 0 ↔ a ^ p = a := by
  rw [← mul_right_inj' (natCast_prime_ne_zero p), mul_fermatQuotient, mul_zero, sub_eq_zero,
    eq_comm]

/-- An integer with `a ^ p = a`, `p ≥ 2`, is `0`, `1` or `-1`. -/
theorem eq_zero_or_eq_one_or_eq_neg_one_of_pow_eq_self {p : ℕ} (hp : 2 ≤ p) {a : ℤ}
    (h : a ^ p = a) : a = 0 ∨ a = 1 ∨ a = -1 := by
  rcases eq_or_ne a 0 with ha | ha
  · exact Or.inl ha
  · obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have hk : a ^ k = 1 := by
      rw [pow_succ] at h
      exact mul_eq_right₀ ha |>.mp h
    exact Or.inr (Int.isUnit_iff.mp (IsUnit.of_pow_eq_one hk (by omega)))

/-! ### The derivative at `p` -/

/-- On a multiple of `p` the Fermat quotient is the cofactor times a unit modulo `p`. -/
theorem fermatQuotient_mul_self (b : ℤ) :
    fermatQuotient p (p * b) = b * (1 - (p : ℤ) ^ (p - 1) * b ^ (p - 1)) := by
  apply mul_left_cancel₀ (natCast_prime_ne_zero p)
  rw [mul_fermatQuotient]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
  have hpow : ((p : ℤ) * b) ^ p = (p : ℤ) * ((p : ℤ) ^ (p - 1) * b ^ (p - 1) * b) := by
    rw [hk, Nat.succ_sub_one, mul_pow, pow_succ, pow_succ]
    ring
  rw [hpow]
  ring

/-- The cofactor unit is coprime to every power of `p`. -/
theorem isCoprime_pow_one_sub (m : ℕ) (b : ℤ) :
    IsCoprime ((p : ℤ) ^ m) (1 - (p : ℤ) ^ (p - 1) * b ^ (p - 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = k + 1 := ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  refine IsCoprime.pow_left ⟨(p : ℤ) ^ k * b ^ (p - 1), 1, ?_⟩
  rw [hk]
  ring

/-- `p ^ m` divides `δ_p (p b)` exactly when it divides `b`. -/
theorem pow_dvd_fermatQuotient_mul_self_iff (m : ℕ) (b : ℤ) :
    (p : ℤ) ^ m ∣ fermatQuotient p (p * b) ↔ (p : ℤ) ^ m ∣ b := by
  rw [fermatQuotient_mul_self]
  exact ⟨(isCoprime_pow_one_sub p m b).dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h _⟩

/-- **`δ_p`-order is `p`-adic order.** The first `m` iterated Fermat quotients of `a` vanish at
`p` exactly when `p ^ m` divides `a`. -/
theorem forall_dvd_iterate_fermatQuotient_iff (m : ℕ) (a : ℤ) :
    (∀ j < m, (p : ℤ) ∣ (fermatQuotient p)^[j] a) ↔ (p : ℤ) ^ m ∣ a := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    constructor
    · intro h
      obtain ⟨b, rfl⟩ := h 0 (Nat.succ_pos m)
      have hδ : (p : ℤ) ^ m ∣ fermatQuotient p (p * b) :=
        (ih _).mp fun j hj => by
          simpa only [Function.iterate_succ_apply] using h (j + 1) (Nat.succ_lt_succ hj)
      rw [pow_succ']
      exact mul_dvd_mul_left _ ((pow_dvd_fermatQuotient_mul_self_iff p m b).mp hδ)
    · rintro ⟨c, rfl⟩ j hj
      have hform : (p : ℤ) ^ (m + 1) * c = p * ((p : ℤ) ^ m * c) := by ring
      rcases j with _ | j
      · exact ⟨(p : ℤ) ^ m * c, hform⟩
      · rw [Function.iterate_succ_apply, hform]
        exact (ih _).mpr ((pow_dvd_fermatQuotient_mul_self_iff p m _).mpr (dvd_mul_right _ _))
          j (Nat.lt_of_succ_lt_succ hj)

/-- **The derivative lowers the order by one.** For a nonzero multiple `a` of `p`,
`ord_p (δ_p a) + 1 = ord_p a`. -/
theorem padicValInt_fermatQuotient_add_one {a : ℤ} (ha : a ≠ 0) (hpa : (p : ℤ) ∣ a) :
    padicValInt p (fermatQuotient p a) + 1 = padicValInt p a := by
  obtain ⟨b, rfl⟩ := hpa
  have hb : b ≠ 0 := right_ne_zero_of_mul ha
  have hcop := isCoprime_pow_one_sub p 1 b
  rw [pow_one] at hcop
  have hu : ¬(p : ℤ) ∣ 1 - (p : ℤ) ^ (p - 1) * b ^ (p - 1) := fun hd =>
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_unit (hcop.isUnit_of_dvd' dvd_rfl hd)
  have hu0 : 1 - (p : ℤ) ^ (p - 1) * b ^ (p - 1) ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero _)
  rw [fermatQuotient_mul_self, padicValInt.mul hb hu0, padicValInt.eq_zero_of_not_dvd hu,
    padicValInt.mul (natCast_prime_ne_zero p) hb, padicValInt.self (Fact.out : p.Prime).one_lt]
  ring

/-! ### The product formula leaves no slack -/

omit [Fact p.Prime] in
/-- **Cost of order `m` on a set of primes.** A nonzero integer vanishing to `δ`-order `m` at
every prime of `S` has `log |a| ≥ m ∑_{p ∈ S} log p`. -/
theorem mul_sum_log_le_log_abs {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (m : ℕ) {a : ℤ}
    (ha : a ≠ 0) (h : ∀ p ∈ S, ∀ j < m, (p : ℤ) ∣ (fermatQuotient p)^[j] a) :
    m * ∑ p ∈ S, Real.log p ≤ Real.log |(a : ℝ)| := by
  have hdvd : ∏ p ∈ S, p ^ m ∣ a.natAbs :=
    prod_pow_dvd_of_forall_pow_dvd hS (fun _ => m) fun p hp => by
      haveI : Fact p.Prime := ⟨hS p hp⟩
      have := (forall_dvd_iterate_fermatQuotient_iff p m a).mp (h p hp)
      rw [← Int.natCast_dvd]
      simpa using this
  have hle : ∏ p ∈ S, p ^ m ≤ a.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hdvd
  have hpos : (0 : ℝ) < ((∏ p ∈ S, p ^ m : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => pow_pos (hS p hp).pos m
  have hlog : (m : ℝ) * ∑ p ∈ S, Real.log p = Real.log ((∏ p ∈ S, p ^ m : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod fun p hp => by
      exact_mod_cast (pow_pos (hS p hp).pos m).ne', Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
  rw [hlog, ← Int.cast_natAbs, Int.cast_natCast]
  exact Real.log_le_log hpos (by exact_mod_cast hle)

omit [Fact p.Prime] in
/-- The bound of `mul_sum_log_le_log_abs` is attained by `∏ p ^ m`. -/
theorem log_prod_pow_eq {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (m : ℕ) :
    (∀ p ∈ S, ∀ j < m, (p : ℤ) ∣ (fermatQuotient p)^[j] ((∏ q ∈ S, q ^ m : ℕ) : ℤ)) ∧
      Real.log |(((∏ q ∈ S, q ^ m : ℕ) : ℤ) : ℝ)| = m * ∑ p ∈ S, Real.log p := by
  constructor
  · intro p hp
    haveI : Fact p.Prime := ⟨hS p hp⟩
    rw [forall_dvd_iterate_fermatQuotient_iff]
    exact_mod_cast Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem (fun q => q ^ m) hp)
  · have hpos : (0 : ℝ) < ((∏ q ∈ S, q ^ m : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun p hp => pow_pos (hS p hp).pos m
    rw [Int.cast_natCast, abs_of_pos hpos, Nat.cast_prod, Real.log_prod fun p hp => by
      exact_mod_cast (pow_pos (hS p hp).pos m).ne', Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]

#print axioms fermatQuotient_eq_zero_iff
#print axioms forall_dvd_iterate_fermatQuotient_iff
#print axioms padicValInt_fermatQuotient_add_one
#print axioms mul_sum_log_le_log_abs
#print axioms log_prod_pow_eq

end GaloisForLFunctions.SignFreePurityMechanisms
