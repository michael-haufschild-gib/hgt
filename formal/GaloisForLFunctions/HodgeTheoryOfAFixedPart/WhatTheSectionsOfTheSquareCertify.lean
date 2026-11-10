import GaloisForLFunctions.HodgeTheoryOfAFixedPart.RiemannRochOnTheTowerHasTheGluingIndex
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints

/-!
# What the sections of the square certify

Bézout for a class with a section is proved by restriction: a section that vanishes on a set of
graphs and not on `Γ_m` has, on `Γ_m`, at least as many zeros as `Γ_m` has contacts with the set,
and the product formula turns the zeros into the size `log|x_m|`. This file compares what the
sections of the arithmetic square certify with the entries of the normal form.

* **The contacts below** (`sum_contact_properDivisors_le_log_abs`): a section that vanishes on the
  graphs of the proper divisors of `m` and not on `Γ_m` has
  `Σ_{d ∣ m, d < m} Γ_d·Γ_m = log m ≤ log|x_m|`. Every contact below `Γ_m` is certified, prime
  powers included.
* **The contacts above, at the primes** (`sum_contact_primes_le_log_abs`): a section that
  vanishes on `Γ_{pm}` for the primes `p` of a finite set and not on `Γ_m` has
  `Σ_p Γ_m·Γ_{pm} = Σ_p log p ≤ log|x_m|`.
* **Not at the prime powers** (`primePointSection`, `log_abs_primePointSection_lt`): the section
  `p − e_p` vanishes on every `Γ_{p^j}`, `j ≥ 1`, and is `p` on the diagonal. The graphs
  `Γ_p, Γ_{p²}, …` pass through one point of the diagonal and impose one condition there, while
  the normal form counts `Γ_1·Γ_{p^j} = log p` for each `j`: on this section
  `log|x_1| = log p < J log p = Σ_{j ≤ J} Γ_1·Γ_{p^j}` for `J ≥ 2`.

So restriction certifies the contacts of the normal form below a graph, and above it one contact
for each prime. It certifies neither the contacts with the higher prime powers above a graph nor
any jet: for the pairing of the normal form, Bézout on a class with a section is a bound from
above on the size of the section, by the jets and by the prime powers.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### The contacts below a graph -/

/-- **The contacts below a graph are certified.** A section of the arithmetic square that
vanishes on the graphs of the proper divisors of `m` and not on `Γ_m` is at least as large on
`Γ_m` as the contacts of `Γ_m` with these graphs. -/
theorem sum_contact_properDivisors_le_log_abs (x : ghostRing) (m : ℕ+)
    (hvan : ∀ d : ℕ+, (d : ℕ) ∣ m → (d : ℕ) < m → ghostComponent d x = 0)
    (hne : ghostComponent m x ≠ 0) :
    ∑ d ∈ (m : ℕ).properDivisors, contact d m ≤ Real.log |((ghostComponent m x : ℤ) : ℝ)| := by
  rw [sum_contact_properDivisors m.pos]
  have h := natCast_le_abs_ghostComponent hne (natCast_dvd_ghostComponent_of_vanish x m hvan)
  have h' : ((m : ℕ) : ℝ) ≤ |((ghostComponent m x : ℤ) : ℝ)| := by exact_mod_cast h
  exact Real.log_le_log (by exact_mod_cast m.pos) h'

/-! ### The contacts above a graph, at the primes -/

/-- A section that vanishes on `Γ_{pm}` is divisible by `p` on `Γ_m`. -/
theorem prime_dvd_ghostComponent_of_vanish (x : ghostRing) (m : ℕ+) {p : ℕ} (hp : p.Prime)
    (hvan : ghostComponent (⟨p, hp.pos⟩ * m) x = 0) : (p : ℤ) ∣ ghostComponent m x := by
  have h := x.2 ⟨p, hp.pos⟩ hp m
  rw [ghostComponent_apply] at hvan
  rw [hvan, zero_sub] at h
  have h1 : (p : ℤ) ∣ (((⟨p, hp.pos⟩ : ℕ+) : ℕ) : ℤ) ^ ((m : ℕ).factorization p + 1) :=
    dvd_pow_self _ (Nat.succ_ne_zero _)
  exact (dvd_neg.mp (h1.trans h))

/-- **The contacts above a graph are certified at the primes.** A section that vanishes on
`Γ_{pm}` for the primes `p` of a finite set and not on `Γ_m` is at least as large on `Γ_m` as the
contacts of `Γ_m` with these graphs. -/
theorem sum_contact_primes_le_log_abs (x : ghostRing) (m : ℕ+) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hvan : ∀ p (hp : p ∈ P), ghostComponent (⟨p, (hP p hp).pos⟩ * m) x = 0)
    (hne : ghostComponent m x ≠ 0) :
    ∑ p ∈ P, contact m (p * m) ≤ Real.log |((ghostComponent m x : ℤ) : ℝ)| := by
  -- the product of the primes divides the value
  have hdvd : (∏ p ∈ P, p) ∣ (ghostComponent m x).natAbs :=
    Finset.prod_primes_dvd _ (fun p hp => (hP p hp).prime) fun p hp =>
      Int.natCast_dvd.mp (prime_dvd_ghostComponent_of_vanish x m (hP p hp) (hvan p hp))
  have hpos : 0 < (ghostComponent m x).natAbs := Int.natAbs_pos.mpr hne
  have hle : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ |((ghostComponent m x : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Nat.le_of_dvd hpos hdvd
  have hprod : (0 : ℝ) < ((∏ p ∈ P, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (hP p hp).pos
  have hcontact : ∀ p ∈ P, contact m (p * m) = Real.log p := by
    intro p hp
    have hp' := hP p hp
    have hlt : (m : ℕ) < p * m := lt_mul_of_one_lt_left m.pos hp'.one_lt
    rw [contact_of_dvd_of_lt (dvd_mul_left _ _) hlt, Nat.mul_div_cancel _ m.pos,
      ArithmeticFunction.vonMangoldt_apply_prime hp']
  rw [Finset.sum_congr rfl hcontact, ← Real.log_prod fun p hp => by
    exact_mod_cast (hP p hp).pos.ne']
  refine Real.log_le_log (Finset.prod_pos fun p hp => by exact_mod_cast (hP p hp).pos) ?_
  rw [← Nat.cast_prod]
  exact hle

/-! ### The prime powers above the diagonal -/

/-- The section `p − e_p`: `p` on the graphs of the degrees prime to `p`, zero on the others. -/
def primePointSection (p : ℕ) : ghostRing := (p : ghostRing) - orbitNat p

theorem ghostComponent_primePointSection {p : ℕ} (hp : 0 < p) (n : ℕ+) :
    ghostComponent n (primePointSection p) = if p ∣ (n : ℕ) then 0 else (p : ℤ) := by
  rw [primePointSection, map_sub, map_natCast, ghostComponent_orbitNat hp]
  split_ifs <;> simp

/-- **One section vanishes on every `Γ_{p^j}`, `j ≥ 1`, and is `p` on the diagonal.** -/
theorem primePointSection_spec {p : ℕ} (hp : p.Prime) :
    ghostComponent 1 (primePointSection p) = p ∧
      ∀ j : ℕ, 1 ≤ j → ∀ h : 0 < p ^ j, ghostComponent ⟨p ^ j, h⟩ (primePointSection p) = 0 := by
  refine ⟨?_, fun j hj h => ?_⟩
  · rw [ghostComponent_primePointSection hp.pos, if_neg]
    rw [PNat.one_coe, Nat.dvd_one]
    exact hp.ne_one
  · rw [ghostComponent_primePointSection hp.pos, if_pos]
    exact dvd_pow_self p (by omega)

/-- **The contacts with the prime powers above the diagonal are not certified.** On the section
`p − e_p`, which vanishes on `Γ_p, …, Γ_{p^J}`, the size on the diagonal is `log p`, below the
`J log p` of the contacts of the normal form, for `J ≥ 2`. -/
theorem log_abs_primePointSection_lt {p : ℕ} (hp : p.Prime) {J : ℕ} (hJ : 2 ≤ J) :
    Real.log |((ghostComponent 1 (primePointSection p) : ℤ) : ℝ)| <
      ∑ j ∈ Icc 1 J, contact 1 (p ^ j) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hcontact : ∀ j ∈ Icc 1 J, contact 1 (p ^ j) = Real.log p := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    rw [contact_of_dvd_of_lt (one_dvd _) (Nat.one_lt_pow (by omega) hp.one_lt), Nat.div_one,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [(primePointSection_spec hp).1, Finset.sum_congr rfl hcontact, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul, Int.cast_natCast, abs_of_pos (by linarith)]
  have hJ' : (2 : ℝ) ≤ ((J + 1 - 1 : ℕ) : ℝ) := by
    rw [Nat.add_sub_cancel]
    exact_mod_cast hJ
  nlinarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
