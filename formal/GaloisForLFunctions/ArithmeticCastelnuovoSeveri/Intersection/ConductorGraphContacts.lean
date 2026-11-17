import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Integral graphs with unit vertical contact at prime-power ratios

The graph of conductor `n` has equation `Y = Gₙ(T)`, with coefficient `rad(d)` at
each divisor `d ∣ n`. Its degree is exactly the conductor. The content of a difference
measures the vertical part of the intersection. A change at just one prime
has length one there, at any depth. Two changed primes give unit content.
For two effective divisors the content of their resultant records all mixed
vertical lengths, including the multiplicities of the graphs.
-/

noncomputable section

open Finset Polynomial
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Divisor polynomial of degree n, with squarefree coefficients. -/
def conductorGraph (n : ℕ) : ℤ[X] :=
  ∑ d ∈ n.divisors, monomial d ((∏ p ∈ d.primeFactors, p : ℕ) : ℤ)

private theorem graph_coeff {n : ℕ} (hn : n ≠ 0) (d : ℕ) :
    (conductorGraph n).coeff d = if d ∣ n then ((∏ p ∈ d.primeFactors, p : ℕ) : ℤ) else 0 := by
  classical
  simp [conductorGraph, coeff_monomial, Nat.mem_divisors, hn]

/-- The same graph that carries vertical contact has horizontal degree n. -/
theorem conductorGraph_natDegree {n : ℕ} (hn : n ≠ 0) : (conductorGraph n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    rw [graph_coeff hn, if_neg (fun h => hd.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h))]
  · rw [graph_coeff hn, if_pos dvd_rfl]
    exact_mod_cast (prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos).ne'

/-- Distinct positive conductors define distinct horizontal branches. -/
theorem conductorContact_graph_ne {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hne : m ≠ n) :
    conductorGraph m ≠ conductorGraph n := by
  intro he
  exact hne ((conductorGraph_natDegree hm).symm.trans
    ((congrArg Polynomial.natDegree he).trans (conductorGraph_natDegree hn)))

/-- Absolute content, multiplicative by Gauss's lemma. -/
def verticalContent : ℤ[X] →* ℕ where
  toFun f := f.content.natAbs
  map_one' := by simp
  map_mul' f g := by simp only [content_mul, Int.natAbs_mul]

/-- Vertical intersection order of the two graph equations. -/
def conductorContact (m n : ℕ) : ℕ :=
  verticalContent (conductorGraph m - conductorGraph n)

theorem conductorContact_comm (m n : ℕ) : conductorContact m n = conductorContact n m := by
  unfold conductorContact
  rw [← neg_sub (conductorGraph n), ← neg_one_mul, map_mul]
  have h : verticalContent (-1) = 1 := by
    change (content (-1 : ℤ[X])).natAbs = 1
    rw [← C_1, ← map_neg, content_C]
    rfl
  rw [h, one_mul]

/-- The first new prime power supplies a coefficient equal to the prime itself. -/
private theorem contact_dvd_of_increase {m n p : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hp : p.Prime) (h : m.factorization p < n.factorization p) : conductorContact m n ∣ p := by
  let k := m.factorization p + 1
  have hk : 0 < k := Nat.succ_pos _
  have hdm : ¬ p^k ∣ m := fun hd => (Nat.not_succ_le_self _) ((hp.pow_dvd_iff_le_factorization hm).mp hd)
  have hdn : p^k ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr h
  have hd := Int.natAbs_dvd_natAbs.mpr
    (content_dvd_coeff (p := conductorGraph m - conductorGraph n) (p^k))
  change (conductorGraph m - conductorGraph n).content.natAbs ∣ p
  simpa only [coeff_sub, graph_coeff hm, graph_coeff hn, if_neg hdm, if_pos hdn, zero_sub,
    Int.natAbs_neg, Int.natAbs_natCast, Nat.primeFactors_pow p hk.ne', hp.primeFactors,
    prod_singleton] using hd

private theorem contact_dvd_of_factor {m t p : ℕ} (hm : m ≠ 0) (ht : t ≠ 0)
    (hp : p.Prime) (hd : p ∣ t) : conductorContact m (m*t) ∣ p := by
  apply contact_dvd_of_increase hm (Nat.mul_ne_zero hm ht) hp
  rw [Nat.factorization_mul hm ht, Finsupp.add_apply]
  exact Nat.lt_add_of_pos_right (hp.factorization_pos_of_dvd ht hd)

/-- The graphs meet along the whole vertical fibre at a prime-power dilation,
with multiplicity exactly one even when the base conductor is divisible by the prime. -/
theorem conductorContact_mul_prime_pow {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hk : 0 < k) : conductorContact m (m*p^k) = p := by
  have hpk := pow_ne_zero k hp.ne_zero
  refine Nat.dvd_antisymm (contact_dvd_of_factor hm hpk hp (dvd_pow_self p hk.ne')) ?_
  change p ∣ (conductorGraph m - conductorGraph (m*p^k)).content.natAbs
  apply Int.natCast_dvd_natCast.mp
  rw [Int.dvd_natAbs, dvd_content_iff_C_dvd, C_dvd_iff_dvd_coeff]
  intro d
  rw [coeff_sub, graph_coeff hm, graph_coeff (Nat.mul_ne_zero hm hpk)]
  by_cases hd : d ∣ m
  · rw [if_pos hd, if_pos (hd.trans (dvd_mul_right m _)), sub_self]
    exact dvd_zero _
  · rw [if_neg hd, zero_sub, dvd_neg]
    by_cases hdm : d ∣ m*p^k
    · rw [if_pos hdm]
      have hdp : p ∣ d := by
        by_contra hnp
        have hc := (hp.coprime_iff_not_dvd.mpr hnp).symm.pow_right k
        exact hd (hc.dvd_of_dvd_mul_right hdm)
      have hd0 := ne_zero_of_dvd_ne_zero (Nat.mul_ne_zero hm hpk) hdm
      exact_mod_cast dvd_prod_of_mem (fun q : ℕ => q) (Nat.mem_primeFactors.mpr ⟨hp, hdp, hd0⟩)
    · rw [if_neg hdm]
      exact dvd_zero _

/-- The log of the vertical intersection is exactly the von Mangoldt weight
on every multiplicative ray. Equal graphs use the convention `log 0 = 0`. -/
theorem log_conductorContact_mul {m t : ℕ} (hm : m ≠ 0) (ht : t ≠ 0) :
    Real.log (conductorContact m (m*t) : ℝ) = Λ t := by
  by_cases ht1 : t = 1
  · subst t
    simp [conductorContact, verticalContent]
  by_cases hpp : IsPrimePow t
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp hpp
    rw [conductorContact_mul_prime_pow hm hp hk, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  · obtain ⟨p, hpt, q, hqt, hpq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le
      (by omega : 2 ≤ t)).mp hpp
    obtain ⟨hp, hdp, _⟩ := Nat.mem_primeFactors.mp hpt
    obtain ⟨hq, hdq, _⟩ := Nat.mem_primeFactors.mp hqt
    have hd := Nat.dvd_gcd (contact_dvd_of_factor hm ht hp hdp) (contact_dvd_of_factor hm ht hq hdq)
    rw [((Nat.coprime_primes hp hq).mpr hpq).gcd_eq_one] at hd
    rw [Nat.eq_one_of_dvd_one hd, Nat.cast_one, Real.log_one,
      ArithmeticFunction.vonMangoldt_apply, if_neg hpp]

/-- Incomparable conductors have no vertical intersection. -/
theorem conductorContact_of_incomparable {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : ¬ m ∣ n) (hnm : ¬ n ∣ m) : conductorContact m n = 1 := by
  have witness {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : ¬ a ∣ b) :
      ∃ p, p.Prime ∧ b.factorization p < a.factorization p := by
    rw [← Nat.factorization_le_iff_dvd ha hb] at h
    change ¬ ∀ p, a.factorization p ≤ b.factorization p at h
    push Not at h
    obtain ⟨p, hp⟩ := h
    refine ⟨p, ?_, hp⟩
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime a hnp] at hp
    omega
  obtain ⟨p, hp, hp'⟩ := witness hm hn hmn
  obtain ⟨q, hq, hq'⟩ := witness hn hm hnm
  have hpd := contact_dvd_of_increase hn hm hp hp'
  rw [conductorContact_comm] at hpd
  have hd := Nat.dvd_gcd hpd (contact_dvd_of_increase hm hn hq hq')
  have hne : p ≠ q := by rintro rfl; omega
  rw [((Nat.coprime_primes hp hq).mpr hne).gcd_eq_one] at hd
  exact Nat.eq_one_of_dvd_one hd

/-- Equation of a union of thickened conductor graphs. -/
def conductorDivisor (S : Finset ℕ) (a : ℕ → ℕ) : Polynomial ℤ[X] :=
  ∏ n ∈ S, (X - C (conductorGraph n)) ^ a n

/-- The vertical order of the Sylvester determinant of the two divisor equations. -/
def verticalIntersection (S T : Finset ℕ) (a b : ℕ → ℕ) : ℕ :=
  verticalContent ((conductorDivisor S a).resultant (conductorDivisor T b))

/-- A single elimination determinant counts every mixed contact of the thickened
divisors with the product of their multiplicities. -/
theorem verticalIntersection_eq (S T : Finset ℕ) (a b : ℕ → ℕ) :
    verticalIntersection S T a b =
      ∏ i ∈ S, ∏ j ∈ T, conductorContact i j ^ (a i * b j) := by
  classical
  unfold verticalIntersection
  have hm (i : ℕ) : ((X - C (conductorGraph i)) ^ a i).Monic :=
    (monic_X_sub_C _).pow _
  rw [conductorDivisor, resultant_prod_left _ _ _ _ (by simp [fun i => (hm i).leadingCoeff]) le_rfl,
    map_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [natDegree_pow, natDegree_X_sub_C, mul_one, resultant_X_sub_C_pow_left _ _ _ _ le_rfl,
    conductorDivisor, eval_prod, map_pow, map_prod, ← Finset.prod_pow]
  refine prod_congr rfl fun j _ => ?_
  simp only [eval_pow, eval_sub, eval_X, eval_C, map_pow, ← pow_mul, conductorContact,
    Nat.mul_comm (b j)]

#print axioms conductorGraph_natDegree
#print axioms conductorContact_mul_prime_pow
#print axioms log_conductorContact_mul
#print axioms conductorContact_of_incomparable
#print axioms verticalIntersection_eq

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
