import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionFourierResolution
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting

/-!
# The first arithmetic collision of torsion sampling

The order-`q` torsion grid reads prime valuations modulo `q`. Below `2^q`
every valuation is smaller than `q`, so the grid recovers every coefficient
of a Dirichlet polynomial. At `2^q`, the frequencies of `1` and `2^q`
coincide. This is an exact support threshold, not an asymptotic estimate.
-/

open Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable (q : ℕ) [NeZero q]

/-- The prime-valuation vector visible to order-`q` torsion phases. -/
def valuationResidue (P : Finset ℕ) (n : ℕ) : P → ZMod q :=
  fun p => (n.factorization p : ZMod q)

/-- Prime coordinates sufficient to observe all positive integers below `2^q`. -/
def shortPrimes : Finset ℕ := (2 ^ q).primesBelow

/-- Below the first power of two, every prime valuation is below the torsion order. -/
theorem factorization_lt_torsion_order {n : ℕ} (hn : n ∈ Ioo 0 (2 ^ q)) (p : ℕ) :
    n.factorization p < q := by
  have hn0 : n ≠ 0 := (mem_Ioo.mp hn).1.ne'
  by_cases hp : p.Prime
  · apply (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp
    exact (Nat.pow_le_pow_left hp.two_le _).trans_lt
      ((Nat.ordProj_le p hn0).trans_lt (mem_Ioo.mp hn).2)
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    exact NeZero.pos q

/-- Prime residues distinguish all positive integers below `2^q`. -/
theorem valuationResidue_injOn_short :
    Set.InjOn (valuationResidue q (shortPrimes q)) (Ioo 0 (2 ^ q) : Finset ℕ) := by
  intro m hm n hn h
  apply Nat.eq_of_factorization_eq (mem_Ioo.mp hm).1.ne' (mem_Ioo.mp hn).1.ne'
  intro p
  by_cases hp : p.Prime
  · by_cases hpq : p < 2 ^ q
    · have hpP : p ∈ shortPrimes q := Nat.mem_primesBelow.mpr ⟨hpq, hp⟩
      have he := congrFun h ⟨p, hpP⟩
      change (m.factorization p : ZMod q) = (n.factorization p : ZMod q) at he
      have hr := (ZMod.natCast_eq_natCast_iff' _ _ q).mp he
      simpa only [Nat.mod_eq_of_lt (factorization_lt_torsion_order q hm p),
        Nat.mod_eq_of_lt (factorization_lt_torsion_order q hn p)] using hr
    · rw [Nat.factorization_eq_zero_of_lt (lt_of_lt_of_le (mem_Ioo.mp hm).2 (le_of_not_gt hpq)),
        Nat.factorization_eq_zero_of_lt (lt_of_lt_of_le (mem_Ioo.mp hn).2 (le_of_not_gt hpq))]
  · rw [Nat.factorization_eq_zero_of_not_prime m hp,
      Nat.factorization_eq_zero_of_not_prime n hp]

/-- A short Dirichlet polynomial restricted to the complete prime torsion grid. -/
def shortTorsionPolynomial (c : ℕ → ℂ) (t : shortPrimes q → ZMod q) : ℂ :=
  torsionPolynomial q (Ioo 0 (2 ^ q)) (valuationResidue q (shortPrimes q)) c t

/-- Each residue fibre of a short polynomial contains exactly its original integer. -/
theorem short_residueCoefficient (c : ℕ → ℂ) (n : Ioo 0 (2 ^ q)) :
    residueCoefficient q (Ioo 0 (2 ^ q)) (valuationResidue q (shortPrimes q)) c
      (valuationResidue q (shortPrimes q) n) = c n := by
  classical
  have hf : {m ∈ Ioo 0 (2 ^ q) |
      valuationResidue q (shortPrimes q) m = valuationResidue q (shortPrimes q) n} = {n.val} := by
    ext m
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hm, he⟩
      exact valuationResidue_injOn_short q hm n.property he
    · intro he
      subst m
      exact ⟨n.property, rfl⟩
  rw [residueCoefficient, hf, sum_singleton]

/-- Exact coefficient recovery below the first arithmetic collision. -/
theorem short_torsion_coefficient_recovery (c : ℕ → ℂ) (n : Ioo 0 (2 ^ q)) :
    (∑ t, shortTorsionPolynomial q c t *
      conj (torsionPhase q (valuationResidue q (shortPrimes q) n) t)) =
      (q : ℂ) ^ Fintype.card (shortPrimes q) * c n := by
  have h := torsion_coefficient_recovery q (Ioo 0 (2 ^ q))
    (valuationResidue q (shortPrimes q)) c (valuationResidue q (shortPrimes q) n)
  rw [short_residueCoefficient q c n] at h
  exact h

/-- No nonzero short auxiliary vanishes on the entire prime torsion grid. -/
theorem short_torsion_vanishing_iff (c : ℕ → ℂ) :
    (∀ t, shortTorsionPolynomial q c t = 0) ↔
      ∀ n ∈ Ioo 0 (2 ^ q), c n = 0 := by
  constructor
  · intro h n hn
    have hr := short_torsion_coefficient_recovery q c ⟨n, hn⟩
    simp only [h, zero_mul, sum_const_zero] at hr
    exact (mul_eq_zero.mp hr.symm).resolve_left
      (pow_ne_zero _ (by exact_mod_cast NeZero.ne q))
  · intro h t
    unfold shortTorsionPolynomial torsionPolynomial
    apply Finset.sum_eq_zero
    intro n hn
    rw [h n hn, zero_mul]

omit [NeZero q] in
/-- The boundary collision is present on every finite prime coordinate set. -/
theorem valuationResidue_two_pow (P : Finset ℕ) :
    valuationResidue q P (2 ^ q) = valuationResidue q P 1 := by
  funext p
  simp only [valuationResidue, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    Nat.factorization_one, Finsupp.zero_apply, Nat.cast_zero]

/-- The binomial at length `2^q` is identically zero on the torsion grid. -/
theorem boundary_binomial_vanishes (P : Finset ℕ) (t : P → ZMod q) :
    torsionPhase q (valuationResidue q P (2 ^ q)) t -
      torsionPhase q (valuationResidue q P 1) t = 0 := by
  rw [valuationResidue_two_pow, sub_self]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
