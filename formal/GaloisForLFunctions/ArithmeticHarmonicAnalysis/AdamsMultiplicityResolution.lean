import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionEulerJetExtraction
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.ArithmeticNewtonResolution
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.MixedJetMultiplicity
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AdamsFixedLocusResolution
import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant
import Mathlib.RingTheory.Nullstellensatz

/-!
# Full Adams multiplicity has an exact arithmetic support cost

Shifted Euler extraction converts full polynomial multiplicity on the
torsion grid into low-order residue Newton vanishing. Unique factorization
then forces every coefficient below `2^(qr)` to vanish. Ordinary analytic
mixed jets give the same statement on the actual Adams fixed locus.
-/

open MvPolynomial Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open ArithmeticCorrelationGeometry ArithmeticGaugeTheory

variable (q r : ℕ) [NeZero q] [NeZero r]

/-- The prime-coordinate polynomial of an arithmetic auxiliary below `2^(qr)`. -/
def arithmeticAuxiliaryPolynomial (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    MvPolynomial (shortPrimes (q * r)) ℂ :=
  finiteMonomialPolynomial univ (fun n : Ioo 0 (2 ^ (q * r)) =>
    fun p : shortPrimes (q * r) => n.val.factorization p) c

omit [NeZero q] [NeZero r] in
/-- Evaluating the prime-coordinate polynomial gives the original arithmetic twist sum. -/
theorem arithmeticAuxiliaryPolynomial_eval_twist
    (c : Ioo 0 (2 ^ (q * r)) → ℂ) (x : GaugeTorus) :
    eval (fun p : shortPrimes (q * r) => twist x p) (arithmeticAuxiliaryPolynomial q r c) =
      ∑ n : Ioo 0 (2 ^ (q * r)), c n * twist x n := by
  simp only [arithmeticAuxiliaryPolynomial, finiteMonomialPolynomial, map_sum, map_mul,
    eval_C, map_prod, map_pow, eval_X]
  apply sum_congr rfl
  intro n _
  congr 1
  rw [prod_coe_sort (shortPrimes (q * r)) (fun p => twist x p ^ n.val.factorization p)]
  have hsub : n.val.primeFactors ⊆ shortPrimes (q * r) := by
    intro p hp
    exact Nat.mem_primesBelow.mpr ⟨
      (Nat.le_of_dvd (mem_Ioo.mp n.property).1 (Nat.dvd_of_mem_primeFactors hp)).trans_lt
        (mem_Ioo.mp n.property).2, Nat.prime_of_mem_primeFactors hp⟩
  calc
    _ = ∏ p ∈ n.val.primeFactors, twist x p ^ n.val.factorization p := by
      symm
      apply prod_subset hsub
      intro p _ hp
      have hz : n.val.factorization p = 0 := by
        by_contra h
        exact hp (by simpa only [Nat.support_factorization] using Finsupp.mem_support_iff.mpr h)
      rw [hz, pow_zero]
    _ = twist x (∏ p ∈ n.val.primeFactors, p ^ n.val.factorization p) := by
      rw [twist_prod x _ _ (fun p hp =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      apply prod_congr rfl
      intro p hp
      exact (twist_pow_index x (Nat.prime_of_mem_primeFactors hp).ne_zero _).symm
    _ = twist x n := by
      rw [← Nat.prod_primeFactors_pow_factorization (mem_Ioo.mp n.property).1.ne']

omit [NeZero r] in
/-- Euler jets recover each arithmetic Newton coefficient with its exact normalization. -/
theorem arithmeticAuxiliary_euler_recovery (c : Ioo 0 (2 ^ (q * r)) → ℂ)
    (b : shortPrimes (q * r) → ZMod q) (a : shortPrimes (q * r) → ℕ) :
    (∑ t : shortPrimes (q * r) → ZMod q,
      eval (fun p => ZMod.stdAddChar (t p))
        (shiftedEulerWord (newtonEulerWord q b a) (arithmeticAuxiliaryPolynomial q r c)) *
          conj (torsionPhase q b t)) =
      (q : ℂ) ^ Fintype.card (shortPrimes (q * r)) *
        ((q : ℂ) ^ newtonOrder a * (∏ p, ((a p).factorial : ℂ))) *
          residueNewtonCoefficient (arithmeticNewtonArray q r c) b a := by
  have h := newtonEuler_fourier_extraction q univ
    (fun n : Ioo 0 (2 ^ (q * r)) =>
      fun p : shortPrimes (q * r) => n.val.factorization p) c b a
  rw [residueCoefficient, sum_filter] at h
  rw [arithmeticNewtonCoefficient_eq]
  exact h

/-- Full point multiplicity `r` on the torsion grid detects every coefficient below `2^(qr)`. -/
theorem arithmeticAuxiliary_multiplicity_vanishes_iff
    (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    (∀ t : shortPrimes (q * r) → ZMod q,
      arithmeticAuxiliaryPolynomial q r c ∈
        vanishingIdeal ℂ {(fun p => ZMod.stdAddChar (t p))} ^ r) ↔
      ∀ n, c n = 0 := by
  constructor
  · intro h
    apply (arithmeticNewton_vanishing_iff q r c).mp
    intro b a ha
    have hjet (t : shortPrimes (q * r) → ZMod q) :
        eval (fun p => ZMod.stdAddChar (t p))
          (shiftedEulerWord (newtonEulerWord q b a)
            (arithmeticAuxiliaryPolynomial q r c)) = 0 := by
      have hlen : 1 + (newtonEulerWord q b a).length ≤ r := by
        rw [newtonEulerWord_length]
        change 1 + newtonOrder a ≤ r
        omega
      have hm := shiftedEulerWord_mem_ideal_pow (newtonEulerWord q b a)
        (vanishingIdeal ℂ {(fun p => ZMod.stdAddChar (t p))}) 1
        (Ideal.pow_le_pow_right hlen (h t))
      simpa only [pow_one, mem_vanishingIdeal_singleton_iff, aeval_eq_eval] using hm
    have hrec := arithmeticAuxiliary_euler_recovery q r c b a
    simp only [hjet, zero_mul, sum_const_zero] at hrec
    apply (mul_eq_zero.mp hrec.symm).resolve_left
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    exact mul_ne_zero (pow_ne_zero _ hq) (mul_ne_zero (pow_ne_zero _ hq)
      (prod_ne_zero_iff.mpr fun p _ => by exact_mod_cast Nat.factorial_ne_zero (a p)))
  · intro h t
    have hz : arithmeticAuxiliaryPolynomial q r c = 0 := by
      simp only [arithmeticAuxiliaryPolynomial, finiteMonomialPolynomial, h, map_zero,
        zero_mul, sum_const_zero]
    rw [hz]
    exact Ideal.zero_mem _

/-- Prime coordinates relabeled by a finite ordinal for the analytic mixed-jet interface. -/
def arithmeticAuxiliaryFinitePolynomial (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    MvPolynomial (Fin (Fintype.card (shortPrimes (q * r)))) ℂ :=
  renameEquiv ℂ (Fintype.equivFin (shortPrimes (q * r)))
    (arithmeticAuxiliaryPolynomial q r c)

/-- All ordinary mixed derivatives below order `r` on the torsion grid detect every coefficient. -/
theorem arithmeticAuxiliary_mixedJets_vanishes_iff
    (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    (∀ t : shortPrimes (q * r) → ZMod q,
      ∀ a : Fin (Fintype.card (shortPrimes (q * r))) →₀ ℕ,
        Finsupp.degree a < r →
          HTGeometry.multiIndexJetEvalCLM
            (fun j => ZMod.stdAddChar (t ((Fintype.equivFin (shortPrimes (q * r))).symm j)))
            a (HTGeometry.mvPolynomialMultivariateEntire (arithmeticAuxiliaryFinitePolynomial q r c)) = 0) ↔
      ∀ n, c n = 0 := by
  rw [← arithmeticAuxiliary_multiplicity_vanishes_iff q r c]
  apply forall_congr' fun t => ?_
  rw [← mem_pointIdeal_pow_iff_mixedJets]
  exact renameEquiv_mem_pointIdeal_pow_iff (Fintype.equivFin (shortPrimes (q * r)))
    (arithmeticAuxiliaryPolynomial q r c) (fun p => ZMod.stdAddChar (t p)) r

/-- The embedded torsion grid realizes its prescribed prime-coordinate roots of unity. -/
theorem twist_torsionGauge_prime (P : Finset ℕ) (t : P → ZMod q)
    (p : P) (hp : p.val.Prime) :
    twist (torsionGauge q P t) p = ZMod.stdAddChar (t p) := by
  rw [twist_prime_apply _ hp, torsionGauge, dif_pos p.property, fourier_apply,
    ← map_zsmul]
  change (ZMod.toCircle ((1 : ℤ) • t p) : ℂ) = ZMod.stdAddChar (t p)
  rw [one_zsmul]
  rfl

/-- Full analytic multiplicity on the actual Adams fixed locus has the same arithmetic cost. -/
theorem short_adams_mixedJets_vanishes_iff
    (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    (∀ x : GaugeTorus, IsAdamsFixed (q + 1) x →
      ∀ a : Fin (Fintype.card (shortPrimes (q * r))) →₀ ℕ,
        Finsupp.degree a < r →
          HTGeometry.multiIndexJetEvalCLM
            (fun j => twist x ((Fintype.equivFin (shortPrimes (q * r))).symm j))
            a (HTGeometry.mvPolynomialMultivariateEntire (arithmeticAuxiliaryFinitePolynomial q r c)) = 0) ↔
      ∀ n, c n = 0 := by
  constructor
  · intro h
    apply (arithmeticAuxiliary_mixedJets_vanishes_iff q r c).mp
    intro t a ha
    have hx := h (torsionGauge q (shortPrimes (q * r)) t)
      (isAdamsFixed_torsionGauge q _ t) a ha
    have heval : (fun j => twist (torsionGauge q (shortPrimes (q * r)) t)
        ((Fintype.equivFin (shortPrimes (q * r))).symm j)) =
          fun j => ZMod.stdAddChar (t ((Fintype.equivFin (shortPrimes (q * r))).symm j)) := by
      funext j
      exact twist_torsionGauge_prime q _ t _
        (Nat.mem_primesBelow.mp ((Fintype.equivFin (shortPrimes (q * r))).symm j).property).2
    rw [heval] at hx
    exact hx
  · intro h x _ a _
    have hz : arithmeticAuxiliaryFinitePolynomial q r c = 0 := by
      simp only [arithmeticAuxiliaryFinitePolynomial, arithmeticAuxiliaryPolynomial,
        finiteMonomialPolynomial, h, map_zero, zero_mul, sum_const_zero]
    rw [hz]
    simp only [HTGeometry.multiIndexJetEvalCLM_mvPolynomial_eq_centered_coeff,
      map_zero, coeff_zero, zero_mul]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
