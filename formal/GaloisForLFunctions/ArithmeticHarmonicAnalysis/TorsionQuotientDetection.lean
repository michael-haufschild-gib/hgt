import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionEulerJetExtraction
import Mathlib.RingTheory.Nullstellensatz

/-!
# Torsion multiplicity detects quotient support

On the order-`q` torsion grid, multiplicity `r` detects every polynomial whose
support exponents have quotient total degree below `r`. Fourier extraction
isolates a residue fibre; a maximal quotient monomial survives unchanged.
Unlike an arithmetic interval bound, this criterion applies directly to
polynomial differences and arbitrary finite sets of prime coordinates.
-/

open MvPolynomial Finset
open scoped ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quotient degree records the number of complete torsion periods in an exponent. -/
def torsionQuotientOrder (q : ℕ) (a : ι →₀ ℕ) : ℕ := ∑ i, a i / q

omit [DecidableEq ι] in
private theorem finiteMonomialPolynomial_support (F : MvPolynomial ι ℂ) :
    finiteMonomialPolynomial F.support (fun a i => a i) F.coeff = F := by
  conv_rhs => rw [MvPolynomial.as_sum F]
  rw [finiteMonomialPolynomial]
  apply sum_congr rfl
  intro a _
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  intro i
  exact pow_zero _

/-- Full torsion multiplicity kills a polynomial with no quotient monomial of order `r`. -/
theorem eq_zero_of_torsionMultiplicity_of_quotientOrder_lt
    (q r : ℕ) [NeZero q] (F : MvPolynomial ι ℂ)
    (hdegree : ∀ a ∈ F.support, torsionQuotientOrder q a < r)
    (hmult : ∀ t : ι → ZMod q,
      F ∈ vanishingIdeal ℂ {fun i => ZMod.stdAddChar (t i)} ^ r) : F = 0 := by
  classical
  by_contra hF
  obtain ⟨a, ha, hmax⟩ := exists_max_image F.support (torsionQuotientOrder q)
    (MvPolynomial.support_nonempty.mpr hF)
  let b : ι → ZMod q := fun i => (a i : ZMod q)
  let k : ι → ℕ := fun i => a i / q
  have hjet (t : ι → ZMod q) :
      eval (fun i => ZMod.stdAddChar (t i))
        (shiftedEulerWord (newtonEulerWord q b k) F) = 0 := by
    have hlen : 1 + (newtonEulerWord q b k).length ≤ r := by
      rw [newtonEulerWord_length]
      have := hdegree a ha
      change (∑ i, a i / q) < r at this
      dsimp only [k]
      omega
    have hm := shiftedEulerWord_mem_ideal_pow (newtonEulerWord q b k)
      (vanishingIdeal ℂ {fun i => ZMod.stdAddChar (t i)}) 1
      (Ideal.pow_le_pow_right hlen (hmult t))
    simpa only [pow_one, mem_vanishingIdeal_singleton_iff, aeval_eq_eval] using hm
  have hrec := newtonEuler_fourier_extraction q F.support (fun a i => a i) F.coeff b k
  rw [finiteMonomialPolynomial_support] at hrec
  simp only [hjet, zero_mul, sum_const_zero] at hrec
  have hnorm : (q : ℂ) ^ Fintype.card ι *
      ((q : ℂ) ^ (∑ i, k i) * ∏ i, ((k i).factorial : ℂ)) ≠ 0 := by
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    exact mul_ne_zero (pow_ne_zero _ hq) (mul_ne_zero (pow_ne_zero _ hq)
      (prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast Nat.factorial_ne_zero (k i)))
  have hz := (mul_eq_zero.mp hrec.symm).resolve_left hnorm
  have htop : residueCoefficient q F.support (fun a i => (a i : ZMod q))
      (fun a => F.coeff a * ∏ i, ((a i / q).choose (k i) : ℂ)) b = F.coeff a := by
    rw [residueCoefficient, sum_eq_single a]
    · simp only [k, Nat.choose_self, Nat.cast_one, prod_const_one, mul_one]
    · intro d hd hda
      obtain ⟨hd, hres⟩ := mem_filter.mp hd
      have hnot : ¬ ∀ i, a i / q ≤ d i / q := by
        intro hle
        have hsum : (∑ i, a i / q) = ∑ i, d i / q :=
          le_antisymm (sum_le_sum fun i _ => hle i) (hmax d hd)
        have hquo := (sum_eq_sum_iff_of_le
          (fun i (_ : i ∈ (univ : Finset ι)) => hle i)).mp hsum
        apply hda
        ext i
        have hr := (ZMod.natCast_eq_natCast_iff' (d i) (a i) q).mp (congrFun hres i)
        have hqi := hquo i (mem_univ i)
        have h1 := Nat.mod_add_div (a i) q
        have h2 := Nat.mod_add_div (d i) q
        rw [hqi, ← hr] at h1
        omega
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      have hp : (∏ j, ((d j / q).choose (k j) : ℂ)) = 0 :=
        prod_eq_zero (mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero])
      rw [hp, mul_zero]
    · intro hnot
      exact (hnot (mem_filter.mpr ⟨ha, rfl⟩)).elim
  rw [htop] at hz
  exact (MvPolynomial.mem_support_iff.mp ha) hz

#print axioms eq_zero_of_torsionMultiplicity_of_quotientOrder_lt

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
