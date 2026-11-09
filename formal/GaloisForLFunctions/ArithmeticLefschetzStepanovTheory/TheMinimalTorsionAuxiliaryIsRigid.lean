import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionQuotientDetection
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovCountOfTheClosedPoints

/-!
# The minimal torsion auxiliary is rigid

Full multiplicity `r` on the order-`q` torsion locus costs length `2^(qr)`.
At equality there is only one auxiliary up to an integer scalar:
`(u₂^q - 1)^r`. Subtracting its top coefficient leaves quotient support
strictly below `r`, which Fourier–Euler extraction detects.
-/

open MvPolynomial Finset

noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open ArithmeticHarmonicAnalysis
variable {P : Finset Nat.Primes}

/-- Quotient order is bounded by the arithmetic weight of an exponent. -/
theorem two_pow_quotientOrder_le_weight (q : ℕ) (a : P →₀ ℕ) :
    2 ^ (q * torsionQuotientOrder q a) ≤ weight a := by
  calc
    _ = ∏ p : P, 2 ^ (q * (a p / q)) := by
      rw [torsionQuotientOrder, mul_sum, ← prod_pow_eq_pow_sum]
    _ ≤ ∏ p : P, 2 ^ a p := prod_le_prod' fun p _ =>
      Nat.pow_le_pow_right (by omega) (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (a p) q)
    _ ≤ weight a := prod_le_prod' fun p _ => Nat.pow_le_pow_left (p : Nat.Primes).2.two_le _

/-- Strictly subcritical arithmetic support cannot have full torsion multiplicity. -/
theorem eq_zero_of_length_lt_torsionMultiplicity (q r : ℕ) [NeZero q]
    (F : MvPolynomial P ℤ) (hlen : length F < 2 ^ (q * r))
    (hmult : ∀ t : P → ZMod q,
      MvPolynomial.map (Int.castRingHom ℂ) F ∈
        vanishingIdeal ℂ {fun p => ZMod.stdAddChar (t p)} ^ r) : F = 0 := by
  have hz := eq_zero_of_torsionMultiplicity_of_quotientOrder_lt q r
    (MvPolynomial.map (Int.castRingHom ℂ) F) ?_ hmult
  · exact (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective)
      (by simpa only [map_zero] using hz)
  · intro a ha
    have haF : a ∈ F.support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at ha
      exact MvPolynomial.mem_support_iff.mpr fun h => ha (by rw [h, map_zero])
    have hlt := (two_pow_quotientOrder_le_weight q a).trans_lt
      ((le_sup (f := weight) haF).trans_lt hlen)
    have hqr := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt
    exact (Nat.mul_lt_mul_left (NeZero.pos q)).mp hqr

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
