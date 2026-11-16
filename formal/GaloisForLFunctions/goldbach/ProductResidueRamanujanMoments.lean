import GaloisForLFunctions.goldbach.ProductResidueProfile
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.RamanujanTupleMoments

/-!
# Ramanujan moments of the multiplication profile

The multiplication profile has gcd Fourier coefficients. Pairing it with
any Ramanujan power therefore counts unit tuples with the gcd weight of
their additive sum. All nonunit fibers survive, and every weighted moment
is a nonnegative integer multiple of the modulus.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.Goldbach
open ArithmeticHarmonicAnalysis
noncomputable section

/-- The multiplication profile weights additive unit tuples by their exact gcd multiplicity. -/
theorem productResidueCount_ramanujan_moment (q : ℕ+) (k : ℕ) :
    (∑ r : ZMod (q : ℕ), (productResidueCount q r : ℂ) *
      _root_.RHTower.cglRamanujanAdditiveSum ⟨q, q.pos⟩ r ^ k) =
      ((q : ℕ) : ℂ) * ∑ t : ZMod (q : ℕ), (Nat.gcd (q : ℕ) t.val : ℂ) *
        unitTupleCount q (fun _ : Fin k => 1) t := by
  classical
  have ht (t : ZMod (q : ℕ)) :
      (∑ r : ZMod (q : ℕ),
        _root_.RHTower.cglRamanujanAdditiveSum ⟨q, q.pos⟩ r ^ k *
          ZMod.stdAddChar (-(r * t))) =
        ((q : ℕ) : ℂ) * unitTupleCount q (fun _ : Fin k => 1) t := by
    simpa only [mul_one, prod_const, card_univ, Fintype.card_fin] using
      sum_ramanujan_product_character (q : ℕ) (fun _ : Fin k => 1) t
  simp_rw [productResidueCount_eq_gcdFourier, sum_mul]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro t _
  calc
    _ = (Nat.gcd (q : ℕ) t.val : ℂ) *
        ∑ r : ZMod (q : ℕ),
          _root_.RHTower.cglRamanujanAdditiveSum ⟨q, q.pos⟩ r ^ k *
            ZMod.stdAddChar (-(r * t)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      rw [mul_comm t r]
      ring
    _ = _ := by rw [ht]; ring

/-- Every multiplication-weighted moment is an exact nonnegative multiple of the modulus. -/
theorem productResidueCount_ramanujan_moment_is_nat (q : ℕ+) (k : ℕ) :
    ∃ n : ℕ,
      (∑ r : ZMod (q : ℕ), (productResidueCount q r : ℂ) *
        _root_.RHTower.cglRamanujanAdditiveSum ⟨q, q.pos⟩ r ^ k) =
        ((q : ℕ) * n : ℕ) := by
  refine ⟨∑ t : ZMod (q : ℕ), Nat.gcd (q : ℕ) t.val *
    unitTupleCount q (fun _ : Fin k => 1) t, ?_⟩
  rw [productResidueCount_ramanujan_moment]
  simp only [Nat.cast_mul, Nat.cast_sum]

/-- Balanced product intervals retain every weighted moment with their exact square multiplicity. -/
theorem balancedProductResidueCount_ramanujan_moment (q : ℕ+) (b k : ℕ) :
    (∑ r : ZMod (q : ℕ), (balancedProductResidueCount q b r : ℂ) *
      _root_.RHTower.cglRamanujanAdditiveSum ⟨q, q.pos⟩ r ^ k) =
      (b : ℂ) ^ 2 * ((q : ℕ) : ℂ) *
        ∑ t : ZMod (q : ℕ), (Nat.gcd (q : ℕ) t.val : ℂ) *
          unitTupleCount q (fun _ : Fin k => 1) t := by
  simp_rw [balancedProductResidueCount_eq, Nat.cast_mul, Nat.cast_pow, mul_assoc]
  rw [← mul_sum, productResidueCount_ramanujan_moment, mul_assoc]

#print axioms productResidueCount_ramanujan_moment
#print axioms productResidueCount_ramanujan_moment_is_nat
#print axioms balancedProductResidueCount_ramanujan_moment

end
end GaloisForLFunctions.Goldbach
