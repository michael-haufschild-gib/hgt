import GaloisForLFunctions.HTGeometry.HardyCrossParseval
import GaloisForLFunctions.RHTower.BernsteinEllipseMixedModeGap

/-!
# Affine Bernstein-row cross moments

The normalized reflected circle moment is exactly the Hermitian pairing of the two finite
Bernstein coefficient rows.  This is the coefficient-level bridge needed to transfer a strict
mixed-mode circle gap into an exponentially smaller packet cross term.
-/

open Complex MeasureTheory
open scoped BigOperators Interval Real ComplexConjugate

namespace RHTower

noncomputable section

/-- One unweighted affine Bernstein row coefficient. -/
def bernsteinAffineRowCoefficient (u : ℂ) (n k : ℕ) : ℂ :=
  (n.choose k : ℂ) * u ^ k * (1 - u) ^ (n - k)

lemma sum_bernsteinAffineRowCoefficient_mul_pow
    (u w : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      bernsteinAffineRowCoefficient u n k * w ^ k) =
      (1 - u + u * w) ^ n := by
  rw [show 1 - u + u * w = u * w + (1 - u) by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [bernsteinAffineRowCoefficient, mul_pow]
  ring

/-- The reflected circle moment is exactly the Hermitian pairing of two affine Bernstein rows. -/
theorem reflectedBernsteinCrossMoment_eq_sum
    (u v : ℂ) (n : ℕ) :
    reflectedBernsteinCrossMoment u v n =
      ∑ k ∈ Finset.range (n + 1),
        bernsteinAffineRowCoefficient u n k *
          conj (bernsteinAffineRowCoefficient v n k) := by
  have hparseval :=
    GaloisForLFunctions.HTGeometry.circleAverage_poly_mul_conj
      (1 : ℝ) (n + 1)
      (bernsteinAffineRowCoefficient u n)
      (bernsteinAffineRowCoefficient v n)
  simp only [Complex.ofReal_one, one_pow, mul_one] at hparseval
  rw [← hparseval, reflectedBernsteinCrossMoment]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta _
  change reflectedBernsteinProduct u v (circleMap 0 1 theta) ^ n =
    (∑ k ∈ Finset.range (n + 1),
      bernsteinAffineRowCoefficient u n k * circleMap 0 1 theta ^ k) *
      conj (∑ j ∈ Finset.range (n + 1),
        bernsteinAffineRowCoefficient v n j * circleMap 0 1 theta ^ j)
  rw [sum_bernsteinAffineRowCoefficient_mul_pow,
    sum_bernsteinAffineRowCoefficient_mul_pow]
  rw [map_pow, ← mul_pow]
  congr 1
  rw [reflectedBernsteinProduct]
  congr 1
  simp

end

end RHTower
