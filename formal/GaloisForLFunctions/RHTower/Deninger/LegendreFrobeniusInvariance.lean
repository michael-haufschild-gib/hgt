import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusRingEndomorphism

/-!
# Frobenius factors invisible to differential normalization

In characteristic `p`, a factor `g(T^p)` has zero derivative. The Legendre weight-two
operator therefore carries that factor unchanged, while the big-Witt logarithmic
ghost forgets it. These are two forms of the same differential cancellation.
-/

namespace RHTower

noncomputable section

open PowerSeries

variable {A : Type*} [CommRing A]

/-- The weight-two Legendre operator on formal power series. -/
def legendreSeriesOperator (f : PowerSeries A) : PowerSeries A :=
  (1 - 2 * X) * f + 6 * X * (1 - X) * derivative A f

/-- Frobenius substitution is killed by formal differentiation in its characteristic. -/
theorem derivative_expand_char (p : ℕ) [CharP A p] (hp : p ≠ 0)
    (g : PowerSeries A) : derivative A (expand p hp g) = 0 := by
  rw [deningerPowerSeriesDerivative_expand, CharP.cast_eq_zero, zero_mul, mul_zero]

/-- Differential normalization retains an undifferentiated Frobenius factor. -/
theorem legendreSeriesOperator_mul_expand (p : ℕ) [CharP A p] (hp : p ≠ 0)
    (f g : PowerSeries A) :
    legendreSeriesOperator (f * expand p hp g) =
      expand p hp g * legendreSeriesOperator f := by
  simp only [legendreSeriesOperator, derivative_mul, derivative_expand_char,
    mul_zero, add_zero]
  ring

/-- The actual big-Witt ghost is unchanged by multiplication by a Frobenius-expanded unit. -/
theorem deningerBigWittLogGhost_mul_expand_char (p : ℕ) [CharP A p] (hp : p ≠ 0)
    (w v : DeningerBigWittRing A) :
    deningerBigWittLogGhost
        (deningerBigWittRingSeries w * expand p hp (deningerBigWittRingSeries v))
        (by rw [map_mul, constantCoeff_expand, deningerBigWittSeries_constantCoeff,
          deningerBigWittSeries_constantCoeff, mul_one]) =
      deningerBigWittLogGhost (deningerBigWittRingSeries w)
        (deningerBigWittSeries_constantCoeff w) := by
  rw [deningerBigWittLogGhost_mul _ _ (deningerBigWittSeries_constantCoeff w)
    (by rw [constantCoeff_expand, deningerBigWittSeries_constantCoeff]),
    deningerBigWittLogGhost_expand p hp _ (deningerBigWittSeries_constantCoeff v),
    CharP.cast_eq_zero, map_zero, zero_mul, add_zero]

end

end RHTower
