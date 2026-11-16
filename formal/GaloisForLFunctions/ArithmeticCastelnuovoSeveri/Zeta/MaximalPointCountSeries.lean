import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity

/-!
# Rational series for maximal extension counts

The sequence `(Q²)^n+1-m*(-Q)^n` is the ghost sequence of
`(1+QX)^m/((1-X)(1-Q²X))`. The formal identity applies directly to
actual extension counts once their signed formula is proved.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open PowerSeries

/-- Raising a series to a natural power multiplies its ghost series by that integer. -/
theorem hasGhost_pow {F G : PowerSeries ℂ} (h : HasGhost F G) (m : ℕ) :
    HasGhost (F ^ m) (m • G) := by
  induction m with
  | zero => simpa only [pow_zero, zero_nsmul] using hasGhost_one
  | succ m ih =>
    rw [pow_succ, add_nsmul, one_nsmul]
    exact hasGhost_mul ih h

/-- The formal series with maximal signed extension counts and zero constant term. -/
def maximalPointCountSeries (Q : ℂ) (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (Q ^ 2) ^ n + 1 - (m : ℂ) * (-Q) ^ n

/-- The rational formal series corresponding to repeated Frobenius eigenvalue `-Q`. -/
def maximalPointCountZeta (Q : ℂ) (m : ℕ) : PowerSeries ℂ :=
  geom 1 * geom (Q ^ 2) * (1 - C (-Q) * X) ^ m

/-- The signed extension-count formula is exactly the ghost series of the rational zeta expression. -/
theorem maximalPointCountZeta_hasGhost (Q : ℂ) (m : ℕ) :
    HasGhost (maximalPointCountZeta Q m) (maximalPointCountSeries Q m) := by
  have h := hasGhost_mul (hasGhost_mul (hasGhost_geom 1) (hasGhost_geom (Q ^ 2)))
    (hasGhost_pow (hasGhost_one_sub (-Q)) m)
  have hG : geomTail 1 + geomTail (Q ^ 2) + m • (-geomTail (-Q)) =
      maximalPointCountSeries Q m := by
    ext n
    simp only [maximalPointCountSeries, geomTail, coeff_mk, map_add, map_nsmul, map_neg]
    by_cases hn : n = 0
    · simp only [if_pos hn, neg_zero, nsmul_zero, add_zero]
    · simp only [if_neg hn, one_pow, nsmul_eq_mul]
      ring
  exact hG ▸ h

/-- The zeta expression has constant coefficient one. -/
theorem maximalPointCountZeta_constantCoeff (Q : ℂ) (m : ℕ) :
    constantCoeff (maximalPointCountZeta Q m) = 1 := by
  simp only [maximalPointCountZeta, map_mul, map_pow, map_sub, map_one,
    constantCoeff_C, constantCoeff_X, geom, constantCoeff_mk, pow_zero,
    mul_zero, sub_zero, one_pow, mul_one]

/-- The two pole factors cancel the geometric series, leaving the repeated linear numerator. -/
theorem maximalPointCountZeta_rational (Q : ℂ) (m : ℕ) :
    ((1 - X) * (1 - C (Q ^ 2) * X)) * maximalPointCountZeta Q m =
      (1 + C Q * X) ^ m := by
  have h1 : (1 - X) * geom 1 = 1 := by
    simpa only [map_one, one_mul] using one_sub_mul_geom (1 : ℂ)
  have hQ := one_sub_mul_geom (Q ^ 2)
  have hfactor : (1 - C (-Q) * X : PowerSeries ℂ) = 1 + C Q * X := by
    rw [map_neg]
    ring
  calc
    _ = ((1 - X) * geom 1) * ((1 - C (Q ^ 2) * X) * geom (Q ^ 2)) *
        (1 - C (-Q) * X) ^ m := by rw [maximalPointCountZeta]; ring
    _ = _ := by rw [h1, hQ, one_mul, one_mul, hfactor]

/-- These ghost coefficients and constant coefficient one uniquely determine the zeta series. -/
theorem maximalPointCountZeta_unique (Q : ℂ) (m : ℕ) (Z : PowerSeries ℂ)
    (h0 : constantCoeff Z = 1) (hZ : HasGhost Z (maximalPointCountSeries Q m)) :
    Z = maximalPointCountZeta Q m := by
  apply eq_of_hasGhost hZ (maximalPointCountZeta_hasGhost Q m)
  · exact h0.trans (maximalPointCountZeta_constantCoeff Q m).symm
  · rw [maximalPointCountSeries, constantCoeff_mk, if_pos rfl]

/-- For integral field size, every coefficient of the rational zeta series is an integer. -/
theorem maximalPointCountZeta_integral (Q m : ℕ) :
    ∃ Z : PowerSeries ℤ, constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Z = maximalPointCountZeta (Q : ℂ) m := by
  refine ⟨(PowerSeries.mk fun n => (1 : ℤ) ^ n) *
    (PowerSeries.mk fun n => ((Q : ℤ) ^ 2) ^ n) * (1 - C (-(Q : ℤ)) * X) ^ m, ?_, ?_⟩
  · simp only [map_mul, map_pow, map_sub, map_one, constantCoeff_mk, constantCoeff_C,
      constantCoeff_X, pow_zero, mul_zero, sub_zero, one_pow, mul_one]
  · simp only [maximalPointCountZeta, map_mul, map_pow, map_sub, map_one,
      PowerSeries.map_X, map_mk_pow,
      Int.cast_one, Int.cast_pow, map_neg, map_natCast, Int.cast_natCast]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
