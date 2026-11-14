import GaloisForLFunctions.HTGeometry.HypergeometricSpatialJets

/-!
# The Riccati equation of the Legendre period

For the actual Gauss series `F = ₂F₁(1/2,1/2;1;z)`, the Picard--Fuchs equation gives
`A = (1-2z)F + 6z(1-z)F'` and `A' = (1-2z)F' - F/2`. Their Wronskian yields a
denominator-free Riccati identity on the whole unit disk and the usual equation for
`A/F` wherever the period is nonzero.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LegendrePeriod

open Complex RHTower

def period (z : ℂ) : ℂ := ordinaryHypergeometric (1 / 2) (1 / 2) 1 z

def slope (z : ℂ) : ℂ :=
  ordinaryHypergeometricFirstDerivativeSeriesValue (1 / 2) (1 / 2) 1 z

def curvature (z : ℂ) : ℂ :=
  ordinaryHypergeometricSecondDerivativeSeriesValue (1 / 2) (1 / 2) 1 z

def numerator (z : ℂ) : ℂ :=
  (1 - 2 * z) * period z + 6 * (z * (1 - z)) * slope z

def normalized (z : ℂ) : ℂ := numerator z / period z

theorem hasDerivAt_period (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt period (slope z) z := by
  exact ((ordinaryHypergeometricSeries ℂ (1 / 2) (1 / 2) 1).hasFDerivAt_sum
    (hz.trans_le (hypergeometric_radius_one_le _ _ _))).hasDerivAt

theorem hasDerivAt_slope (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt slope (curvature z) z := by
  let p := ordinaryHypergeometricSeries ℂ (1 / 2) (1 / 2) 1
  have hzp : ‖z‖ₑ < p.radius := hz.trans_le (hypergeometric_radius_one_le _ _ _)
  have h := p.derivSeries.hasFDerivAt_sum
    (hzp.trans_le p.radius_le_radius_derivSeries)
  exact (h.clm_apply (hasFDerivAt_const (1 : ℂ) z)).hasDerivAt

/-- The analytic Legendre Picard--Fuchs equation, derived from the convergent Gauss series. -/
theorem picardFuchs (z : ℂ) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) * curvature z + (1 - 2 * z) * slope z - period z / 4 = 0 := by
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -(1 : ℂ) := by
    intro j hj
    have hr := congrArg Complex.re hj
    simp only [Complex.natCast_re, Complex.neg_re, Complex.one_re] at hr
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have h := ordinaryHypergeometric_standardGaussODE (1 / 2) (1 / 2) 1 z hc
    (hz.trans_le (hypergeometric_radius_one_le _ _ _))
  change z * (1 - z) * curvature z +
    (1 - ((1 / 2 : ℂ) + 1 / 2 + 1) * z) * slope z -
      (1 / 2 : ℂ) * (1 / 2) * period z = 0 at h
  linear_combination h

/-- The first-order operator turns the second-order period equation into a two-state system. -/
theorem hasDerivAt_numerator (z : ℂ) (hz : ‖z‖ₑ < 1) :
    HasDerivAt numerator ((1 - 2 * z) * slope z - period z / 2) z := by
  have hc : HasDerivAt (fun w : ℂ => 1 - 2 * w) (-2) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul 2) using 1 <;> ring
  have hh : HasDerivAt (fun w : ℂ => w * (1 - w)) (1 - 2 * z) z := by
    convert (hasDerivAt_id z).mul
      ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)) using 1 <;> ring
  have h := (hc.mul (hasDerivAt_period z hz)).add
    ((hh.const_mul 6).mul (hasDerivAt_slope z hz))
  convert h using 1
  linear_combination -6 * picardFuchs z hz

/-- The Wronskian is a quadratic expression in the period and its first derivative. -/
theorem wronskian (z : ℂ) (hz : ‖z‖ₑ < 1) :
    deriv numerator z * period z - numerator z * slope z =
      -(period z ^ 2) / 2 - 6 * z * (1 - z) * slope z ^ 2 := by
  rw [(hasDerivAt_numerator z hz).deriv, numerator]
  ring

/-- Clearing the period denominator keeps the Riccati identity valid even at period zeros. -/
theorem riccati_cleared (z : ℂ) (hz : ‖z‖ₑ < 1) :
    6 * z * (1 - z) * (deriv numerator z * period z - numerator z * slope z) =
      -(numerator z ^ 2) + 2 * (1 - 2 * z) * numerator z * period z -
        (z ^ 2 - z + 1) * period z ^ 2 := by
  rw [wronskian z hz, numerator]
  ring

/-- The normalized Legendre period satisfies the Riccati equation on its regular locus. -/
theorem riccati (z : ℂ) (hz : ‖z‖ₑ < 1) (hF : period z ≠ 0) :
    6 * z * (1 - z) * deriv normalized z =
      -(normalized z ^ 2) + 2 * (1 - 2 * z) * normalized z - (z ^ 2 - z + 1) := by
  have hd := (hasDerivAt_numerator z hz).div (hasDerivAt_period z hz) hF
  change HasDerivAt normalized _ z at hd
  rw [hd.deriv, normalized]
  field_simp
  have h := riccati_cleared z hz
  rw [(hasDerivAt_numerator z hz).deriv] at h
  linear_combination h

/-- A multiple numerator zero at a nonzero period lies over the elliptic value `j = 0`. -/
theorem multiple_zero_obstruction (z : ℂ) (hz : ‖z‖ₑ < 1) :
    numerator z ≠ 0 ∨ deriv numerator z ≠ 0 ∨ period z = 0 ∨ z ^ 2 - z + 1 = 0 := by
  by_contra h
  push Not at h
  obtain ⟨hA, hdA, hF, hL⟩ := h
  have he := riccati_cleared z hz
  rw [hA, hdA] at he
  have hprod : (z ^ 2 - z + 1) * period z ^ 2 = 0 := by
    linear_combination he
  exact (mul_ne_zero hL (pow_ne_zero 2 hF)) hprod

end GaloisForLFunctions.HTGeometry.LegendrePeriod
