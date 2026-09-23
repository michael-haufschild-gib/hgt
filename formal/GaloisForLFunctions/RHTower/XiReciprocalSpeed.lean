import GaloisForLFunctions.RHTower.CCMFirstRowVanDerCorputBlocks

/-!
# Controlled variation of the reciprocal phase speed

The exterior Liouville–Green phase speed `xi'(x) = sqrt((x²-s)/(x²-1))` is at least one on the
exterior range, and the corpus already owns that bound together with the speed's derivative.  What
an oscillatory integration by parts consumes is not the speed but its reciprocal: the antiderivative
of `A·exp(i c xi)` is `A/(i c xi')`, so the variation of `1/xi'` is what has to be controlled.

The reciprocal speed has derivative `-xi''/(xi')²`, and since the speed is at least one, that is
bounded by `x/(x²-1)²`, which is below `x^{-2}` from `x = 2` onward.  The estimate is exact, with
constant one, and uses no asymptotics.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The derivative of the reciprocal phase speed. -/
theorem hasDerivAt_inv_xiSpeed {s x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x) :
    HasDerivAt (fun u : ℝ => (xiSpeed s u)⁻¹)
      (-(x * (s - 1) / ((x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s x)) / (xiSpeed s x) ^ (2 : ℕ)) x := by
  have hpos : 0 < xiSpeed s x := lt_of_lt_of_le zero_lt_one (one_le_xiSpeed hs1 hx)
  exact (hasDerivAt_xiSpeed hs1 hx).inv (ne_of_gt hpos)

/-- **Controlled variation of the reciprocal speed.**  On the exterior range the derivative of
`1/xi'` is bounded by `x^{-2}`, with constant one. -/
theorem abs_deriv_inv_xiSpeed_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : 2 ≤ x) :
    |(-(x * (s - 1) / ((x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s x)) / (xiSpeed s x) ^ (2 : ℕ))| ≤ 1 / x ^ (2 : ℕ) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hV : 1 ≤ xiSpeed s x := one_le_xiSpeed hs1 hx1
  have hVpos : 0 < xiSpeed s x := lt_of_lt_of_le zero_lt_one hV
  have hV3 : 1 ≤ (xiSpeed s x) ^ (3 : ℕ) := one_le_pow₀ hV
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hval : -(x * (s - 1) / ((x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s x)) / (xiSpeed s x) ^ (2 : ℕ)
      = x * (1 - s) / ((x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * (xiSpeed s x) ^ (3 : ℕ)) := by
    field_simp
    ring
  have hnum : 0 ≤ x * (1 - s) := mul_nonneg hx0.le (by linarith)
  have hden : (0 : ℝ) < (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * (xiSpeed s x) ^ (3 : ℕ) := by positivity
  rw [hval, abs_of_nonneg (div_nonneg hnum hden.le)]
  have hstep : x * (1 - s) / ((x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * (xiSpeed s x) ^ (3 : ℕ)) ≤ x / (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have h1 : 0 ≤ x * (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * s :=
      mul_nonneg (mul_nonneg hx0.le (sq_nonneg _)) hs0
    have h2 : 0 ≤ x * (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) * ((xiSpeed s x) ^ (3 : ℕ) - 1) :=
      mul_nonneg (mul_nonneg hx0.le (sq_nonneg _)) (by linarith)
    nlinarith [h1, h2]
  have hfinal : x / (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) ≤ 1 / x ^ (2 : ℕ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx))
      (by linarith : (0 : ℝ) ≤ x + 1)]
  linarith

end GaloisForLFunctions.RHTower
