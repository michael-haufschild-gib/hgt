import GaloisForLFunctions.RHTower.CCMRadialProfileAsymptotic

/-!
# Decay of the leading cosine amplitude

The corpus bridges the regular Bessel profile to its leading cosine form with amplitude
`sqrt(2/pi) * ampFourth s x`, where `ampFourth s x = ((x²-1)(x²-s))^{-1/4}`.  That amplitude decays
like `x^{-1}`, so written in the normalization `a(x)/sqrt x` used by the exterior oscillatory
estimate the amplitude `a` decays like `x^{-1/2}` — which is exactly the hypothesis of that
estimate.

This is the amplitude half of the two-branch exterior expansion, for the *leading* form rather than
for the Bessel form.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **The leading amplitude decays like `1/x`.** -/
theorem ampFourth_le_two_div {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    ampFourth s x ≤ 2 / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hprod : (0 : ℝ) < (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := mul_pos hd hn
  -- the quartic lower bound
  have hquart : x ^ (4 : ℕ) / 16 ≤ (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := by
    nlinarith [hx, hs1, hs0, sq_nonneg x, sq_nonneg (x ^ (2 : ℕ))]
  have hinner : x ^ (2 : ℕ) / 4 ≤ Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := by
    have h1 : Real.sqrt ((x ^ (2 : ℕ) / 4) ^ (2 : ℕ)) ≤ Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) :=
      Real.sqrt_le_sqrt (by nlinarith [hquart])
    rwa [Real.sqrt_sq (by positivity)] at h1
  have houter : x / 2 ≤ Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) := by
    have h1 : Real.sqrt ((x / 2) ^ (2 : ℕ))
        ≤ Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) :=
      Real.sqrt_le_sqrt (by nlinarith [hinner])
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hpos : (0 : ℝ) < Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hprod)
  rw [ampFourth, div_le_div_iff₀ hpos hx0]
  nlinarith [houter, hx0]

/-- The same bound in the normalization the exterior estimate uses: `a(x) = sqrt x * amplitude`
decays like `x^{-1/2}`. -/
theorem sqrt_mul_ampFourth_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    Real.sqrt x * ampFourth s x ≤ 2 / Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have h := ampFourth_le_two_div hs0 hs1 hx
  have hstep : Real.sqrt x * ampFourth s x ≤ Real.sqrt x * (2 / x) :=
    mul_le_mul_of_nonneg_left h hsx.le
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  linarith [hss]

/-- The algebraic identity behind the quarter-root derivative, with the square relation abstracted
so that no rewriting loops through the radicands. -/
theorem quarter_root_deriv_identity {N P p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hpp : p * p = P) :
    -(N / (2 * p) / (2 * q)) / p = -N / (4 * P) * q⁻¹ := by
  rw [← hpp]
  field_simp
  ring

/-- The derivative of the leading amplitude, in logarithmic form. -/
theorem hasDerivAt_ampFourth {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (ampFourth s)
      (-(2 * x * (2 * x ^ (2 : ℕ) - s - 1)) / (4 * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) * ampFourth s x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := mul_pos hd hn
  have hsP : (0 : ℝ) < Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := Real.sqrt_pos.mpr hP
  have hssP : (0 : ℝ) < Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) :=
    Real.sqrt_pos.mpr hsP
  have hPP : Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))
      = (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := Real.mul_self_sqrt hP.le
  have hSS : Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))
      * Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))
      = Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := Real.mul_self_sqrt hsP.le
  -- the polynomial and its derivative
  have hpoly : HasDerivAt (fun u : ℝ => (u ^ (2 : ℕ) - 1) * (u ^ (2 : ℕ) - s))
      (2 * x * (2 * x ^ (2 : ℕ) - s - 1)) x := by
    have h1 : HasDerivAt (fun u : ℝ => u ^ (2 : ℕ) - 1) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const 1
    have h2 : HasDerivAt (fun u : ℝ => u ^ (2 : ℕ) - s) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const s
    have h := h1.mul h2
    have hv : 2 * x * (x ^ (2 : ℕ) - s) + (x ^ (2 : ℕ) - 1) * (2 * x) = 2 * x * (2 * x ^ (2 : ℕ) - s - 1) := by
      ring
    rwa [hv] at h
  -- one square root
  have hsqrt1 : HasDerivAt (fun u : ℝ => Real.sqrt ((u ^ (2 : ℕ) - 1) * (u ^ (2 : ℕ) - s)))
      (2 * x * (2 * x ^ (2 : ℕ) - s - 1) / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))) x := by
    have h := (Real.hasDerivAt_sqrt (ne_of_gt hP)).comp x hpoly
    have hv : 1 / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) * (2 * x * (2 * x ^ (2 : ℕ) - s - 1))
        = 2 * x * (2 * x ^ (2 : ℕ) - s - 1) / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) := by
      ring
    rwa [hv] at h
  -- the second square root
  have hsqrt2 : HasDerivAt (fun u : ℝ => Real.sqrt (Real.sqrt ((u ^ (2 : ℕ) - 1) * (u ^ (2 : ℕ) - s))))
      (2 * x * (2 * x ^ (2 : ℕ) - s - 1) / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))
        / (2 * Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))))) x := by
    have h := (Real.hasDerivAt_sqrt (ne_of_gt hsP)).comp x hsqrt1
    have hv : 1 / (2 * Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))))
          * (2 * x * (2 * x ^ (2 : ℕ) - s - 1) / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))))
        = 2 * x * (2 * x ^ (2 : ℕ) - s - 1) / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))
          / (2 * Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))) := by
      ring
    rwa [hv] at h
  -- invert
  have hinv := hsqrt2.inv (ne_of_gt hssP)
  have hval : -(2 * x * (2 * x ^ (2 : ℕ) - s - 1) / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))
        / (2 * Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))))
      / Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) ^ (2 : ℕ)
      = -(2 * x * (2 * x ^ (2 : ℕ) - s - 1)) / (4 * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))
        * (Real.sqrt (Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))))⁻¹ := by
    rw [Real.sq_sqrt hsP.le]
    exact quarter_root_deriv_identity (ne_of_gt hsP) (ne_of_gt hssP) hPP
  rw [hval] at hinv
  have hgoal : ampFourth s
      = fun u : ℝ => (Real.sqrt (Real.sqrt ((u ^ (2 : ℕ) - 1) * (u ^ (2 : ℕ) - s))))⁻¹ := by
    funext u
    rw [ampFourth, one_div]
  rw [hgoal]
  exact hinv

/-- **The derivative half of the leading amplitude bound.** -/
theorem abs_deriv_ampFourth_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |-(2 * x * (2 * x ^ (2 : ℕ) - s - 1)) / (4 * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) * ampFourth s x|
      ≤ 32 / x ^ (2 : ℕ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := mul_pos hd hn
  have hquart : x ^ (4 : ℕ) / 16 ≤ (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := by
    nlinarith [hx, hs1, hs0, sq_nonneg x, sq_nonneg (x ^ (2 : ℕ))]
  have hamp := ampFourth_le_two_div hs0 hs1 hx
  have hamp0 : 0 < ampFourth s x := ampFourth_pos hs1 (by linarith)
  have hnum : |(-(2 * x * (2 * x ^ (2 : ℕ) - s - 1)))| ≤ 4 * x ^ (3 : ℕ) := by
    rw [abs_neg, abs_of_nonneg (by nlinarith [hx0, hx, hs1])]
    nlinarith [hx0, hs0, hx]
  have hfrac : |-(2 * x * (2 * x ^ (2 : ℕ) - s - 1)) / (4 * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))|
      ≤ 16 / x := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))),
      div_le_div_iff₀ (by positivity) hx0]
    nlinarith [hnum, hquart, hx0]
  rw [abs_mul, abs_of_pos hamp0]
  have hstep : |-(2 * x * (2 * x ^ (2 : ℕ) - s - 1)) / (4 * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))|
      * ampFourth s x ≤ 16 / x * (2 / x) :=
    mul_le_mul hfrac hamp hamp0.le (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring


end GaloisForLFunctions.RHTower
