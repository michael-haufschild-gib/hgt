import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalDelayedChargeFactorialAbelBridge

/-!
# Monotone Abel form of the literal critical CCM--FU profile

The complete FU endpoint-plus-curvature coefficient is one explicit profile.  On its literal
active clock it is strictly decreasing.  Thus finite Abel summation expresses the complete
profile-weighted prime--polar source as a positive-decrement functional of the same exact
Chebyshev--factorial prefix.  This is a structural identity, not a bound for that signed
functional.
-/

open Set

namespace RHTower

noncomputable section

/-- The literal FU profile has strictly negative derivative on its complete active clock. -/
theorem cauchyVolterraFUProfileDeriv_neg_on_active
    {H y : ℝ} (hH : 0 < H) (hy : 1 < y) (hyH : 2 * Real.log y ≤ H) :
    cauchyVolterraFUProfileDeriv H y < 0 := by
  let t : ℝ := Real.log y
  have hy0 : 0 < y := by linarith
  have ht : 0 < t := by
    simpa only [t] using Real.log_pos hy
  have htH : 2 * t ≤ H := by
    simpa only [t] using hyH
  let u : ℝ := H / 2 - t
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    linarith
  have huH : 2 * u ≤ H := by
    dsimp only [u]
    linarith
  have huSq : 2 * u ^ (2 : ℕ) ≤ H * u := by
    nlinarith
  have hnum : 2 * t ^ (2 : ℕ) + (4 - H) * t - 3 * H < 0 := by
    have hrearrange :
        2 * t ^ (2 : ℕ) + (4 - H) * t - 3 * H =
          -H - (H + 4) * u + 2 * u ^ (2 : ℕ) := by
      dsimp only [u]
      ring
    rw [hrearrange]
    nlinarith
  have hformula : cauchyVolterraFUProfileDeriv H y =
      4 * (2 * t ^ (2 : ℕ) + (4 - H) * t - 3 * H) /
        (y ^ (2 : ℕ) * H * t ^ (4 : ℕ)) := by
    unfold cauchyVolterraFUProfileDeriv
    dsimp only [t]
    field_simp [hH.ne', hy0.ne', ht.ne']
    ring
  rw [hformula]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hnum) (by positivity)

/-- The complete FU profile is strictly decreasing on the literal active interval. -/
theorem cauchyVolterraFUProfile_strictAntiOn_active
    {H : ℝ} (hH : 0 < H) :
    StrictAntiOn (cauchyVolterraFUProfile H)
      (Ioc 1 (Real.exp (H / 2))) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
  · intro y hy
    exact (hasDerivAt_cauchyVolterraFUProfile hH.ne'
      (ne_of_gt (by linarith [hy.1]))
      (ne_of_gt (Real.log_pos hy.1))).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    have hy0 : 0 < y := lt_trans zero_lt_one hy.1
    have hlogH : 2 * Real.log y ≤ H := by
      have hlog : Real.log y < H / 2 := by
        rw [← Real.log_exp (H / 2)]
        exact Real.strictMonoOn_log hy0 (Real.exp_pos _) hy.2
      linarith
    rw [(hasDerivAt_cauchyVolterraFUProfile hH.ne' hy0.ne'
      (ne_of_gt (Real.log_pos hy.1))).deriv]
    exact cauchyVolterraFUProfileDeriv_neg_on_active hH hy.1 hlogH

/-- Successive values of the literal FU profile have nonnegative decrement on its active clock. -/
theorem cauchyVolterraFUProfile_sub_nonneg_on_active
    {H x z : ℝ} (hH : 0 < H)
    (hx : x ∈ Ioc 1 (Real.exp (H / 2)))
    (hz : z ∈ Ioc 1 (Real.exp (H / 2))) (hxz : x ≤ z) :
    0 ≤ cauchyVolterraFUProfile H x - cauchyVolterraFUProfile H z := by
  exact sub_nonneg.mpr
    ((cauchyVolterraFUProfile_strictAntiOn_active hH).antitoneOn hx hz hxz)

/-- Exact Abel form of the complete finite profile-weighted critical FU source. -/
theorem ccmFUSuzuki_criticalProfileCharge_eq_abelChebyshevFactorialPrefix
    (N : ℕ) (H : ℝ) :
    (∑ j ∈ Finset.range (N + 1),
      ccmFUSuzukiCriticalPrimePolarCoefficient j *
        cauchyVolterraFUProfile H (Real.sqrt ((j + 3 : ℕ) : ℝ))) =
      ccmFUSuzukiCriticalChebyshevFactorialPrefix N *
        cauchyVolterraFUProfile H (Real.sqrt ((N + 3 : ℕ) : ℝ)) +
      ∑ j ∈ Finset.range N,
        ccmFUSuzukiCriticalChebyshevFactorialPrefix j *
          (cauchyVolterraFUProfile H (Real.sqrt ((j + 3 : ℕ) : ℝ)) -
            cauchyVolterraFUProfile H (Real.sqrt ((j + 4 : ℕ) : ℝ))) := by
  rw [deningerAbelSummation]
  change ccmFUSuzukiCriticalPrimePolarPrefix N *
      cauchyVolterraFUProfile H (Real.sqrt ((N + 3 : ℕ) : ℝ)) +
    ∑ j ∈ Finset.range N,
      ccmFUSuzukiCriticalPrimePolarPrefix j *
        (cauchyVolterraFUProfile H (Real.sqrt ((j + 3 : ℕ) : ℝ)) -
          cauchyVolterraFUProfile H (Real.sqrt ((j + 4 : ℕ) : ℝ))) = _
  simp_rw [ccmFUSuzuki_criticalPrimePolarPrefix_eq_chebyshevFactorial]

end

end RHTower
