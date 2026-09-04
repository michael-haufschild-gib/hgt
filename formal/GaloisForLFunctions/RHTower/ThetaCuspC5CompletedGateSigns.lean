import GaloisForLFunctions.RHTower.ThetaCuspCompletedCurvatureProjectiveFarTail
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5JacobianCompensation
import GaloisForLFunctions.RHTower.C5FixedActionDescentLemmas

/-!
# The two analytic hypotheses of the completed C5 gate from curvature sign facts

With `c = thetaCuspLogCurvature` (completed curvature, `c > 0`), `j = c'`, `j₂ = c''`,
`j₃ = c'''` (the corpus's curvature jets), and `σ = thetaCuspLogDecaySlope` (`σ' = c`), fix the
centre `u` and put

```text
e(s) = (c(u+s) + c(u−s))/2,   o(s) = (c(u+s) − c(u−s))/2,
E(s) = (σ(u+s) − σ(u−s))/2,   O(s) = (σ(u+s) + σ(u−s) − 2σ(u))/2,
```

so that `E' = e`, `O' = o`, `Φ_t = 2E`, `Φ_u = 2O`, `Φ_tt = 2e`, `Φ_ut = 2o`, and the completed
centre numerator is `H = 4(o·tE − O·(E + te))`.

* **Velocity floor.**  `c'' ≥ 0` on `[0, ∞)` makes `e` nondecreasing, `E` convex, and the chord
  bound gives `Φ = 2∫₀ᵗE ≤ tE(t)`, i.e. `v = tΦ_t ≥ 2Φ`.
* **Centre negativity.**  `c' > 0`, `c'' > 0` on the half-line and the projective inequality
  `c·c''' ≤ c'·c''` wherever `c''' ≥ 0` give the two-point inequality
  `(c''₊ − c''₋)[2(c₊ + c₋) + t(c'₊ − c'₋)] < (c'₊ + c'₋)[3(c'₊ − c'₋) + t(c''₊ + c''₋)]`, which is
  strict decrease of `o'/(2e + te')`; two monotone-l'Hospital descents then give `H < 0`.

Both statements take the sign facts as explicit hypotheses; proving those on the whole half-line
is the remaining special-function work of the card
`theta-c5-completed-compensation-direct-gate.md`.
-/

open Set

namespace RHTower

noncomputable section

/-- Even part of the completed curvature around the centre `u`. -/
def completedCurvatureEven (u s : ℝ) : ℝ :=
  (thetaCuspLogCurvature (u + s) + thetaCuspLogCurvature (u - s)) / 2

/-- Odd part of the completed curvature around the centre `u`. -/
def completedCurvatureOdd (u s : ℝ) : ℝ :=
  (thetaCuspLogCurvature (u + s) - thetaCuspLogCurvature (u - s)) / 2

/-- `E(s) = (σ(u+s) − σ(u−s))/2 = Φ_t/2`. -/
def completedDecayEvenPrimitive (u s : ℝ) : ℝ :=
  (thetaCuspLogDecaySlope (u + s) - thetaCuspLogDecaySlope (u - s)) / 2

/-- `O(s) = (σ(u+s) + σ(u−s) − 2σ(u))/2 = Φ_u/2`. -/
def completedDecayOddPrimitive (u s : ℝ) : ℝ :=
  (thetaCuspLogDecaySlope (u + s) + thetaCuspLogDecaySlope (u - s) -
    2 * thetaCuspLogDecaySlope u) / 2

theorem completedDecayEvenPrimitive_eq (u t : ℝ) :
    completedDecayEvenPrimitive u t = thetaCuspReflectedLogJetOne u t / 2 := by
  unfold completedDecayEvenPrimitive thetaCuspReflectedLogJetOne; ring

theorem completedDecayOddPrimitive_eq (u t : ℝ) :
    completedDecayOddPrimitive u t = thetaCuspReflectedLogCenterJetOne u t / 2 := by
  unfold completedDecayOddPrimitive thetaCuspReflectedLogCenterJetOne; ring

theorem completedCurvatureEven_eq (u t : ℝ) :
    completedCurvatureEven u t = thetaCuspReflectedLogJetTwo u t / 2 := by
  unfold completedCurvatureEven thetaCuspReflectedLogJetTwo; ring

theorem completedCurvatureOdd_eq (u t : ℝ) :
    completedCurvatureOdd u t = thetaCuspReflectedLogCenterMixedJetOne u t / 2 := by
  unfold completedCurvatureOdd thetaCuspReflectedLogCenterMixedJetOne; ring

theorem completedDecayEvenPrimitive_zero (u : ℝ) : completedDecayEvenPrimitive u 0 = 0 := by
  unfold completedDecayEvenPrimitive; simp

theorem completedDecayOddPrimitive_zero (u : ℝ) : completedDecayOddPrimitive u 0 = 0 := by
  unfold completedDecayOddPrimitive; simp; ring

theorem completedCurvatureOdd_zero (u : ℝ) : completedCurvatureOdd u 0 = 0 := by
  unfold completedCurvatureOdd; simp

theorem hasDerivAt_completedDecayEvenPrimitive (u s : ℝ) :
    HasDerivAt (completedDecayEvenPrimitive u) (completedCurvatureEven u s) s := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogDecaySlope (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have := (hp.sub hm).div_const 2
  unfold completedDecayEvenPrimitive completedCurvatureEven
  convert this using 1
  simp only [id_eq]; ring

theorem hasDerivAt_completedDecayOddPrimitive (u s : ℝ) :
    HasDerivAt (completedDecayOddPrimitive u) (completedCurvatureOdd u s) s := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogDecaySlope (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have := ((hp.add hm).sub_const (2 * thetaCuspLogDecaySlope u)).div_const 2
  unfold completedDecayOddPrimitive completedCurvatureOdd
  convert this using 1
  simp only [id_eq]; ring

theorem hasDerivAt_completedCurvatureEven (u s : ℝ) :
    HasDerivAt (completedCurvatureEven u)
      ((thetaCuspLogCurvatureJet (u + s) - thetaCuspLogCurvatureJet (u - s)) / 2) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvature (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvature (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have := (hp.add hm).div_const 2
  unfold completedCurvatureEven
  convert this using 1
  simp only [id_eq]; ring

theorem hasDerivAt_completedCurvatureOdd (u s : ℝ) :
    HasDerivAt (completedCurvatureOdd u)
      ((thetaCuspLogCurvatureJet (u + s) + thetaCuspLogCurvatureJet (u - s)) / 2) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvature (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvature (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have := (hp.sub hm).div_const 2
  unfold completedCurvatureOdd
  convert this using 1
  simp only [id_eq]; ring

/-- Even part of the curvature is positive. -/
theorem completedCurvatureEven_pos (u s : ℝ) : 0 < completedCurvatureEven u s := by
  unfold completedCurvatureEven
  have := thetaCuspLogCurvature_pos (u + s)
  have := thetaCuspLogCurvature_pos (u - s)
  linarith

/-- **Velocity floor from curvature convexity.**  If `c'' ≥ 0` on `[0, ∞)` then `2Φ ≤ v` for
`0 < t ≤ u`. -/
theorem two_mul_action_le_velocity_of_jetTwo_nonneg {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hR3 : ∀ x : ℝ, 0 ≤ x → 0 ≤ thetaCuspLogCurvatureJetTwo x) :
    2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t := by
  -- `E` is convex on `[0, t]`: its derivative `e` is nondecreasing there
  have hj_mono : MonotoneOn thetaCuspLogCurvatureJet (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro x _; exact (hasDerivAt_thetaCuspLogCurvatureJet x).continuousAt.continuousWithinAt
    · intro x _; exact (hasDerivAt_thetaCuspLogCurvatureJet x).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ici] at hx
      rw [(hasDerivAt_thetaCuspLogCurvatureJet x).deriv]; exact hR3 x hx.le
  have he_mono : MonotoneOn (completedCurvatureEven u) (Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
    · intro s _; exact (hasDerivAt_completedCurvatureEven u s).continuousAt.continuousWithinAt
    · intro s _; exact (hasDerivAt_completedCurvatureEven u s).differentiableAt.differentiableWithinAt
    · intro s hs; rw [interior_Icc] at hs
      rw [(hasDerivAt_completedCurvatureEven u s).deriv]
      have h1 : u - s ≤ u + s := by linarith [hs.1]
      have h0 : 0 ≤ u - s := by linarith [hs.2]
      have := hj_mono (mem_Ici.2 h0) (mem_Ici.2 (by linarith : (0:ℝ) ≤ u + s)) h1
      linarith
  have hconv : ConvexOn ℝ (Icc 0 t) (completedDecayEvenPrimitive u) := by
    refine MonotoneOn.convexOn_of_deriv (convex_Icc 0 t) ?_ ?_ ?_
    · intro s _; exact (hasDerivAt_completedDecayEvenPrimitive u s).continuousAt.continuousWithinAt
    · intro s _; exact (hasDerivAt_completedDecayEvenPrimitive u s).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro a ha b hb hab
      rw [(hasDerivAt_completedDecayEvenPrimitive u a).deriv,
        (hasDerivAt_completedDecayEvenPrimitive u b).deriv]
      exact he_mono (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) hab
  have hcont : ContinuousOn (completedDecayEvenPrimitive u) (Icc 0 t) :=
    fun s _ => (hasDerivAt_completedDecayEvenPrimitive u s).continuousAt.continuousWithinAt
  have hchord := two_mul_integral_le_mul_of_convexOn ht (completedDecayEvenPrimitive_zero u)
    hconv hcont
  -- `Φ = 2 ∫₀ᵗ E` by the fundamental theorem of calculus
  have hΦ : thetaCuspReflectedLogAction u t = 2 * ∫ s in (0 : ℝ)..t, completedDecayEvenPrimitive u s := by
    have hderiv : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt (thetaCuspReflectedLogAction u)
        (2 * completedDecayEvenPrimitive u s) s := by
      intro s _
      have := hasDerivAt_thetaCuspReflectedLogAction u s
      rw [completedDecayEvenPrimitive_eq]
      convert this using 1; ring
    have hint : IntervalIntegrable (fun s => 2 * completedDecayEvenPrimitive u s) MeasureTheory.volume 0 t :=
      ((hcont.const_smul (2 : ℝ)).intervalIntegrable_of_Icc ht.le)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hderiv s (uIcc_of_le ht.le ▸ hs)) hint
    rw [intervalIntegral.integral_const_mul] at hftc
    have h0 : thetaCuspReflectedLogAction u 0 = 0 := by
      unfold thetaCuspReflectedLogAction; simp; ring
    linarith
  rw [hΦ]
  unfold thetaCuspReflectedActionVelocity
  rw [show thetaCuspReflectedLogJetOne u t = 2 * completedDecayEvenPrimitive u t by
    rw [completedDecayEvenPrimitive_eq]; ring]
  linarith

/-! ## Centre negativity from the curvature sign facts -/

/-- `o'(s) = (j(u+s) + j(u−s))/2`, the numerator of the local ratio `r₃`. -/
def completedCurvatureOddJet (u s : ℝ) : ℝ :=
  (thetaCuspLogCurvatureJet (u + s) + thetaCuspLogCurvatureJet (u - s)) / 2

/-- `2e + s e'`, the denominator of the local ratio `r₃`. -/
def completedLocalDenominator (u s : ℝ) : ℝ :=
  2 * completedCurvatureEven u s +
    s * ((thetaCuspLogCurvatureJet (u + s) - thetaCuspLogCurvatureJet (u - s)) / 2)

theorem hasDerivAt_completedCurvatureOddJet (u s : ℝ) :
    HasDerivAt (completedCurvatureOddJet u)
      ((thetaCuspLogCurvatureJetTwo (u + s) - thetaCuspLogCurvatureJetTwo (u - s)) / 2) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have := (hp.add hm).div_const 2
  unfold completedCurvatureOddJet
  convert this using 1
  simp only [id_eq]; ring

theorem hasDerivAt_completedLocalDenominator (u s : ℝ) :
    HasDerivAt (completedLocalDenominator u)
      (3 * ((thetaCuspLogCurvatureJet (u + s) - thetaCuspLogCurvatureJet (u - s)) / 2) +
        s * ((thetaCuspLogCurvatureJetTwo (u + s) + thetaCuspLogCurvatureJetTwo (u - s)) / 2)) s := by
  have he := (hasDerivAt_completedCurvatureEven u s).const_mul 2
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u + s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u - s)).comp s ((hasDerivAt_id s).const_sub u)
  have hdiff := (hp.sub hm).div_const 2
  have hprod := (hasDerivAt_id s).mul hdiff
  have := he.add hprod
  unfold completedLocalDenominator
  convert this using 1
  simp only [id_eq]; ring

/-- `E(s) + s e(s)`, the first-descent denominator. -/
def completedFirstDenominator (u s : ℝ) : ℝ :=
  completedDecayEvenPrimitive u s + s * completedCurvatureEven u s

theorem hasDerivAt_completedFirstDenominator (u s : ℝ) :
    HasDerivAt (completedFirstDenominator u) (completedLocalDenominator u s) s := by
  have h1 := hasDerivAt_completedDecayEvenPrimitive u s
  have h2 := (hasDerivAt_id s).mul (hasDerivAt_completedCurvatureEven u s)
  have := h1.add h2
  unfold completedFirstDenominator completedLocalDenominator
  convert this using 1
  simp only [id_eq]; ring

theorem hasDerivAt_mul_completedDecayEvenPrimitive (u s : ℝ) :
    HasDerivAt (fun s => s * completedDecayEvenPrimitive u s) (completedFirstDenominator u s) s := by
  have := (hasDerivAt_id s).mul (hasDerivAt_completedDecayEvenPrimitive u s)
  unfold completedFirstDenominator
  convert this using 1
  simp only [id_eq]; ring

/-- The two-point inequality `(∗)`: strict decrease of the local ratio `o'/(2e + se')`. -/
theorem local_ratio_deriv_neg {u s : ℝ} (hs : 0 < s) (hsu : s ≤ u)
    (hR2 : ∀ x : ℝ, 0 < x → 0 < thetaCuspLogCurvatureJet x)
    (hR3 : ∀ x : ℝ, 0 ≤ x → 0 < thetaCuspLogCurvatureJetTwo x)
    (hR4 : ∀ x : ℝ, 0 ≤ x → 0 ≤ thetaCuspLogCurvatureJetThree x →
      thetaCuspLogCurvature x * thetaCuspLogCurvatureJetThree x ≤
        thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo x) :
    ((thetaCuspLogCurvatureJetTwo (u + s) - thetaCuspLogCurvatureJetTwo (u - s)) / 2) *
        completedLocalDenominator u s -
      completedCurvatureOddJet u s *
        (3 * ((thetaCuspLogCurvatureJet (u + s) - thetaCuspLogCurvatureJet (u - s)) / 2) +
          s * ((thetaCuspLogCurvatureJetTwo (u + s) + thetaCuspLogCurvatureJetTwo (u - s)) / 2)) < 0 := by
  set y := u - s with hy
  set x := u + s with hx
  have hy0 : 0 ≤ y := by linarith
  have hyx : y ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  -- the two-point curvature gain at `(y, x)`
  have hQ := twoPointCurvatureGain_nonneg (c := thetaCuspLogCurvature) (c₁ := thetaCuspLogCurvatureJet)
    (c₂ := thetaCuspLogCurvatureJetTwo) (c₃ := thetaCuspLogCurvatureJetThree) (y := y)
    (fun z _ => hasDerivAt_thetaCuspLogCurvature z)
    (fun z _ => hasDerivAt_thetaCuspLogCurvatureJet z)
    (fun z _ => hasDerivAt_thetaCuspLogCurvatureJetTwo z)
    (fun z _ => thetaCuspLogCurvature_pos z)
    (fun z hz => by
      rcases eq_or_lt_of_le hz with h | h
      · rw [← h]
        have h1 := hR2 (y + 1) (by linarith)
        -- `j ≥ 0` at `y` follows from monotonicity; here we only need `0 ≤ j y`
        have hmono : MonotoneOn thetaCuspLogCurvatureJet (Ici 0) := by
          refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
          · intro w _; exact (hasDerivAt_thetaCuspLogCurvatureJet w).continuousAt.continuousWithinAt
          · intro w _; exact (hasDerivAt_thetaCuspLogCurvatureJet w).differentiableAt.differentiableWithinAt
          · intro w hw; rw [interior_Ici] at hw
            rw [(hasDerivAt_thetaCuspLogCurvatureJet w).deriv]; exact (hR3 w hw.le).le
        rcases eq_or_lt_of_le hy0 with h0 | h0
        · -- `j 0 = 0` by oddness
          have hodd := thetaCuspLogCurvatureJet_neg 0
          rw [neg_zero] at hodd
          rw [← h0]; linarith
        · exact (hR2 y (by rw [h] at h0; exact h0)).le
      · exact (hR2 z (lt_of_le_of_lt hy0 h)).le)
    (fun z hz => (hR3 z (le_trans hy0 hz)).le)
    (fun z hz h3 => hR4 z (le_trans hy0 hz) h3)
    x hyx
  unfold twoPointCurvatureGain at hQ
  unfold completedLocalDenominator completedCurvatureOddJet completedCurvatureEven
  -- the `s`-term: `2s(j₊ j₂₋ + j₂₊ j₋) > 0`
  have hj₊ : 0 < thetaCuspLogCurvatureJet x := hR2 x hxpos
  have hj₂₋ : 0 < thetaCuspLogCurvatureJetTwo y := hR3 y hy0
  have hj₋ : 0 ≤ thetaCuspLogCurvatureJet y := by
    rcases eq_or_lt_of_le hy0 with h0 | h0
    · have hodd := thetaCuspLogCurvatureJet_neg 0
      rw [neg_zero] at hodd
      rw [← h0]; linarith
    · exact (hR2 y h0).le
  have hj₂₊ : 0 < thetaCuspLogCurvatureJetTwo x := hR3 x hxpos.le
  have hgain : 0 < 2 * s * (thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo y +
      thetaCuspLogCurvatureJetTwo x * thetaCuspLogCurvatureJet y) := by
    have : 0 < thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo y := mul_pos hj₊ hj₂₋
    have : 0 ≤ thetaCuspLogCurvatureJetTwo x * thetaCuspLogCurvatureJet y := mul_nonneg hj₂₊.le hj₋
    positivity
  -- `RHS − LHS = Q + 2s(…)`, divided by 4
  nlinarith [hQ, hgain]

/-- **Centre negativity from the sign facts.**  For `0 < t ≤ u`: `H < 0`. -/
theorem centerNumerator_neg_of_curvatureSigns {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hR2 : ∀ x : ℝ, 0 < x → 0 < thetaCuspLogCurvatureJet x)
    (hR3 : ∀ x : ℝ, 0 ≤ x → 0 < thetaCuspLogCurvatureJetTwo x)
    (hR4 : ∀ x : ℝ, 0 ≤ x → 0 ≤ thetaCuspLogCurvatureJetThree x →
      thetaCuspLogCurvature x * thetaCuspLogCurvatureJetThree x ≤
        thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo x) :
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0 := by
  -- positivity of the local denominator on `(0, t]`
  have hden_pos : ∀ s ∈ Ioc (0 : ℝ) t, 0 < completedLocalDenominator u s := by
    intro s hs
    unfold completedLocalDenominator
    have he := completedCurvatureEven_pos u s
    have hmono : MonotoneOn thetaCuspLogCurvatureJet (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
      · intro w _; exact (hasDerivAt_thetaCuspLogCurvatureJet w).continuousAt.continuousWithinAt
      · intro w _; exact (hasDerivAt_thetaCuspLogCurvatureJet w).differentiableAt.differentiableWithinAt
      · intro w hw; rw [interior_Ici] at hw
        rw [(hasDerivAt_thetaCuspLogCurvatureJet w).deriv]; exact (hR3 w hw.le).le
    have hj : thetaCuspLogCurvatureJet (u - s) ≤ thetaCuspLogCurvatureJet (u + s) :=
      hmono (mem_Ici.2 (by linarith [hs.2])) (mem_Ici.2 (by linarith [hs.1])) (by linarith [hs.1])
    have : 0 ≤ s * ((thetaCuspLogCurvatureJet (u + s) - thetaCuspLogCurvatureJet (u - s)) / 2) := by
      apply mul_nonneg hs.1.le; linarith
    linarith
  -- strict decrease of the local ratio `r₃ = o'/(2e + se')` on `(0, t]`
  have hr3 : StrictAntiOn (fun s => completedCurvatureOddJet u s / completedLocalDenominator u s)
      (Ioc 0 t) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc 0 t) ?_ ?_
    · refine ContinuousOn.div ?_ ?_ (fun s hs => (hden_pos s hs).ne')
      · exact fun s _ => (hasDerivAt_completedCurvatureOddJet u s).continuousAt.continuousWithinAt
      · exact fun s _ => (hasDerivAt_completedLocalDenominator u s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioc] at hs
      have hs' : s ∈ Ioc 0 t := ⟨hs.1, hs.2.le⟩
      have hd := (hasDerivAt_completedCurvatureOddJet u s).div
        (hasDerivAt_completedLocalDenominator u s) (hden_pos s hs').ne'
      rw [hd.deriv]
      apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (hden_pos s hs'))
      exact local_ratio_deriv_neg hs.1 (hs.2.le.trans htu) hR2 hR3 hR4
  -- first descent: `o/(E + se)` strictly decreasing on `(0, t]`
  have hr2 : StrictAntiOn (fun s => completedCurvatureOdd u s / completedFirstDenominator u s)
      (Ioc 0 t) := by
    refine strictAntiOn_ratio_of_strictAnti_derivRatio ht (completedCurvatureOdd_zero u) ?_ ?_ ?_
      (fun s _ => hasDerivAt_completedCurvatureOdd u s)
      (fun s _ => hasDerivAt_completedFirstDenominator u s) hden_pos ?_
    · unfold completedFirstDenominator; simp [completedDecayEvenPrimitive_zero]
    · exact fun s _ => (hasDerivAt_completedCurvatureOdd u s).continuousAt.continuousWithinAt
    · exact fun s _ => (hasDerivAt_completedFirstDenominator u s).continuousAt.continuousWithinAt
    · exact hr3
  -- second descent, cross form: `o(t)·tE(t) < O(t)·(E(t) + t e(t))`
  have hD₂pos : ∀ s ∈ Ioc (0 : ℝ) t, 0 < completedFirstDenominator u s := by
    intro s hs
    unfold completedFirstDenominator
    have hE : 0 < completedDecayEvenPrimitive u s := by
      rw [completedDecayEvenPrimitive_eq]
      exact div_pos (thetaCuspReflectedLogJetOne_pos u hs.1) (by norm_num)
    have := completedCurvatureEven_pos u s
    have : 0 < s * completedCurvatureEven u s := mul_pos hs.1 this
    linarith
  have hcross := deriv_cross_lt_of_strictAnti_derivRatio (N := completedDecayOddPrimitive u)
    (D := fun s => s * completedDecayEvenPrimitive u s) (N' := completedCurvatureOdd u)
    (D' := completedFirstDenominator u) ht (completedDecayOddPrimitive_zero u) (by simp)
    (fun s _ => (hasDerivAt_completedDecayOddPrimitive u s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_mul_completedDecayEvenPrimitive u s).continuousAt.continuousWithinAt)
    (fun s _ => hasDerivAt_completedDecayOddPrimitive u s)
    (fun s _ => hasDerivAt_mul_completedDecayEvenPrimitive u s) hD₂pos hr2
  -- identify `H` with `4(o·tE − O·(E + te))`
  have hH : thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t =
      4 * (completedCurvatureOdd u t * (t * completedDecayEvenPrimitive u t) -
        completedDecayOddPrimitive u t * completedFirstDenominator u t) := by
    unfold thetaCuspReflectedActionVelocityFixedActionCenterNumerator completedFirstDenominator
    rw [completedDecayEvenPrimitive_eq, completedDecayOddPrimitive_eq, completedCurvatureEven_eq,
      completedCurvatureOdd_eq]
    ring
  rw [hH]
  linarith

end

end RHTower
