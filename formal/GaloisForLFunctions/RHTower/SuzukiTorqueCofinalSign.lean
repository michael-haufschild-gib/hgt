import GaloisForLFunctions.RHTower.OneSignTailImpossible

/-!
# `(19)`: the free position torque changes sign cofinally

The prime layer is nonnegative and the archimedean layer is an explicit elementary function, so the
torque's transform is the completed curvature difference `(16)`.  Above any nontrivial zero of `ξ`
that difference has a genuine double pole, which no one-sign tail can carry: applying the
one-sign-tail obstruction to the torque and to its negative gives points of both signs beyond every
height.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The torque continuation is analytic on the half-plane minus its own divisor. -/
theorem analyticAt_continuation_of_mem {z : ℂ} (hz : 1 / 4 < z.re) (h1 : xi (z - 1 / 2) ≠ 0) :
    AnalyticAt ℂ suzukiPositionTorqueLaplaceContinuation z := by
  refine analyticAt_suzukiPositionTorqueLaplaceContinuation ?_ h1 ?_
  · intro hcon
    rw [hcon, Complex.zero_re] at hz
    norm_num at hz
  · refine xi_ne_zero_of_one_lt_re ?_
    rw [Complex.add_re]
    norm_num
    linarith

/-- A nontrivial Xi zero, lifted to the pole of the continuation. -/
theorem exists_continuation_pole :
    ∃ p : ℂ, 1 / 4 < p.re ∧
      meromorphicOrderAt suzukiPositionTorqueLaplaceContinuation p = ((-2 : ℤ) : WithTop ℤ) := by
  obtain ⟨ρ, h0, h1, hz⟩ := exists_xi_zero_openStrip
  refine ⟨ρ + 1 / 2, ?_, meromorphicOrderAt_continuation_eq_neg_two h0 h1 hz⟩
  rw [Complex.add_re]
  norm_num
  linarith

/-- **The torque is not eventually nonnegative.** -/
theorem not_eventually_nonneg_suzukiFreePositionTorque :
    ¬ ∃ H : ℝ, 0 ≤ H ∧ ∀ L : ℝ, H < L → 0 ≤ suzukiFreePositionTorque L := by
  obtain ⟨p, hp, hporder⟩ := exists_continuation_pole
  exact no_oneSign_tail continuous_suzukiFreePositionTorque
    (fun σ hσ => integrableOn_suzukiFreePositionTorque_mul_exp hσ)
    (fun σ hσ => integral_suzukiFreePositionTorque_mul_exp_eq_continuation hσ)
    (fun z hz h1 => analyticAt_continuation_of_mem hz h1) hp hporder

/-- **The torque is not eventually nonpositive.** -/
theorem not_eventually_nonpos_suzukiFreePositionTorque :
    ¬ ∃ H : ℝ, 0 ≤ H ∧ ∀ L : ℝ, H < L → suzukiFreePositionTorque L ≤ 0 := by
  obtain ⟨p, hp, hporder⟩ := exists_continuation_pole
  have hneg : ¬ ∃ H : ℝ, 0 ≤ H ∧ ∀ L : ℝ, H < L → 0 ≤ -suzukiFreePositionTorque L := by
    refine no_oneSign_tail (g := fun L : ℝ => -suzukiFreePositionTorque L)
      (Gc := fun s : ℂ => -suzukiPositionTorqueLaplaceContinuation s)
      continuous_suzukiFreePositionTorque.neg ?_ ?_ ?_ hp ?_
    · intro σ hσ
      have h := (integrableOn_suzukiFreePositionTorque_mul_exp hσ).neg
      refine h.congr_fun (fun L _ => ?_) measurableSet_Ioi
      simp only [Pi.neg_apply]
      ring
    · intro σ hσ
      have hcongr : (∫ L in Ioi (0 : ℝ), -suzukiFreePositionTorque L * Real.exp (-σ * L))
          = -∫ L in Ioi (0 : ℝ), suzukiFreePositionTorque L * Real.exp (-σ * L) := by
        rw [← integral_neg]
        refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
        ring
      rw [hcongr, Complex.ofReal_neg,
        integral_suzukiFreePositionTorque_mul_exp_eq_continuation hσ]
    · intro z hz h1
      exact (analyticAt_continuation_of_mem hz h1).neg
    · rw [← meromorphicOrderAt_fun_neg (f := suzukiPositionTorqueLaplaceContinuation) (x := p)]
      exact hporder
  intro hcon
  obtain ⟨H, hH, hle⟩ := hcon
  exact hneg ⟨H, hH, fun L hL => by linarith [hle L hL]⟩

/-- **`(19)`: the free position torque crosses zero cofinally in both directions.** -/
theorem exists_suzukiFreePositionTorque_sign_change (L₀ : ℝ) :
    ∃ Lm Lp : ℝ, L₀ < Lm ∧ L₀ < Lp ∧
      suzukiFreePositionTorque Lm < 0 ∧ 0 < suzukiFreePositionTorque Lp := by
  have hm : ∃ Lm : ℝ, L₀ < Lm ∧ suzukiFreePositionTorque Lm < 0 := by
    by_contra hcon
    refine not_eventually_nonneg_suzukiFreePositionTorque
      ⟨max L₀ 0, le_max_right _ _, fun L hL => ?_⟩
    have hL₀ : L₀ < L := lt_of_le_of_lt (le_max_left _ _) hL
    by_contra hneg
    exact hcon ⟨L, hL₀, lt_of_not_ge hneg⟩
  have hp : ∃ Lp : ℝ, L₀ < Lp ∧ 0 < suzukiFreePositionTorque Lp := by
    by_contra hcon
    refine not_eventually_nonpos_suzukiFreePositionTorque
      ⟨max L₀ 0, le_max_right _ _, fun L hL => ?_⟩
    have hL₀ : L₀ < L := lt_of_le_of_lt (le_max_left _ _) hL
    by_contra hpos
    exact hcon ⟨L, hL₀, lt_of_not_ge hpos⟩
  obtain ⟨Lm, hLm, hLmneg⟩ := hm
  obtain ⟨Lp, hLp, hLppos⟩ := hp
  exact ⟨Lm, Lp, hLm, hLp, hLmneg, hLppos⟩

/-- **`(20)`: the prime torque crosses its exact archimedean baseline cofinally in both
directions.** -/
theorem exists_suzukiFreePrimePositionTorque_cross_baseline (L₀ : ℝ) :
    ∃ Lm Lp : ℝ, L₀ < Lm ∧ L₀ < Lp ∧
      suzukiFreePrimePositionTorque Lm < -suzukiFreeArchPositionTorque Lm ∧
      -suzukiFreeArchPositionTorque Lp < suzukiFreePrimePositionTorque Lp := by
  obtain ⟨Lm, Lp, hLm, hLp, hneg, hpos⟩ := exists_suzukiFreePositionTorque_sign_change L₀
  rw [suzukiFreePositionTorque] at hneg hpos
  exact ⟨Lm, Lp, hLm, hLp, by linarith, by linarith⟩

end RHTower
