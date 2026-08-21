import GaloisForLFunctions.RHTower.CosineIntegralAsymptotic
import GaloisForLFunctions.RHTower.SuzukiWeilPositionTorqueCurvature

/-!
# The regularized Fourier transform of Suzuki's smooth remainder curvature

The smooth remainder of the origin expansion splits as `r = r₀ + r₁` with

`r₀(t) = -4(e^{t/2} + e^{-t/2} - 2)`,  `r₀''(t) = -2 cosh(t/2)`,

and the Bernoulli block `r₁`, whose curvature is the elementary kernel

`r₁''(t) = e^{-|t|/2}/(1 - e^{-2|t|}) - 1/(2|t|)`.

That closed form is exactly the tail already carried by the corpus's
`suzukiWeilRemainderSecondDerivative`, so the split is an algebraic identity.

The kernel `r₁''` is *not* integrable at infinity — it decays like `-1/(2|t|)` — so its Fourier
transform exists only as a regularized limit.  Substituting `u = 2t` and splitting off the
exponential comparison,

`∫_ε^R (e^{-u/4}/(1-e^{-u}) - 1/u) cos(zu/2) du
   = ∫_ε^R ( e^{-u/4}cos(zu/2)/(1-e^{-u}) - e^{-u}/u ) du + ∫_ε^R (e^{-u} - cos(zu/2))/u du`,

the first block converges absolutely to `-Re ψ(1/4 + iz/2)` and the second, by the archimedean
cancellation, to `log z - log 2`.  Hence

`\hat{r₁''}(z) = -Re ψ(1/4 + iz/2) + log z - log 2`,

which is the source's evaluation.
-/

open MeasureTheory Set Filter Real

noncomputable section

namespace RHTower

/-! ## The Bernoulli block of the remainder curvature -/

/-- The curvature of the Bernoulli block of the origin remainder,
`r₁''(t) = e^{-|t|/2}/(1 - e^{-2|t|}) - 1/(2|t|)`. -/
def suzukiR1SecondDerivative (t : ℝ) : ℝ :=
  Real.exp (-|t| / 2) / (1 - Real.exp (-(2 * |t|))) - 1 / (2 * |t|)

theorem exp_div_two_sinh_eq {t : ℝ} (ht : 0 < t) :
    Real.exp (t / 2) / (2 * Real.sinh t)
      = Real.exp (-t / 2) / (1 - Real.exp (-(2 * t))) := by
  have hexp2 : Real.exp (-(2 * t)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hden : (1 : ℝ) - Real.exp (-(2 * t)) ≠ 0 := by linarith
  have hsinh : (2 : ℝ) * Real.sinh t ≠ 0 := by
    have : Real.sinh t ≠ 0 := (Real.sinh_ne_zero).2 ht.ne'
    simpa using this
  rw [div_eq_div_iff hsinh hden, Real.sinh_eq]
  have hL : Real.exp (t / 2) * (1 - Real.exp (-(2 * t)))
      = Real.exp (t / 2) - Real.exp (-(3 * t / 2)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  have hR : Real.exp (-t / 2) * (2 * ((Real.exp t - Real.exp (-t)) / 2))
      = Real.exp (t / 2) - Real.exp (-(3 * t / 2)) := by
    have hstep : Real.exp (-t / 2) * (2 * ((Real.exp t - Real.exp (-t)) / 2))
        = Real.exp (-t / 2) * Real.exp t - Real.exp (-t / 2) * Real.exp (-t) := by ring
    rw [hstep, ← Real.exp_add, ← Real.exp_add]
    congr 2 <;> ring
  rw [hL, hR]

/-- **The split of the remainder curvature.**  On the positive lag axis,
`r'' = r₀'' + r₁''` with `r₀''(t) = -2 cosh(t/2)`. -/
theorem suzukiWeilRemainderSecondDerivative_eq_r0_add_r1 {t : ℝ} (ht : 0 < t) :
    suzukiWeilRemainderSecondDerivative t
      = -2 * Real.cosh (t / 2) + suzukiR1SecondDerivative t := by
  rw [suzukiWeilRemainderSecondDerivative, suzukiR1SecondDerivative, abs_of_pos ht,
    exp_div_two_sinh_eq ht]
  ring

/-! ## Shrinking the base point of a half-line integral -/

theorem tendsto_setIntegral_Ioi_nhdsWithin_zero {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume) :
    Tendsto (fun ε : ℝ => ∫ u in Ioi ε, f u) (nhdsWithin 0 (Ioi 0))
      (nhds (∫ u in Ioi (0 : ℝ), f u)) := by
  have hind : ∀ ε : ℝ, 0 < ε →
      (∫ u in Ioi (0 : ℝ), (Ioi ε).indicator f u) = ∫ u in Ioi ε, f u := by
    intro ε hε
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
    congr 1
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨lt_trans hε h, h⟩
  have hDCT : Tendsto (fun ε : ℝ => ∫ u in Ioi (0 : ℝ), (Ioi ε).indicator f u)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ u in Ioi (0 : ℝ), f u)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => ‖f u‖) ?_ ?_ hf.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε _
      exact hf.aestronglyMeasurable.indicator measurableSet_Ioi
    · filter_upwards [self_mem_nhdsWithin] with ε _
      filter_upwards with u
      rw [Set.indicator_apply]
      split_ifs
      · exact le_rfl
      · simpa using norm_nonneg (f u)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      have heven : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), (Ioi ε).indicator f u = f u := by
        have hlt : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε < u := by
          have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          exact hid.eventually_lt_const hu0
        filter_upwards [hlt] with ε hε
        rw [Set.indicator_apply, if_pos hε]
      exact Tendsto.congr' heven.symm tendsto_const_nhds
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hind ε hε

/-! ## The regularized Fourier transform -/

/-- The truncated Fourier integral of `r₁''` in the variable `u = 2t`. -/
def suzukiR1FourierTruncated (z ε R : ℝ) : ℝ :=
  ∫ u in ε..R, (Real.exp (-u / 4) / (1 - Real.exp (-u)) - 1 / u) * Real.cos (z * u / 2)

/-- The value the truncated integrals converge to as the cut-off is removed. -/
def suzukiR1FourierPartial (z ε : ℝ) : ℝ :=
  (∫ u in Ioi ε, suzukiArchKernel z u)
    + ((∫ u in Ioi ε, Real.exp (-u) / u) - cosIntegralTail (z / 2 * ε))

theorem intervalIntegrable_suzukiArchKernel {z ε R : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (suzukiArchKernel z) volume ε R := by
  refine ContinuousOn.intervalIntegrable ?_
  intro u hu
  have hu0 : 0 < u := by
    rcases le_total ε R with h | h
    · rw [Set.uIcc_of_le h] at hu; exact lt_of_lt_of_le hε hu.1
    · rw [Set.uIcc_of_ge h] at hu
      exact lt_of_lt_of_le hε (le_trans hu.1 (le_of_eq rfl)) |>.trans_le hu.1 |>.le.trans_lt
        (lt_of_lt_of_le hε hu.1) |>.le.trans_lt (lt_of_lt_of_le hε hu.1)
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.sub ?_ ?_
  · refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    have := one_sub_exp_neg_pos hu0
    linarith
  · exact ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt hu0)

theorem intervalIntegrable_expDivT {ε R : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun u : ℝ => Real.exp (-u) / u) volume ε R := by
  refine ContinuousOn.intervalIntegrable ?_
  intro u hu
  have hu0 : 0 < u := by
    rcases le_total ε R with h | h
    · rw [Set.uIcc_of_le h] at hu; exact lt_of_lt_of_le hε hu.1
    · rw [Set.uIcc_of_ge h] at hu; exact lt_of_lt_of_le hε hu.1
  exact ContinuousAt.continuousWithinAt
    (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt hu0))

theorem intervalIntegrable_cosDivT {z ε R : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun u : ℝ => Real.cos (z * u / 2) / u) volume ε R := by
  refine ContinuousOn.intervalIntegrable ?_
  intro u hu
  have hu0 : 0 < u := by
    rcases le_total ε R with h | h
    · rw [Set.uIcc_of_le h] at hu; exact lt_of_lt_of_le hε hu.1
    · rw [Set.uIcc_of_ge h] at hu; exact lt_of_lt_of_le hε hu.1
  exact ContinuousAt.continuousWithinAt
    (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt hu0))

/-- The algebraic split of the truncated Fourier integrand. -/
theorem suzukiR1FourierTruncated_split {z ε R : ℝ} (hε : 0 < ε) :
    suzukiR1FourierTruncated z ε R
      = (∫ u in ε..R, suzukiArchKernel z u)
        + ∫ u in ε..R, (Real.exp (-u) - Real.cos (z * u / 2)) / u := by
  have hsecond : IntervalIntegrable
      (fun u : ℝ => (Real.exp (-u) - Real.cos (z * u / 2)) / u) volume ε R := by
    refine ((intervalIntegrable_expDivT hε).sub (intervalIntegrable_cosDivT hε)).congr ?_
    intro u hu
    have hu0 : 0 < u := by
      rcases le_total ε R with h | h
      · rw [Set.uIoc_of_le h] at hu; exact lt_trans hε hu.1
      · rw [Set.uIoc_of_ge h] at hu; exact lt_of_lt_of_le hε (le_of_lt hu.1)
    simp only [Pi.sub_apply]
    field_simp
  rw [← intervalIntegral.integral_add (intervalIntegrable_suzukiArchKernel hε) hsecond]
  refine intervalIntegral.integral_congr ?_
  intro u hu
  have hu0 : 0 < u := by
    rcases le_total ε R with h | h
    · rw [Set.uIcc_of_le h] at hu; exact lt_of_lt_of_le hε hu.1
    · rw [Set.uIcc_of_ge h] at hu; exact lt_of_lt_of_le hε hu.1
  have hden : (1 : ℝ) - Real.exp (-u) ≠ 0 := ne_of_gt (one_sub_exp_neg_pos hu0)
  dsimp only
  rw [suzukiArchKernel]
  field_simp
  ring

end RHTower
