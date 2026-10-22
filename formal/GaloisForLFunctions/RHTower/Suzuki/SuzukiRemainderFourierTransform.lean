import GaloisForLFunctions.RHTower.CosineIntegralAsymptotic
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPositionTorqueCurvature
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

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
  have hsinh : (2 : ℝ) * Real.sinh t ≠ 0 :=
    mul_ne_zero two_ne_zero ((Real.sinh_ne_zero).2 ht.ne')
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
    have hset : Ioi (0 : ℝ) ∩ Ioi ε = Ioi ε := by
      ext u
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨lt_trans hε h, h⟩
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi, hset]
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
      · simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      have hlt : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε < u := by
        have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        exact hid.eventually_lt_const hu0
      refine Tendsto.congr' ?_ (tendsto_const_nhds
        (x := f u) (f := nhdsWithin (0 : ℝ) (Ioi 0)))
      filter_upwards [hlt] with ε hε
      exact (Set.indicator_of_mem (Set.mem_Ioi.mpr hε) f).symm
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

theorem pos_of_mem_uIcc {ε R u : ℝ} (hε : 0 < ε) (hR : 0 < R) (hu : u ∈ Set.uIcc ε R) :
    0 < u := by
  rcases le_total ε R with h | h
  · rw [Set.uIcc_of_le h] at hu
    exact lt_of_lt_of_le hε hu.1
  · rw [Set.uIcc_of_ge h] at hu
    exact lt_of_lt_of_le hR hu.1

theorem intervalIntegrable_suzukiArchKernel {z ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    IntervalIntegrable (suzukiArchKernel z) volume ε R := by
  refine ContinuousOn.intervalIntegrable ?_
  intro u hu
  have hu0 : 0 < u := pos_of_mem_uIcc hε hR hu
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.sub ?_ ?_
  · refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    have := one_sub_exp_neg_pos hu0
    linarith
  · exact ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt hu0)

theorem intervalIntegrable_expDivT {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    IntervalIntegrable (fun u : ℝ => Real.exp (-u) / u) volume ε R := by
  refine ContinuousOn.intervalIntegrable ?_
  intro u hu
  have hu0 : 0 < u := pos_of_mem_uIcc hε hR hu
  exact ContinuousAt.continuousWithinAt
    (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt hu0))

theorem intervalIntegrable_cosDivT {z ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    IntervalIntegrable (fun u : ℝ => Real.cos (z * u / 2) / u) volume ε R := by
  refine ContinuousOn.intervalIntegrable ?_
  intro u hu
  have hu0 : 0 < u := pos_of_mem_uIcc hε hR hu
  exact ContinuousAt.continuousWithinAt
    (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt hu0))

/-- The algebraic split of the truncated Fourier integrand. -/
theorem suzukiR1FourierTruncated_split {z ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    suzukiR1FourierTruncated z ε R
      = (∫ u in ε..R, suzukiArchKernel z u)
        + ∫ u in ε..R, (Real.exp (-u) - Real.cos (z * u / 2)) / u := by
  have hsecond : IntervalIntegrable
      (fun u : ℝ => (Real.exp (-u) - Real.cos (z * u / 2)) / u) volume ε R := by
    refine ((intervalIntegrable_expDivT hε hR).sub
      (intervalIntegrable_cosDivT (z := z) hε hR)).congr ?_
    intro u hu
    have hu0 : 0 < u := pos_of_mem_uIcc hε hR (Set.Ioc_subset_Icc_self hu)
    field_simp
  rw [← intervalIntegral.integral_add (intervalIntegrable_suzukiArchKernel hε hR) hsecond]
  refine intervalIntegral.integral_congr ?_
  intro u hu
  have hu0 : 0 < u := pos_of_mem_uIcc hε hR hu
  have hden : (1 : ℝ) - Real.exp (-u) ≠ 0 := ne_of_gt (one_sub_exp_neg_pos hu0)
  dsimp only
  rw [suzukiArchKernel]
  field_simp
  ring


/-! ## Removing the cut-offs -/

theorem integrableOn_expNegDiv_Ioi {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioi ε) volume := by
  rcases le_total ε 1 with h1 | h1
  · have hsplit : Set.Ioc ε 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi ε := Set.Ioc_union_Ioi_eq_Ioi h1
    have hIoc : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Set.Ioc ε 1) volume := by
      have h := intervalIntegrable_exp_neg_div hε h1
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le h1] at h
    rw [← hsplit]
    exact hIoc.union integrableOn_exp_neg_div_Ioi_one
  · exact integrableOn_exp_neg_div_Ioi_ge h1

theorem intervalIntegral_cos_scale {z : ℝ} (hz : 0 < z) (ε R : ℝ) :
    (∫ u in ε..R, Real.cos (z * u / 2) / u)
      = ∫ v in (z / 2 * ε)..(z / 2 * R), Real.cos v / v := by
  set a : ℝ := z / 2 with ha_def
  have hapos : 0 < a := by rw [ha_def]; linarith
  have ha : a ≠ 0 := ne_of_gt hapos
  have hsub := intervalIntegral.integral_comp_mul_left (a := ε) (b := R) (c := a)
    (fun v : ℝ => Real.cos v / v) ha
  have hpoint : ∀ u : ℝ, Real.cos (z * u / 2) / u = a * (Real.cos (a * u) / (a * u)) := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · rw [ha_def]
      field_simp
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, hsub, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ha, one_mul]

theorem tendsto_suzukiR1FourierTruncated_atTop {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε) :
    Tendsto (fun R : ℝ => suzukiR1FourierTruncated z ε R) atTop
      (nhds (suzukiR1FourierPartial z ε)) := by
  have hapos : 0 < z / 2 := by linarith
  have hArch : Tendsto (fun R : ℝ => ∫ u in ε..R, suzukiArchKernel z u) atTop
      (nhds (∫ u in Ioi ε, suzukiArchKernel z u)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := ε)
      ((integrableOn_suzukiArchKernel z).mono_set (Set.Ioi_subset_Ioi (le_of_lt hε)))
      tendsto_id
  have hExp : Tendsto (fun R : ℝ => ∫ u in ε..R, Real.exp (-u) / u) atTop
      (nhds (∫ u in Ioi ε, Real.exp (-u) / u)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := ε)
      (integrableOn_expNegDiv_Ioi hε) tendsto_id
  have hCos : Tendsto (fun R : ℝ => ∫ u in ε..R, Real.cos (z * u / 2) / u) atTop
      (nhds (cosIntegralTail (z / 2 * ε))) := by
    have hscale : Tendsto (fun R : ℝ => z / 2 * R) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hapos tendsto_id
    have hbase := (tendsto_cosIntegralTail (x := z / 2 * ε) (by positivity)).comp hscale
    refine hbase.congr ?_
    intro R
    simp only [Function.comp_apply]
    exact (intervalIntegral_cos_scale hz ε R).symm
  have hSecond : Tendsto
      (fun R : ℝ => ∫ u in ε..R, (Real.exp (-u) - Real.cos (z * u / 2)) / u) atTop
      (nhds ((∫ u in Ioi ε, Real.exp (-u) / u) - cosIntegralTail (z / 2 * ε))) := by
    refine (hExp.sub hCos).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR0
    rw [← intervalIntegral.integral_sub (intervalIntegrable_expDivT hε hR0)
      (intervalIntegrable_cosDivT (z := z) hε hR0)]
    refine intervalIntegral.integral_congr ?_
    intro u hu
    have hu0 : 0 < u := pos_of_mem_uIcc hε hR0 hu
    dsimp only
    field_simp
  have hsum := hArch.add hSecond
  rw [suzukiR1FourierPartial]
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (suzukiR1FourierTruncated_split hε hR).symm


theorem suzukiR1FourierTruncated_neg (z : ℝ) (ε R : ℝ) :
    suzukiR1FourierTruncated (-z) ε R = suzukiR1FourierTruncated z ε R := by
  rw [suzukiR1FourierTruncated, suzukiR1FourierTruncated]
  refine intervalIntegral.integral_congr ?_
  intro u _
  dsimp only
  rw [show -z * u / 2 = -(z * u / 2) by ring, Real.cos_neg]

/-- **The regularized Fourier transform of `r₁''`.**  For `z > 0` the cut-off value converges to
`-Re ψ(1/4 + iz/2) + log z - log 2`. -/
theorem tendsto_suzukiR1FourierPartial {z : ℝ} (hz : 0 < z) :
    Tendsto (fun ε : ℝ => suzukiR1FourierPartial z ε) (nhdsWithin 0 (Ioi 0))
      (nhds (-(Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re
        + Real.log z - Real.log 2)) := by
  have hA : Tendsto (fun ε : ℝ => ∫ u in Ioi ε, suzukiArchKernel z u)
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ u in Ioi (0 : ℝ), suzukiArchKernel z u)) :=
    tendsto_setIntegral_Ioi_nhdsWithin_zero (integrableOn_suzukiArchKernel z)
  have hB := tendsto_expIntegralTail_sub_cosIntegralTail (a := z / 2) (by linarith)
  have hsum := hA.add hB
  rw [integral_suzukiArchKernel z, Real.log_div (ne_of_gt hz) two_ne_zero] at hsum
  have hassoc : -(Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re
        + (Real.log z - Real.log 2)
      = -(Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re
        + Real.log z - Real.log 2 := by ring
  rw [← hassoc]
  exact hsum

/-- **Suzuki's evaluation of `\hat{r₁''}`.**  For `z > 0`:

* for every cut-off `ε > 0` the truncated Fourier integrals converge as `R → ∞`, and
* the resulting values converge, as `ε → 0+`, to `-Re ψ(1/4 + iz/2) + log z - log 2`.

Together these are the source's `\hat{r₁''}(z) = -Re ψ(1/4 + iz/2) + log|z| - log 2`; the integrand
`r₁''` is not integrable at infinity, so the transform exists only in this regularized sense. -/
theorem suzukiR1Fourier_regularized {z : ℝ} (hz : 0 < z) :
    (∀ ε : ℝ, 0 < ε →
        Tendsto (fun R : ℝ => suzukiR1FourierTruncated z ε R) atTop
          (nhds (suzukiR1FourierPartial z ε)))
      ∧ Tendsto (fun ε : ℝ => suzukiR1FourierPartial z ε) (nhdsWithin 0 (Ioi 0))
          (nhds (-(Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re
            + Real.log z - Real.log 2)) :=
  ⟨fun _ hε => tendsto_suzukiR1FourierTruncated_atTop hz hε,
    tendsto_suzukiR1FourierPartial hz⟩


/-! ## The archimedean symbol of (2.7)–(2.8) -/

/-- **The symbol identity behind the passage from (2.7) to (2.8).**  Subtracting the regularized
Fourier transform `\hat{r₁''}(z) = -Re ψ(1/4 + iz/2) + log z - log 2` from the raw logarithmic
symbol `log z - log(2π)` leaves exactly the archimedean digamma symbol
`Re ψ(1/4 + iz/2) - log π`: the `log z` cancels and `-log(2π) + log 2 = -log π`. -/
theorem suzukiArchimedeanSymbol (z : ℝ) :
    Real.log z - Real.log (2 * Real.pi)
        - (-(Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re
            + Real.log z - Real.log 2)
      = (Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi := by
  rw [Real.log_mul two_ne_zero Real.pi_ne_zero]
  ring

/-- **The full archimedean evaluation.**  For `z > 0` the regularized Fourier transform of `r₁''`
is the limit of the truncated integrals, and subtracting it from `log z - log(2π)` gives the
digamma symbol.  This is the passage from (2.7) to (2.8) in the source. -/
theorem suzukiR1Fourier_symbol {z : ℝ} (hz : 0 < z) :
    Tendsto (fun ε : ℝ => Real.log z - Real.log (2 * Real.pi) - suzukiR1FourierPartial z ε)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re
        - Real.log Real.pi)) := by
  have h := (tendsto_const_nhds
    (x := Real.log z - Real.log (2 * Real.pi))
    (f := nhdsWithin (0 : ℝ) (Ioi 0))).sub (tendsto_suzukiR1FourierPartial hz)
  rw [suzukiArchimedeanSymbol z] at h
  exact h


/-! ## The archimedean symbol at large frequency -/

/-- **The source's archimedean asymptotic** `Re ψ(s/2) = log|s| - log 2 + O(|s|^{-2})` on the
right half plane.  The `-1/(2s)` term of the digamma asymptotic contributes `Re(1/s) = Re s/|s|²`,
which is `O(|s|^{-2})` uniformly on any vertical strip. -/
theorem abs_re_digamma_half_sub_log_le {s : ℂ} (hre : 0 < s.re) (hs : 4 ≤ ‖s‖) :
    |(Complex.digamma (s / 2)).re - (Real.log ‖s‖ - Real.log 2)|
      ≤ (20 + s.re) / ‖s‖ ^ (2 : ℕ) := by
  have hnorm2 : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [norm_div]
    norm_num
  have hspos : (0 : ℝ) < ‖s‖ := by linarith
  have hw2 : (2 : ℝ) ≤ ‖s / 2‖ := by rw [hnorm2]; linarith
  have hwre : 0 < (s / 2).re := by
    have hre2 : (s / 2).re = s.re / 2 := by simp
    rw [hre2]
    linarith
  have h := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_add_half_inv_le_of_re_pos hwre hw2
  have hhalf : (2 : ℂ) * (s / 2) = s := by ring
  have hrw : Complex.digamma (s / 2) - Complex.log (s / 2) + 1 / (2 * (s / 2))
      = Complex.digamma (s / 2) - Complex.log (s / 2) + 1 / s := by rw [hhalf]
  rw [hrw] at h
  have hre_le : |(Complex.digamma (s / 2) - Complex.log (s / 2) + 1 / s).re|
      ≤ 5 / ‖s / 2‖ ^ (2 : ℕ) := le_trans (Complex.abs_re_le_norm _) h
  have hlogre : (Complex.log (s / 2)).re = Real.log ‖s‖ - Real.log 2 := by
    rw [Complex.log_re, hnorm2, Real.log_div (ne_of_gt hspos) two_ne_zero]
  have hinvre : (1 / s : ℂ).re = s.re / ‖s‖ ^ (2 : ℕ) := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hsplit : (Complex.digamma (s / 2) - Complex.log (s / 2) + 1 / s).re
      = ((Complex.digamma (s / 2)).re - (Real.log ‖s‖ - Real.log 2)) + s.re / ‖s‖ ^ (2 : ℕ) := by
    rw [Complex.add_re, Complex.sub_re, hlogre, hinvre]
  rw [hsplit] at hre_le
  have hbound : (5 : ℝ) / ‖s / 2‖ ^ (2 : ℕ) = 20 / ‖s‖ ^ (2 : ℕ) := by
    rw [hnorm2]
    field_simp
    ring
  rw [hbound] at hre_le
  have hnn : (0 : ℝ) ≤ s.re / ‖s‖ ^ (2 : ℕ) := by positivity
  have hAB := abs_le.mp hre_le
  have hsum : (20 : ℝ) / ‖s‖ ^ (2 : ℕ) + s.re / ‖s‖ ^ (2 : ℕ) = (20 + s.re) / ‖s‖ ^ (2 : ℕ) := by ring
  rw [abs_le]
  constructor
  · linarith [hAB.1, hnn, hsum.le, hsum.ge]
  · linarith [hAB.2, hnn, hsum.le, hsum.ge]

end RHTower
