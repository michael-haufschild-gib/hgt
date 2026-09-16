import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCoordinateTransport
import GaloisForLFunctions.RHTower.SuzukiScrewGrowthBound
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingCurrent

/-!
# De la Vallee Poussin rate in matched polar mass coordinate

The rigid matched-to-quantile displacement is driven by the completed critical-Mellin error.
This module begins its unconditional arithmetic control at the exact Volterra input: the
normalized Chebyshev error. The corpus Littlewood/de la Vallee Poussin theorem gives the sharp
logarithmic-height rate

`|E_norm(h)| <= B exp(h/2 - c sqrt(h))`.

Consequently this driver vanishes after division by the polar mass scale `exp(h/2)`. These are
source theorems with no RH premise, numerical verification, or additional axiom.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

private theorem intervalIntegrable_of_bound_on {f : ℝ → ℝ} (hf : Measurable f)
    {C a b : ℝ} (hab : a ≤ b) (hb : ∀ t ∈ Icc a b, |f t| ≤ C) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := |C|) (by simp)
    hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact (hb t (Ioc_subset_Icc_self ht)).trans (le_abs_self C)

/-- The normalized Chebyshev driver of the completed critical-Mellin error has the
de la Vallee Poussin rate in logarithmic height. -/
theorem exists_abs_criticalMellinNormalizedChebyshevError_le_exp_half_sub_sqrt :
    ∃ c B : ℝ, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ h : ℝ in atTop,
      |criticalMellinNormalizedChebyshevError h| ≤
        B * Real.exp (h / 2 - c * Real.sqrt h) := by
  obtain ⟨c, B, hc, hB, hrate⟩ :=
    exists_abs_suzukiChebyshevError_le_sqrtLog
  refine ⟨c, B, hc, hB, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hrate,
    eventually_ge_atTop (0 : ℝ)] with h hrateh hh
  have hexp : (0 : ℝ) < Real.exp h := Real.exp_pos h
  have hsqrt : Real.sqrt (Real.exp h) = Real.exp (h / 2) :=
    sqrt_exp_eq_exp_half h
  have hrateh' : |Chebyshev.psi (Real.exp h) - Real.exp h| ≤
      B * Real.exp h * Real.exp (-c * Real.sqrt h) := by
    simpa only [suzukiChebyshevError, Real.log_exp] using hrateh
  unfold criticalMellinNormalizedChebyshevError
  rw [criticalMellinError, criticalCumulative_vonMangoldt_eq_psi, abs_div,
    abs_of_pos (Real.sqrt_pos.mpr hexp)]
  calc
    |Chebyshev.psi (Real.exp h) - Real.exp h| / Real.sqrt (Real.exp h) ≤
        (B * Real.exp h * Real.exp (-c * Real.sqrt h)) /
          Real.sqrt (Real.exp h) :=
      div_le_div_of_nonneg_right hrateh' (Real.sqrt_nonneg _)
    _ = B * Real.exp (h / 2 - c * Real.sqrt h) := by
      rw [hsqrt, div_eq_iff (Real.exp_ne_zero (h / 2))]
      rw [show Real.exp h = Real.exp (h / 2) * Real.exp (h / 2) by
        rw [← Real.exp_add]
        congr 1
        ring]
      rw [show Real.exp (h / 2 - c * Real.sqrt h) =
          Real.exp (h / 2) * Real.exp (-c * Real.sqrt h) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring

/-- The PNT-scale driver is negligible relative to the polar mass coordinate. -/
theorem tendsto_exp_neg_half_mul_criticalMellinNormalizedChebyshevError_atTop_zero :
    Tendsto (fun h : ℝ => Real.exp (-h / 2) *
      criticalMellinNormalizedChebyshevError h) atTop (𝓝 0) := by
  obtain ⟨c, B, hc, hB, hrate⟩ :=
    exists_abs_criticalMellinNormalizedChebyshevError_le_exp_half_sub_sqrt
  have hmajor : Tendsto (fun h : ℝ =>
      B * Real.exp (-c * Real.sqrt h)) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun h : ℝ => Real.sqrt h) atTop atTop :=
      Real.tendsto_sqrt_atTop
    have harg : Tendsto (fun h : ℝ => -c * Real.sqrt h) atTop atBot := by
      have hmul := hsqrt.const_mul_atTop hc
      have hneg := tendsto_neg_atBot_iff.2 hmul
      simpa [neg_mul] using hneg
    have hexp := Real.tendsto_exp_atBot.comp harg
    simpa using hexp.const_mul B
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hrate] with h hh
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-h / 2) * |criticalMellinNormalizedChebyshevError h| ≤
        Real.exp (-h / 2) *
          (B * Real.exp (h / 2 - c * Real.sqrt h)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = B * Real.exp (-c * Real.sqrt h) := by
      rw [show Real.exp (h / 2 - c * Real.sqrt h) =
          Real.exp (h / 2) * Real.exp (-c * Real.sqrt h) by
        rw [← Real.exp_add]
        congr 1
        ring]
      calc
        Real.exp (-h / 2) *
            (B * (Real.exp (h / 2) * Real.exp (-c * Real.sqrt h))) =
            B * (Real.exp (-h / 2) * Real.exp (h / 2)) *
              Real.exp (-c * Real.sqrt h) := by ring
        _ = B * Real.exp (-c * Real.sqrt h) := by
          rw [show Real.exp (-h / 2) * Real.exp (h / 2) = 1 by
            calc
              Real.exp (-h / 2) * Real.exp (h / 2) = Real.exp 0 := by
                rw [← Real.exp_add]
                congr 1
                ring
              _ = 1 := Real.exp_zero]
          ring

/-- Causal Volterra integration preserves negligibility relative to the polar mass scale.
The proof uses the actual normalized Chebyshev driver, splits at a fixed late threshold, and
evaluates the tail against the exact half-exponential primitive. -/
theorem tendsto_exp_neg_half_mul_criticalMellinNormalizedChebyshevPrimitive_atTop_zero :
    Tendsto (fun h : ℝ => Real.exp (-h / 2) *
      (∫ t in (0 : ℝ)..h, criticalMellinNormalizedChebyshevError t))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp
    tendsto_exp_neg_half_mul_criticalMellinNormalizedChebyshevError_atTop_zero
    (eps / 4) (by linarith)
  let T' : ℝ := max 0 T
  have hT0 : 0 ≤ T' := le_max_left _ _
  have hTT' : T ≤ T' := le_max_right _ _
  let A : ℝ := ∫ t in (0 : ℝ)..T', criticalMellinNormalizedChebyshevError t
  have hhead : Tendsto (fun h : ℝ => Real.exp (-h / 2) * A) atTop (𝓝 0) := by
    have harg : Tendsto (fun h : ℝ => -h / 2) atTop atBot := by
      have hmul := tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      have hneg := tendsto_neg_atBot_iff.2 hmul
      convert hneg using 1
      ext h
      simp only [id_eq]
      ring
    have hexp : Tendsto (fun h : ℝ => Real.exp (-h / 2)) atTop (𝓝 0) := by
      convert Real.tendsto_exp_atBot.comp harg using 1
      ext h
      simp only [Function.comp_apply]
    simpa only [zero_mul] using hexp.mul_const A
  obtain ⟨H, hH⟩ := Metric.tendsto_atTop.mp hhead (eps / 2) (by linarith)
  refine ⟨max T' H, fun h hh => ?_⟩
  have hT'h : T' ≤ h := le_trans (le_max_left _ _) hh
  have hHh : H ≤ h := le_trans (le_max_right _ _) hh
  have hheadsmall : |Real.exp (-h / 2) * A| < eps / 2 := by
    simpa only [Real.dist_eq, sub_zero] using hH h hHh
  have htailInt : IntervalIntegrable criticalMellinNormalizedChebyshevError volume T' h := by
    refine intervalIntegrable_of_bound_on
      (C := criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) +
        Real.exp h)
      measurable_criticalMellinNormalizedChebyshevError hT'h ?_
    intro x hx
    exact abs_criticalMellinNormalizedChebyshevError_le_endpoint
      ⟨hT0.trans hx.1, hx.2⟩
  have hgInt : IntervalIntegrable (fun t : ℝ => eps / 4 * Real.exp (t / 2)) volume T' h :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 2))).intervalIntegrable _ _
  have htailBound :
      |∫ t in T'..h, criticalMellinNormalizedChebyshevError t| ≤
        ∫ t in T'..h, eps / 4 * Real.exp (t / 2) := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_of_norm_le
        (f := criticalMellinNormalizedChebyshevError) hT'h
        (Filter.Eventually.of_forall fun t ht => by
          have hpoint := hT t (hTT'.trans ht.1.le)
          have hpoint' :
              |Real.exp (-t / 2) * criticalMellinNormalizedChebyshevError t| < eps / 4 := by
            simpa only [Real.dist_eq, sub_zero] using hpoint
          have hrewrite : |criticalMellinNormalizedChebyshevError t| =
              Real.exp (t / 2) *
                |Real.exp (-t / 2) * criticalMellinNormalizedChebyshevError t| := by
            symm
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            calc
              Real.exp (t / 2) *
                  (Real.exp (-t / 2) * |criticalMellinNormalizedChebyshevError t|) =
                  (Real.exp (t / 2) * Real.exp (-t / 2)) *
                    |criticalMellinNormalizedChebyshevError t| := by ring
              _ = |criticalMellinNormalizedChebyshevError t| := by
                rw [← Real.exp_add]
                rw [show t / 2 + -t / 2 = 0 by ring, Real.exp_zero, one_mul]
          rw [Real.norm_eq_abs, hrewrite]
          simpa only [mul_comm] using
            (mul_lt_mul_of_pos_left hpoint' (Real.exp_pos (t / 2))).le)
        hgInt
  have hExpInt : ∫ t in T'..h, Real.exp (t / 2) =
      2 * Real.exp (h / 2) - 2 * Real.exp (T' / 2) := by
    let F : ℝ → ℝ := fun x => 2 * Real.exp (x / 2)
    have hderiv : ∀ x ∈ Set.uIcc T' h, HasDerivAt F (Real.exp (x / 2)) x := by
      intro x _
      dsimp only [F]
      have hlin : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
        simpa using (hasDerivAt_id x).div_const (2 : ℝ)
      have h' : HasDerivAt (fun y : ℝ => 2 * Real.exp (y / 2))
          (2 * (Real.exp (x / 2) * (1 / 2))) x := by
        simpa only [Function.comp_apply] using
          ((Real.hasDerivAt_exp (x / 2)).comp x hlin).const_mul (2 : ℝ)
      convert h' using 1
      ring
    have hint : IntervalIntegrable (fun x : ℝ => Real.exp (x / 2)) volume T' h :=
      (Real.continuous_exp.comp (continuous_id.div_const 2)).intervalIntegrable _ _
    simpa only [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have htailCalc :
      ∫ t in T'..h, eps / 4 * Real.exp (t / 2) =
        eps / 2 * (Real.exp (h / 2) - Real.exp (T' / 2)) := by
    rw [intervalIntegral.integral_const_mul, hExpInt]
    ring
  have htailSmall :
      |Real.exp (-h / 2) *
        (∫ t in T'..h, criticalMellinNormalizedChebyshevError t)| ≤ eps / 2 := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-h / 2) * |∫ t in T'..h, criticalMellinNormalizedChebyshevError t| ≤
          Real.exp (-h / 2) * (∫ t in T'..h, eps / 4 * Real.exp (t / 2)) :=
        mul_le_mul_of_nonneg_left htailBound (Real.exp_pos _).le
      _ = Real.exp (-h / 2) *
          (eps / 2 * (Real.exp (h / 2) - Real.exp (T' / 2))) := by rw [htailCalc]
      _ ≤ Real.exp (-h / 2) * (eps / 2 * Real.exp (h / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have hmono : Real.exp (T' / 2) ≤ Real.exp (h / 2) :=
          Real.exp_le_exp.mpr (by linarith)
        nlinarith [Real.exp_pos (T' / 2)]
      _ = eps / 2 := by
        calc
          Real.exp (-h / 2) * (eps / 2 * Real.exp (h / 2)) =
              eps / 2 * (Real.exp (-h / 2) * Real.exp (h / 2)) := by ring
          _ = eps / 2 := by
            rw [← Real.exp_add]
            rw [show -h / 2 + h / 2 = 0 by ring, Real.exp_zero, mul_one]
  have hheadInt : IntervalIntegrable criticalMellinNormalizedChebyshevError volume 0 T' := by
    refine intervalIntegrable_of_bound_on
      (C := criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp T') +
        Real.exp T')
      measurable_criticalMellinNormalizedChebyshevError hT0 ?_
    intro x hx
    exact abs_criticalMellinNormalizedChebyshevError_le_endpoint hx
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hheadInt htailInt
  change |Real.exp (-h / 2) *
    (∫ t in (0 : ℝ)..h, criticalMellinNormalizedChebyshevError t) - 0| < eps
  rw [sub_zero, ← hsplit]
  calc
    |Real.exp (-h / 2) *
        ((∫ t in (0 : ℝ)..T', criticalMellinNormalizedChebyshevError t) +
          ∫ t in T'..h, criticalMellinNormalizedChebyshevError t)| ≤
        |Real.exp (-h / 2) * A| +
          |Real.exp (-h / 2) *
            (∫ t in T'..h, criticalMellinNormalizedChebyshevError t)| := by
      dsimp only [A]
      rw [mul_add]
      exact abs_add_le _ _
    _ < eps := by linarith

/-- The literal completed critical-Mellin error is negligible relative to polar mass.

This is the exact consequence of the DLV P driver after the causal Volterra completion; it is
not a bound on the signed collective coverage seam. -/
theorem tendsto_exp_neg_half_mul_criticalMellinCompletedError_atTop_zero :
    Tendsto (fun h : ℝ => Real.exp (-h / 2) * criticalMellinCompletedError h)
      atTop (𝓝 0) := by
  have harg : Tendsto (fun h : ℝ => -h / 2) atTop atBot := by
    have hmul := tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    have hneg := tendsto_neg_atBot_iff.2 hmul
    convert hneg using 1
    ext h
    simp only [id_eq]
    ring
  have hexp : Tendsto (fun h : ℝ => Real.exp (-h / 2)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp harg using 1
    ext h
    simp only [Function.comp_apply]
  have hexpsq : Tendsto (fun h : ℝ =>
      Real.exp (-h / 2) * Real.exp (-h / 2)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hexp.mul hexp
  have hfirst : Tendsto (fun h : ℝ => Real.exp (-h / 2) * (1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hexp.mul_const (1 : ℝ)
  have hdriver :=
    tendsto_exp_neg_half_mul_criticalMellinNormalizedChebyshevError_atTop_zero
  have hprimitive :=
    tendsto_exp_neg_half_mul_criticalMellinNormalizedChebyshevPrimitive_atTop_zero
  have hmodel := ((hfirst.sub (hexpsq.const_mul (2 : ℝ))).sub hdriver).sub
    (hprimitive.const_mul (1 / 2 : ℝ))
  have hmodelzero : Tendsto (fun h : ℝ =>
      Real.exp (-h / 2) * 1 -
        2 * (Real.exp (-h / 2) * Real.exp (-h / 2)) -
        Real.exp (-h / 2) * criticalMellinNormalizedChebyshevError h -
        (1 / 2 : ℝ) * (Real.exp (-h / 2) *
          ∫ t in (0 : ℝ)..h, criticalMellinNormalizedChebyshevError t))
      atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero, zero_sub, sub_zero] using hmodel
  apply hmodelzero.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
  rw [criticalMellinCompletedError_eq_volterraPotential hh,
    criticalMellinChebyshevVolterraPotential, sqrt_exp_eq_exp_half]
  have hinv : (Real.exp (h / 2))⁻¹ = Real.exp (-h / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have htwo : (2 : ℝ) / Real.exp (h / 2) =
      2 * Real.exp (-h / 2) := by
    rw [div_eq_mul_inv, hinv]
  rw [htwo, intervalIntegral.integral_of_le hh]
  ring

end RHTower
