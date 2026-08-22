import GaloisForLFunctions.RHTower.ScrewTailPrimitive

/-!
# The half-weight moment of the screw tail primitive
-/

namespace RHTower

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- The exact primitive of `A_∞(h) e^{-h/2}`. -/
def screwHalfMomentPrimitive (h : ℝ) : ℝ :=
  -2 * Real.exp (-(h / 2)) * Real.arctan (Real.exp (-(h / 2)))
    - (Real.exp (-(h / 2)) + 1) * Real.log (1 + Real.exp (-(h / 2)))
    + (Real.exp (-(h / 2)) - 1) * Real.log (1 - Real.exp (-(h / 2)))
    + Real.log (1 + (Real.exp (-(h / 2))) ^ 2)

theorem hasDerivAt_screwHalfMomentPrimitive {h : ℝ} (hh : 0 < h) :
    HasDerivAt screwHalfMomentPrimitive
      (screwTailPrimitive h * Real.exp (-(h / 2))) h := by
  have h0 := exp_neg_half_pos h
  have h1 := exp_neg_half_lt_one hh
  set u : ℝ := Real.exp (-(h / 2)) with hu
  have hup : HasDerivAt (fun t : ℝ => Real.exp (-(t / 2))) (-(u / 2)) h :=
    hasDerivAt_expNegHalf h
  have hu2 : HasDerivAt (fun t : ℝ => (Real.exp (-(t / 2))) ^ 2)
      ((2 : ℕ) * u ^ 1 * (-(u / 2))) h := hup.pow 2
  have harc : HasDerivAt (fun t : ℝ => Real.arctan (Real.exp (-(t / 2))))
      ((1 / (1 + u ^ 2)) * (-(u / 2))) h := by
    have hcomp := (Real.hasDerivAt_arctan u).comp h hup
    simpa [Function.comp_def] using hcomp
  have hlogp : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (-(t / 2))))
      ((-(u / 2)) / (1 + u)) h := by
    have := (hup.const_add 1).log (by linarith)
    simpa using this
  have hlogm : HasDerivAt (fun t : ℝ => Real.log (1 - Real.exp (-(t / 2))))
      ((u / 2) / (1 - u)) h := by
    have := (hup.const_sub 1).log (by linarith)
    simpa using this
  have hlogq : HasDerivAt (fun t : ℝ => Real.log (1 + (Real.exp (-(t / 2))) ^ 2))
      (((2 : ℕ) * u ^ 1 * (-(u / 2))) / (1 + u ^ 2)) h := by
    have := (hu2.const_add 1).log (by positivity)
    simpa using this
  have hT1 := ((hup.const_mul (-2 : ℝ))).mul harc
  have hT2 := ((hup.add_const 1)).mul hlogp
  have hT3 := ((hup.sub_const 1)).mul hlogm
  have hsum := ((hT1.sub hT2).add hT3).add hlogq
  refine hsum.congr_deriv ?_
  rw [screwTailPrimitive, ← hu]
  have hne1 : (1 : ℝ) + u ≠ 0 := by linarith
  have hne2 : (1 : ℝ) - u ≠ 0 := by linarith
  have hne3 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem continuous_screwHalfMomentPrimitive : Continuous screwHalfMomentPrimitive := by
  have hexp : Continuous fun h : ℝ => Real.exp (-(h / 2)) := by fun_prop
  have hT1 : Continuous fun h : ℝ =>
      -2 * Real.exp (-(h / 2)) * Real.arctan (Real.exp (-(h / 2))) :=
    (hexp.const_mul _).mul (Real.continuous_arctan.comp hexp)
  have hT2 : Continuous fun h : ℝ =>
      (Real.exp (-(h / 2)) + 1) * Real.log (1 + Real.exp (-(h / 2))) := by
    refine (hexp.add continuous_const).mul ?_
    refine Real.continuousOn_log.comp_continuous (continuous_const.add hexp) fun h => ?_
    have := Real.exp_pos (-(h / 2))
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    linarith
  have hT3 : Continuous fun h : ℝ =>
      (Real.exp (-(h / 2)) - 1) * Real.log (1 - Real.exp (-(h / 2))) := by
    have hrw : (fun h : ℝ => (Real.exp (-(h / 2)) - 1) * Real.log (1 - Real.exp (-(h / 2))))
        = fun h : ℝ => -((1 - Real.exp (-(h / 2))) * Real.log (1 - Real.exp (-(h / 2)))) := by
      funext h
      ring
    rw [hrw]
    exact (Real.continuous_mul_log.comp (continuous_const.sub hexp)).neg
  have hT4 : Continuous fun h : ℝ => Real.log (1 + (Real.exp (-(h / 2))) ^ 2) := by
    refine Real.continuousOn_log.comp_continuous (continuous_const.add (hexp.pow 2)) fun h => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    nlinarith [Real.exp_pos (-(h / 2))]
  exact ((hT1.sub hT2).add hT3).add hT4

theorem screwHalfMomentPrimitive_tendsto_zero :
    Tendsto screwHalfMomentPrimitive atTop (𝓝 0) := by
  have hu := tendsto_exp_neg_half_atTop
  have hu2 : Tendsto (fun h : ℝ => (Real.exp (-(h / 2))) ^ 2) atTop (𝓝 0) := by
    simpa using hu.pow 2
  have hlogp : Tendsto (fun h : ℝ => Real.log (1 + Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 + Real.exp (-(h / 2))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hu
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have hlogm : Tendsto (fun h : ℝ => Real.log (1 - Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 - Real.exp (-(h / 2))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hu
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have hlogq : Tendsto (fun h : ℝ => Real.log (1 + (Real.exp (-(h / 2))) ^ 2)) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 + (Real.exp (-(h / 2))) ^ 2) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hu2
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have harc : Tendsto (fun h : ℝ => Real.arctan (Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_arctan.continuousAt.tendsto.comp hu
  have hfun : screwHalfMomentPrimitive = fun h : ℝ =>
      -2 * Real.exp (-(h / 2)) * Real.arctan (Real.exp (-(h / 2)))
        - (Real.exp (-(h / 2)) + 1) * Real.log (1 + Real.exp (-(h / 2)))
        + (Real.exp (-(h / 2)) - 1) * Real.log (1 - Real.exp (-(h / 2)))
        + Real.log (1 + (Real.exp (-(h / 2))) ^ 2) := rfl
  rw [hfun]
  have t1 : Tendsto (fun h : ℝ =>
      -2 * Real.exp (-(h / 2)) * Real.arctan (Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (-2 : ℝ) hu).mul harc
  have t2 : Tendsto (fun h : ℝ =>
      (Real.exp (-(h / 2)) + 1) * Real.log (1 + Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    simpa using (hu.add_const 1).mul hlogp
  have t3 : Tendsto (fun h : ℝ =>
      (Real.exp (-(h / 2)) - 1) * Real.log (1 - Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    simpa using (hu.sub_const 1).mul hlogm
  simpa using ((t1.sub t2).add t3).add hlogq

theorem screwHalfMomentPrimitive_zero :
    screwHalfMomentPrimitive 0 = -(Real.log 2 + Real.pi / 2) := by
  rw [screwHalfMomentPrimitive]
  norm_num [Real.arctan_one]
  ring

theorem screwTailPrimitive_mul_exp_half_nonneg {h : ℝ} (hh : 0 < h) :
    0 ≤ screwTailPrimitive h * Real.exp (-(h / 2)) := by
  have h0 := exp_neg_half_pos h
  have h1 := exp_neg_half_lt_one hh
  have hlogm : Real.log (1 - Real.exp (-(h / 2))) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  have hlogp : 0 ≤ Real.log (1 + Real.exp (-(h / 2))) :=
    Real.log_nonneg (by linarith)
  have harc : 0 ≤ Real.arctan (Real.exp (-(h / 2))) := Real.arctan_nonneg.mpr (le_of_lt h0)
  have hA : 0 ≤ screwTailPrimitive h := by
    rw [screwTailPrimitive]
    have : 0 ≤ (Real.log (1 + Real.exp (-(h / 2))) - Real.log (1 - Real.exp (-(h / 2)))) / 2 := by
      linarith
    linarith
  exact mul_nonneg hA (le_of_lt (Real.exp_pos _))

/-- The half-weight moment of the tail primitive is integrable on the half-line. -/
theorem integrableOn_screwTailPrimitive_mul_exp_half :
    IntegrableOn (fun h : ℝ => screwTailPrimitive h * Real.exp (-(h / 2))) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (g := screwHalfMomentPrimitive) (l := 0)
    (continuous_screwHalfMomentPrimitive.continuousWithinAt)
    (fun x hx => hasDerivAt_screwHalfMomentPrimitive hx)
    (fun x hx => screwTailPrimitive_mul_exp_half_nonneg hx)
    screwHalfMomentPrimitive_tendsto_zero

/-- The exact half-weight moment `∫_0^∞ A_∞(h) e^{-h/2} dh = log 2 + π/2`. -/
theorem integral_Ioi_screwTailPrimitive_mul_exp_half :
    ∫ h in Ioi (0 : ℝ), screwTailPrimitive h * Real.exp (-(h / 2))
      = Real.log 2 + Real.pi / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := screwHalfMomentPrimitive) (a := (0 : ℝ))
    (continuous_screwHalfMomentPrimitive.continuousWithinAt)
    (fun x hx => hasDerivAt_screwHalfMomentPrimitive hx)
    (fun x hx => screwTailPrimitive_mul_exp_half_nonneg hx)
    screwHalfMomentPrimitive_tendsto_zero
  rw [screwHalfMomentPrimitive_zero] at h
  rw [h]
  ring

end

end RHTower
