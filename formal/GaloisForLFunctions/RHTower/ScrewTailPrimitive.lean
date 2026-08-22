import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The Gamma tail kernel and its exact primitive
-/

namespace RHTower

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- `k_∞(h) = e^{-h/2} / (1 - e^{-2h})`, equation `(6)`. -/
def screwTailKernel (h : ℝ) : ℝ := Real.exp (-(h / 2)) / (1 - Real.exp (-(2 * h)))

/-- The exact tail primitive `A_∞`, equation `(8)`, written logarithmically. -/
def screwTailPrimitive (h : ℝ) : ℝ :=
  (Real.log (1 + Real.exp (-(h / 2))) - Real.log (1 - Real.exp (-(h / 2)))) / 2
    + Real.arctan (Real.exp (-(h / 2)))

/-- The canonical contact normalization `κ_∞ = (log(8π) + γ)/2 + π/4`, equation `(13)`. -/
def screwContactConst : ℝ :=
  (Real.log (8 * Real.pi) + Real.eulerMascheroniConstant) / 2 + Real.pi / 4

/-! ## Elementary bounds on the exponential coordinate -/

theorem exp_neg_half_pos (h : ℝ) : 0 < Real.exp (-(h / 2)) := Real.exp_pos _

theorem exp_neg_half_lt_one {h : ℝ} (hh : 0 < h) : Real.exp (-(h / 2)) < 1 := by
  rw [Real.exp_lt_one_iff]
  linarith

theorem hasDerivAt_expNegHalf (h : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t / 2))) (-(Real.exp (-(h / 2)) / 2)) h := by
  have hin : HasDerivAt (fun t : ℝ => -(t / 2)) (-(1 / 2 : ℝ)) h := by
    simpa [Pi.neg_def] using ((hasDerivAt_id h).div_const 2).neg
  exact hin.exp.congr_deriv (by ring)

theorem exp_neg_half_pow_four (h : ℝ) :
    (Real.exp (-(h / 2))) ^ 4 = Real.exp (-(2 * h)) := by
  rw [← Real.exp_nat_mul]
  norm_num
  ring_nf

theorem exp_neg_half_pow_three (h : ℝ) :
    (Real.exp (-(h / 2))) ^ 3 = Real.exp (-(3 * h / 2)) := by
  rw [← Real.exp_nat_mul]
  norm_num
  ring_nf

/-- **Equation `(8)`.**  The logarithmic primitive is the stated inverse-hyperbolic form. -/
theorem screwTailPrimitive_eq_artanh_add_arctan {h : ℝ} (hh : 0 < h) :
    screwTailPrimitive h
      = Real.artanh (Real.exp (-(h / 2))) + Real.arctan (Real.exp (-(h / 2))) := by
  have h0 := exp_neg_half_pos h
  have h1 := exp_neg_half_lt_one hh
  have hmem : Real.exp (-(h / 2)) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, le_of_lt h1⟩
  rw [screwTailPrimitive, Real.artanh_eq_half_log hmem,
    Real.log_div (by linarith) (by linarith)]
  ring

/-! ## The tail primitive differentiates to the tail kernel -/

/-- **Equation `(9)`.**  `A_∞' = -k_∞`. -/
theorem hasDerivAt_screwTailPrimitive {h : ℝ} (hh : 0 < h) :
    HasDerivAt screwTailPrimitive (-(screwTailKernel h)) h := by
  have h0 := exp_neg_half_pos h
  have h1 := exp_neg_half_lt_one hh
  set u : ℝ := Real.exp (-(h / 2)) with hu
  have hup : HasDerivAt (fun t : ℝ => Real.exp (-(t / 2))) (-(u / 2)) h :=
    hasDerivAt_expNegHalf h
  have hd1 : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (-(t / 2))))
      ((-(u / 2)) / (1 + u)) h := by
    have := (hup.const_add 1).log (by linarith)
    simpa using this
  have hd2 : HasDerivAt (fun t : ℝ => Real.log (1 - Real.exp (-(t / 2))))
      ((u / 2) / (1 - u)) h := by
    have := ((hup.const_sub 1).log (by linarith))
    simpa using this
  have hd3 : HasDerivAt (fun t : ℝ => Real.arctan (Real.exp (-(t / 2))))
      ((1 / (1 + u ^ 2)) * (-(u / 2))) h := by
    have hcomp := (Real.hasDerivAt_arctan u).comp h hup
    simpa [Function.comp_def] using hcomp
  have hsum := ((hd1.sub hd2).div_const 2).add hd3
  refine hsum.congr_deriv ?_
  rw [screwTailKernel, ← exp_neg_half_pow_four h, ← hu]
  have hne1 : (1 : ℝ) + u ≠ 0 := by linarith
  have hne2 : (1 : ℝ) - u ≠ 0 := by linarith
  have hne3 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  have hne4 : (1 : ℝ) - u ^ 4 ≠ 0 := by
    have : u ^ 4 < 1 := pow_lt_one₀ (le_of_lt h0) h1 (by norm_num)
    linarith
  field_simp
  ring

theorem tendsto_exp_neg_half_atTop : Tendsto (fun h : ℝ => Real.exp (-(h / 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun h : ℝ => h / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)

theorem screwTailPrimitive_tendsto_zero :
    Tendsto screwTailPrimitive atTop (𝓝 0) := by
  have hu := tendsto_exp_neg_half_atTop
  have hA : Tendsto (fun h : ℝ => Real.log (1 + Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 + Real.exp (-(h / 2))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hu
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have hB : Tendsto (fun h : ℝ => Real.log (1 - Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 - Real.exp (-(h / 2))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hu
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have hC : Tendsto (fun h : ℝ => Real.arctan (Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_arctan.continuousAt.tendsto.comp hu
  have hfun : screwTailPrimitive = fun h : ℝ =>
      (Real.log (1 + Real.exp (-(h / 2))) - Real.log (1 - Real.exp (-(h / 2)))) / 2
        + Real.arctan (Real.exp (-(h / 2))) := rfl
  rw [hfun]
  simpa using ((hA.sub hB).div_const 2).add hC

/-! ## The tail kernel integrates to the primitive -/

theorem screwTailKernel_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ screwTailKernel t := by
  have h1 : Real.exp (-(2 * t)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (by linarith)

theorem hasDerivAt_neg_screwTailPrimitive {h : ℝ} (hh : 0 < h) :
    HasDerivAt (fun t : ℝ => -screwTailPrimitive t) (screwTailKernel h) h := by
  simpa [Pi.neg_def] using (hasDerivAt_screwTailPrimitive hh).neg

theorem integrableOn_screwTailKernel {a : ℝ} (ha : 0 < a) :
    IntegrableOn screwTailKernel (Ioi a) := by
  have hlim : Tendsto (fun t : ℝ => -screwTailPrimitive t) atTop (𝓝 0) := by
    simpa [Pi.neg_def] using screwTailPrimitive_tendsto_zero.neg
  exact integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -screwTailPrimitive t) (l := 0)
    ((hasDerivAt_neg_screwTailPrimitive ha).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_neg_screwTailPrimitive (lt_trans ha hx))
    (fun x hx => screwTailKernel_nonneg (lt_trans ha hx)) hlim

/-- **Equations `(7)`–`(8)`.**  The tail integral of `k_∞` is the exact primitive `A_∞`. -/
theorem integral_Ioi_screwTailKernel {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi a, screwTailKernel t = screwTailPrimitive a := by
  have hlim : Tendsto (fun t : ℝ => -screwTailPrimitive t) atTop (𝓝 0) := by
    simpa [Pi.neg_def] using screwTailPrimitive_tendsto_zero.neg
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun t : ℝ => -screwTailPrimitive t)
    ((hasDerivAt_neg_screwTailPrimitive ha).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_neg_screwTailPrimitive (lt_trans ha hx))
    (fun x hx => screwTailKernel_nonneg (lt_trans ha hx)) hlim
  simpa using h

/-! ## The exact contact moment `(14)` -/

/-- The exact primitive of `A_∞(h) e^{-3h/2}`. -/
def screwMomentPrimitive (h : ℝ) : ℝ :=
  (1 / 3) * ((Real.exp (-(h / 2))) ^ 3 - 1) * Real.log (1 - Real.exp (-(h / 2)))
    - (1 / 3) * ((Real.exp (-(h / 2))) ^ 3 + 1) * Real.log (1 + Real.exp (-(h / 2)))
    - (2 / 3) * (Real.exp (-(h / 2))) ^ 3 * Real.arctan (Real.exp (-(h / 2)))
    - (1 / 3) * Real.log (1 + (Real.exp (-(h / 2))) ^ 2)

theorem hasDerivAt_screwMomentPrimitive {h : ℝ} (hh : 0 < h) :
    HasDerivAt screwMomentPrimitive
      (screwTailPrimitive h * Real.exp (-(3 * h / 2))) h := by
  have h0 := exp_neg_half_pos h
  have h1 := exp_neg_half_lt_one hh
  set u : ℝ := Real.exp (-(h / 2)) with hu
  have hup : HasDerivAt (fun t : ℝ => Real.exp (-(t / 2))) (-(u / 2)) h :=
    hasDerivAt_expNegHalf h
  have hu3 : HasDerivAt (fun t : ℝ => (Real.exp (-(t / 2))) ^ 3)
      ((3 : ℕ) * u ^ 2 * (-(u / 2))) h := hup.pow 3
  have hu2 : HasDerivAt (fun t : ℝ => (Real.exp (-(t / 2))) ^ 2)
      ((2 : ℕ) * u ^ 1 * (-(u / 2))) h := hup.pow 2
  have hlogm : HasDerivAt (fun t : ℝ => Real.log (1 - Real.exp (-(t / 2))))
      ((u / 2) / (1 - u)) h := by
    have := (hup.const_sub 1).log (by linarith)
    simpa using this
  have hlogp : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (-(t / 2))))
      ((-(u / 2)) / (1 + u)) h := by
    have := (hup.const_add 1).log (by linarith)
    simpa using this
  have hlogq : HasDerivAt (fun t : ℝ => Real.log (1 + (Real.exp (-(t / 2))) ^ 2))
      (((2 : ℕ) * u ^ 1 * (-(u / 2))) / (1 + u ^ 2)) h := by
    have := (hu2.const_add 1).log (by positivity)
    simpa using this
  have harc : HasDerivAt (fun t : ℝ => Real.arctan (Real.exp (-(t / 2))))
      ((1 / (1 + u ^ 2)) * (-(u / 2))) h := by
    have hcomp := (Real.hasDerivAt_arctan u).comp h hup
    simpa [Function.comp_def] using hcomp
  have hT1 := (((hu3.sub_const 1).const_mul (1 / 3 : ℝ))).mul hlogm
  have hT2 := (((hu3.add_const 1).const_mul (1 / 3 : ℝ))).mul hlogp
  have hT3 := ((hu3.const_mul (2 / 3 : ℝ))).mul harc
  have hT4 := hlogq.const_mul (1 / 3 : ℝ)
  have hsum := ((hT1.sub hT2).sub hT3).sub hT4
  refine hsum.congr_deriv ?_
  rw [screwTailPrimitive, ← hu, ← exp_neg_half_pow_three h, ← hu]
  have hne1 : (1 : ℝ) + u ≠ 0 := by linarith
  have hne2 : (1 : ℝ) - u ≠ 0 := by linarith
  have hne3 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem continuous_screwMomentPrimitive : Continuous screwMomentPrimitive := by
  have hexp : Continuous fun h : ℝ => Real.exp (-(h / 2)) := by fun_prop
  have hfirst : Continuous fun h : ℝ =>
      (1 / 3) * ((Real.exp (-(h / 2))) ^ 3 - 1) * Real.log (1 - Real.exp (-(h / 2))) := by
    have hrw : (fun h : ℝ =>
        (1 / 3) * ((Real.exp (-(h / 2))) ^ 3 - 1) * Real.log (1 - Real.exp (-(h / 2))))
        = fun h : ℝ => (-(1 / 3) * ((Real.exp (-(h / 2))) ^ 2 + Real.exp (-(h / 2)) + 1)) *
          ((1 - Real.exp (-(h / 2))) * Real.log (1 - Real.exp (-(h / 2)))) := by
      funext h
      ring
    rw [hrw]
    exact (((hexp.pow 2).add hexp).add continuous_const).const_mul _ |>.mul
      (Real.continuous_mul_log.comp (continuous_const.sub hexp))
  have hsecond : Continuous fun h : ℝ =>
      (1 / 3) * ((Real.exp (-(h / 2))) ^ 3 + 1) * Real.log (1 + Real.exp (-(h / 2))) := by
    refine (((hexp.pow 3).add continuous_const).const_mul _).mul ?_
    refine Real.continuousOn_log.comp_continuous (continuous_const.add hexp) fun h => ?_
    have := Real.exp_pos (-(h / 2))
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    linarith
  have hthird : Continuous fun h : ℝ =>
      (2 / 3) * (Real.exp (-(h / 2))) ^ 3 * Real.arctan (Real.exp (-(h / 2))) :=
    ((hexp.pow 3).const_mul _).mul (Real.continuous_arctan.comp hexp)
  have hfourth : Continuous fun h : ℝ =>
      (1 / 3) * Real.log (1 + (Real.exp (-(h / 2))) ^ 2) := by
    refine Continuous.const_mul ?_ _
    refine Real.continuousOn_log.comp_continuous (continuous_const.add (hexp.pow 2)) fun h => ?_
    have := Real.exp_pos (-(h / 2))
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    nlinarith [Real.exp_pos (-(h / 2))]
  exact ((hfirst.sub hsecond).sub hthird).sub hfourth

theorem screwMomentPrimitive_tendsto_zero :
    Tendsto screwMomentPrimitive atTop (𝓝 0) := by
  have hu := tendsto_exp_neg_half_atTop
  have hu3 : Tendsto (fun h : ℝ => (Real.exp (-(h / 2))) ^ 3) atTop (𝓝 0) := by
    simpa using hu.pow 3
  have hu2 : Tendsto (fun h : ℝ => (Real.exp (-(h / 2))) ^ 2) atTop (𝓝 0) := by
    simpa using hu.pow 2
  have hlogm : Tendsto (fun h : ℝ => Real.log (1 - Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 - Real.exp (-(h / 2))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hu
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have hlogp : Tendsto (fun h : ℝ => Real.log (1 + Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 + Real.exp (-(h / 2))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hu
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have hlogq : Tendsto (fun h : ℝ => Real.log (1 + (Real.exp (-(h / 2))) ^ 2)) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
    have h2 : Tendsto (fun h : ℝ => 1 + (Real.exp (-(h / 2))) ^ 2) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hu2
    simpa [Function.comp_def] using hc.tendsto.comp h2
  have harc : Tendsto (fun h : ℝ => Real.arctan (Real.exp (-(h / 2)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_arctan.continuousAt.tendsto.comp hu
  have hfun : screwMomentPrimitive = fun h : ℝ =>
      (1 / 3) * ((Real.exp (-(h / 2))) ^ 3 - 1) * Real.log (1 - Real.exp (-(h / 2)))
        - (1 / 3) * ((Real.exp (-(h / 2))) ^ 3 + 1) * Real.log (1 + Real.exp (-(h / 2)))
        - (2 / 3) * (Real.exp (-(h / 2))) ^ 3 * Real.arctan (Real.exp (-(h / 2)))
        - (1 / 3) * Real.log (1 + (Real.exp (-(h / 2))) ^ 2) := rfl
  rw [hfun]
  have t1 : Tendsto (fun h : ℝ =>
      (1 / 3 : ℝ) * ((Real.exp (-(h / 2))) ^ 3 - 1) * Real.log (1 - Real.exp (-(h / 2))))
      atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (1 / 3 : ℝ) (hu3.sub_const 1)).mul hlogm
  have t2 : Tendsto (fun h : ℝ =>
      (1 / 3 : ℝ) * ((Real.exp (-(h / 2))) ^ 3 + 1) * Real.log (1 + Real.exp (-(h / 2))))
      atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (1 / 3 : ℝ) (hu3.add_const 1)).mul hlogp
  have t3 : Tendsto (fun h : ℝ =>
      (2 / 3 : ℝ) * (Real.exp (-(h / 2))) ^ 3 * Real.arctan (Real.exp (-(h / 2))))
      atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (2 / 3 : ℝ) hu3).mul harc
  have t4 : Tendsto (fun h : ℝ =>
      (1 / 3 : ℝ) * Real.log (1 + (Real.exp (-(h / 2))) ^ 2)) atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_mul (1 / 3 : ℝ) hlogq
  simpa using ((t1.sub t2).sub t3).sub t4

theorem screwMomentPrimitive_zero :
    screwMomentPrimitive 0 = -(Real.log 2 + Real.pi / 6) := by
  rw [screwMomentPrimitive]
  norm_num [Real.arctan_one]
  ring

theorem screwTailPrimitive_mul_exp_nonneg {h : ℝ} (hh : 0 < h) :
    0 ≤ screwTailPrimitive h * Real.exp (-(3 * h / 2)) := by
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

/-- **Equation `(14)`.**  `∫_0^∞ A_∞(h) e^{-3h/2} dh = log 2 + π/6`. -/
theorem integral_Ioi_screwTailPrimitive_mul_exp :
    ∫ h in Ioi (0 : ℝ), screwTailPrimitive h * Real.exp (-(3 * h / 2))
      = Real.log 2 + Real.pi / 6 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := screwMomentPrimitive) (a := (0 : ℝ))
    (continuous_screwMomentPrimitive.continuousWithinAt)
    (fun x hx => hasDerivAt_screwMomentPrimitive hx)
    (fun x hx => screwTailPrimitive_mul_exp_nonneg hx)
    screwMomentPrimitive_tendsto_zero
  rw [screwMomentPrimitive_zero] at h
  rw [h]
  ring

end

end RHTower
