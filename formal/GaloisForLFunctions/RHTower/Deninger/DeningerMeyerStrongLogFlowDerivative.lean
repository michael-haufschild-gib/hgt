import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogOperatorContinuity
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogFlowContinuity
import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strong differentiation of the original Meyer dilation flow

The two-sided Schwartz translation argument extends to every exponential
derivative gauge. The resulting difference quotient converges in the actual
strong source topology. Consequently every continuous source functional reads
the original flow with its actual logarithmic generator as derivative.
-/

open Filter Set Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

private theorem strong_iteratedDeriv {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (n : ℕ) :
    DeningerMeyerStrongLogDecay (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

private theorem weighted_shift_bound (g : DeningerMeyerStrongLogTarget)
    (n : ℕ) (k : ℤ) (t u : ℝ) (hu : |u| ≤ 1) :
    ‖(Real.exp t ^ (k : ℝ) : ℝ) • iteratedDeriv n g.val (t + u)‖ ≤
      Real.exp |(k : ℝ)| * ‖deningerMeyerStrongLogGauge n k g‖ := by
  have hpoint := (deningerMeyerStrongLogGauge n k g).norm_coe_le_norm (t + u)
  rw [deningerMeyerStrongLogGauge_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _),
    ← Real.exp_mul] at hpoint
  have hphase : Real.exp (-((k : ℝ) * u)) ≤ Real.exp |(k : ℝ)| := by
    apply Real.exp_le_exp.mpr
    calc
      -((k : ℝ) * u) ≤ |(k : ℝ) * u| := neg_le_abs _
      _ = |(k : ℝ)| * |u| := abs_mul _ _
      _ ≤ |(k : ℝ)| := by nlinarith [abs_nonneg (k : ℝ)]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) _), ← Real.exp_mul]
  calc
    _ = Real.exp (-((k : ℝ) * u)) *
        (Real.exp ((t + u) * (k : ℝ)) * ‖iteratedDeriv n g.val (t + u)‖) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul hphase hpoint (by positivity) (by positivity)

private theorem weighted_right_slope_error (g : DeningerMeyerStrongLogTarget)
    (n : ℕ) (k : ℤ) (t h : ℝ) (hh0 : h ≠ 0) (hh1 : |h| ≤ 1) :
    ‖(Real.exp t ^ (k : ℝ) : ℝ) •
      ((h⁻¹ : ℝ) • (iteratedDeriv n g.val (t + h) - iteratedDeriv n g.val t) -
        iteratedDeriv (n + 1) g.val t)‖ ≤
      (Real.exp |(k : ℝ)| * ‖deningerMeyerStrongLogGauge (n + 2) k g‖) * |h| := by
  let r := |h|
  let c := h / r
  let f := iteratedDeriv n g.val
  let w := Real.exp t ^ (k : ℝ)
  let fw : ℝ → ℂ := fun x => w • f x
  have hr : 0 < r := abs_pos.mpr hh0
  have hc : |c| = 1 := by
    dsimp [c, r]
    rw [abs_div, abs_abs, div_self (ne_of_gt (abs_pos.mpr hh0))]
  have hcr : c * r = h := by dsimp [c, r]; field_simp
  have hf : ContDiff ℝ 2 f :=
    (strong_iteratedDeriv g.property n).smooth.of_le (by norm_cast)
  have hfw : ContDiff ℝ 2 fw := hf.const_smul w
  have hsecond (x : ℝ) : iteratedDeriv 2 fw x = w • iteratedDeriv (n + 2) g.val x := by
    change iteratedDeriv 2 (w • f) x = _
    rw [iteratedDeriv_const_smul hf.contDiffAt w,
      SchwartzMap.iteratedDeriv_iteratedDeriv]
  have hfirst : deriv fw t = w • iteratedDeriv (n + 1) g.val t := by
    rw [← congrFun iteratedDeriv_one t]
    change iteratedDeriv 1 (w • f) t = _
    rw [iteratedDeriv_const_smul (n := 1) (hf.of_le (by norm_num)).contDiffAt w,
      SchwartzMap.iteratedDeriv_iteratedDeriv]
  have hb : ∀ x ∈ Icc 0 r, ‖iteratedDeriv 2 fw (t + c * x)‖ ≤
      Real.exp |(k : ℝ)| * ‖deningerMeyerStrongLogGauge (n + 2) k g‖ := by
    intro x hx
    rw [hsecond]
    apply weighted_shift_bound
    rw [abs_mul, hc, one_mul, abs_of_nonneg hx.1]
    exact hx.2.trans hh1
  have hd := SchwartzMap.directionalDifferenceQuotientError_le hfw hr hc hb
  rw [hcr, hfirst] at hd
  dsimp only [fw] at hd
  rw [← smul_sub, smul_comm (h⁻¹ : ℝ) w, ← smul_sub] at hd
  exact hd

/-- Every gauge sees the correct derivative of the original translation. -/
theorem deningerMeyerStrongLogFlow_slope_error_le
    (g : DeningerMeyerStrongLogTarget) (n : ℕ) (k : ℤ)
    (h : ℝ) (hh0 : h ≠ 0) (hh1 : |h| ≤ 1) :
    ‖deningerMeyerStrongLogGaugeLinear n k
      (((h⁻¹ : ℝ) : ℂ) • (deningerMeyerStrongLogFlow h g - g) -
        deningerMeyerStrongLogGenerator g)‖ ≤
      (Real.exp |(k : ℝ)| * ‖deningerMeyerStrongLogGauge (n + 2) k g‖) * |h| := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  have hb := weighted_right_slope_error g n k t (-h) (neg_ne_zero.mpr hh0)
    (by simpa using hh1)
  rw [map_sub, map_smul, map_sub]
  change ‖(((h⁻¹ : ℝ) : ℂ) •
    (deningerMeyerStrongLogGauge n k (deningerMeyerStrongLogFlow h g) -
      deningerMeyerStrongLogGauge n k g) -
        deningerMeyerStrongLogGauge n k (deningerMeyerStrongLogGenerator g)) t‖ ≤ _
  rw [deningerMeyerStrongLogGauge_generator]
  simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.neg_apply, deningerMeyerStrongLogGauge_apply]
  change ‖(_ : ℂ) * (_ * iteratedDeriv n (fun x => g.val (x - h)) t -
    _ * iteratedDeriv n g.val t) - -(_ * iteratedDeriv (n + 1) g.val t)‖ ≤ _
  rw [iteratedDeriv_comp_sub_const]
  simp only [← sub_eq_add_neg, inv_neg, abs_neg] at hb
  rw [show (((h⁻¹ : ℝ) : ℂ) *
      (((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) * iteratedDeriv n g.val (t - h) -
        ((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) * iteratedDeriv n g.val t) -
      -(((Real.exp t ^ (k : ℝ) : ℝ) : ℂ) * iteratedDeriv (n + 1) g.val t)) =
      -((Real.exp t ^ (k : ℝ) : ℝ) •
        ((-(h⁻¹) : ℝ) • (iteratedDeriv n g.val (t - h) - iteratedDeriv n g.val t) -
          iteratedDeriv (n + 1) g.val t)) by
        simp only [Complex.real_smul, ofReal_neg]; ring, norm_neg]
  exact hb

/-- Strong difference-quotient convergence in all weights and derivative orders. -/
theorem deningerMeyerStrongLogFlow_tendsto_slope (g : DeningerMeyerStrongLogTarget) :
    Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : ℂ) • (deningerMeyerStrongLogFlow h g - g))
      (𝓝[≠] 0) (𝓝 (deningerMeyerStrongLogGenerator g)) := by
  have herr : Tendsto (fun h : ℝ =>
      ((h⁻¹ : ℝ) : ℂ) • (deningerMeyerStrongLogFlow h g - g) -
        deningerMeyerStrongLogGenerator g) (𝓝[≠] 0) (𝓝 0) := by
    change Tendsto _ _ (@nhds _ (⨅ i : ℕ × ℤ, TopologicalSpace.induced
      (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) 0)
    rw [nhds_iInf, tendsto_iInf]
    intro i
    rw [nhds_induced, map_zero, tendsto_comap_iff, tendsto_zero_iff_norm_tendsto_zero]
    have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
      simpa using continuous_abs.continuousAt.tendsto.mono_left
        (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hsmall := habs.eventually_lt_const zero_lt_one
    have hne : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      simpa using hh
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [hne, hsmall] with h hh hs
      exact deningerMeyerStrongLogFlow_slope_error_le g i.1 i.2 h hh hs.le
    · simpa using habs.const_mul
        (Real.exp |(i.2 : ℝ)| * ‖deningerMeyerStrongLogGauge (i.1 + 2) i.2 g‖)
  simpa only [sub_add_cancel, zero_add] using herr.add_const (deningerMeyerStrongLogGenerator g)

end
end RHTower
