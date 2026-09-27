import GaloisForLFunctions.RHTower.ThetaGammaPolarScalingEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The literal continuous Gamma/pole crossing current

The current integrates every continuous shift crossing an observation point.
Its interval length cancels the Gamma singularity. A uniform integrable bound
retains the whole shift ray and proves that the current vanishes at infinity.
-/

noncomputable section

open MeasureTheory Filter Set Topology

namespace RHTower.ThetaSourceWard

def thetaGammaPolarCrossingTerm (S : ThetaSource) (x u : ℝ) : ℝ :=
  thetaGammaPolarScalingKernel u * ∫ y in x..x + u, S.k y * S.k (y - u)

def thetaGammaPolarCrossingCurrent (S : ThetaSource) (x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), thetaGammaPolarCrossingTerm S x u

private theorem damped_length_bound {u : ℝ} (hu : 0 < u) :
    |thetaGammaPolarScalingKernel u| * Real.exp (-2 * u) * u ≤
      (2 * u + 1 / 2) * Real.exp (-u / 2) := by
  apply (mul_le_mul_iff_left₀ hu).mp
  nlinarith only [thetaGammaPolar_damped_square_bound hu]

def thetaGammaPolarCrossingMajorant (u : ℝ) : ℝ :=
  (2 * |u| + 1 / 2) * Real.exp (-(1 / 2) * |u|)

theorem integrable_thetaGammaPolarCrossingMajorant : Integrable thetaGammaPolarCrossingMajorant := by
  have h₀ := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have h₁ := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1
    (show (0 : ℝ) < 1 / 2 by norm_num)
  convert! (h₁.const_mul 2).add (h₀.div_const 2) using 1
  ext u
  simp only [thetaGammaPolarCrossingMajorant, Pi.add_apply, pow_zero, pow_one, one_mul]
  ring

theorem measurable_thetaGammaPolarCrossingTerm (S : ThetaSource) (x : ℝ) :
    Measurable (thetaGammaPolarCrossingTerm S x) := by
  have hc : Continuous (Function.uncurry (fun u y : ℝ => S.k y * S.k (y - u))) :=
    (S.cont.comp continuous_snd).mul (S.cont.comp (continuous_snd.sub continuous_fst))
  have h₁ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := (0 : ℝ)) hc (continuous_const.add continuous_id : Continuous (fun u : ℝ => x + u))
  have h₂ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := (0 : ℝ)) hc (continuous_const : Continuous (fun _ : ℝ => x))
  have hi : Continuous (fun u : ℝ => ∫ y in x..x + u, S.k y * S.k (y - u)) := by
    convert! h₁.sub h₂ using 1
    funext u
    exact (intervalIntegral.integral_interval_sub_left
      ((S.cont.mul (S.cont.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _)
      ((S.cont.mul (S.cont.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _)).symm
  have hm : Measurable thetaGammaPolarScalingKernel := by
    unfold thetaGammaPolarScalingKernel
    fun_prop
  exact hm.mul hi.measurable

/-- One integrable majorant controls all observation points. -/
theorem exists_thetaGammaPolarCrossingTerm_bound (S : ThetaSource) :
    ∃ C : ℝ, 0 < C ∧ ∀ x u : ℝ, 0 < u →
      ‖thetaGammaPolarCrossingTerm S x u‖ ≤ C ^ 2 * thetaGammaPolarCrossingMajorant u := by
  obtain ⟨C, hC, hb⟩ := thetaSource_shiftPair_decay S
  refine ⟨C, hC, fun x u hu => ?_⟩
  have hp (y : ℝ) : ‖S.k y * S.k (y - u)‖ ≤ C ^ 2 * Real.exp (-2 * u) := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (S.pos y) (S.pos (y - u)))]
    have he : Real.exp (-2 * |y - u|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg (y - u)])
    calc
      _ = S.k (y - u) * S.k ((y - u) + u) := by rw [sub_add_cancel, mul_comm]
      _ ≤ C ^ 2 * Real.exp (-2 * |y - u|) * Real.exp (-2 * u) := hb _ _ hu.le
      _ ≤ C ^ 2 * 1 * Real.exp (-2 * u) := by gcongr
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (fun y _ => hp y)
    (a := x) (b := x + u)
  rw [add_sub_cancel_left, abs_of_pos hu] at hi
  rw [thetaGammaPolarCrossingTerm, norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ |thetaGammaPolarScalingKernel u| * (C ^ 2 * Real.exp (-2 * u) * u) :=
      mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    _ = C ^ 2 * (|thetaGammaPolarScalingKernel u| * Real.exp (-2 * u) * u) := by ring
    _ ≤ C ^ 2 * ((2 * u + 1 / 2) * Real.exp (-u / 2)) :=
      mul_le_mul_of_nonneg_left (damped_length_bound hu) (sq_nonneg C)
    _ = _ := by
      rw [thetaGammaPolarCrossingMajorant, abs_of_pos hu,
        show -(1 / 2 : ℝ) * u = -u / 2 by ring]

theorem integrable_thetaGammaPolarCrossingTerm (S : ThetaSource) (x : ℝ) :
    IntegrableOn (thetaGammaPolarCrossingTerm S x) (Ioi (0 : ℝ)) := by
  obtain ⟨C, _, hb⟩ := exists_thetaGammaPolarCrossingTerm_bound S
  apply (integrable_thetaGammaPolarCrossingMajorant.integrableOn.const_mul (C ^ 2)).mono'
    (measurable_thetaGammaPolarCrossingTerm S x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact hb x u hu

theorem hasDerivAt_thetaGammaPolarCrossingTerm (S : ThetaSource) (x u : ℝ) :
    HasDerivAt (fun z => thetaGammaPolarCrossingTerm S z u)
      (thetaGammaPolarScalingKernel u * S.k x * (S.k (x + u) - S.k (x - u))) x := by
  let f := fun y : ℝ => S.k y * S.k (y - u)
  have hc : Continuous f := S.cont.mul (S.cont.comp (continuous_id.sub continuous_const))
  have hd (z : ℝ) : HasDerivAt (fun b => ∫ y in (0 : ℝ)..b, f y) (f z) z :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := (((hd (x + u)).comp x ((hasDerivAt_id x).add_const u)).sub
    (hd x)).const_mul (thetaGammaPolarScalingKernel u)
  convert! h using 1
  · funext z
    simp only [Function.comp_apply, Pi.sub_apply, id_eq]
    rw [intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 (z + u)) (hc.intervalIntegrable 0 z)]
    rfl
  · simp only [f, add_sub_cancel_right, mul_one]
    ring

private theorem integrable_shift_link (S : ThetaSource) (u : ℝ) :
    Integrable (fun y => S.k y * S.k (y - u)) := by
  have hS : Integrable S.k := by
    simpa only [laplaceIntegrand, zero_mul, Complex.exp_zero, mul_one,
      RCLike.re_to_complex, Complex.ofReal_re] using (integrable_laplaceIntegrand S 0).re
  obtain ⟨B, _, hb⟩ := S.decay 0
  apply hS.mul_bdd (c := B) (S.cont.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  filter_upwards with y
  change ‖S.k (y - u)‖ ≤ B
  simpa only [Real.norm_eq_abs, abs_of_pos (S.pos (y - u)), zero_mul,
    neg_zero, Real.exp_zero, mul_one] using hb (y - u)

theorem tendsto_thetaGammaPolarCrossingTerm_atTop (S : ThetaSource) (u : ℝ) :
    Tendsto (fun x => thetaGammaPolarCrossingTerm S x u) atTop (𝓝 0) := by
  have hi := integrable_shift_link S u
  have h₁ := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi.integrableOn
    (tendsto_atTop_add_const_right atTop u tendsto_id)
  have h₂ := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi.integrableOn
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have he (x : ℝ) :
      thetaGammaPolarScalingKernel u * ((∫ y in (0 : ℝ)..x + u, S.k y * S.k (y - u)) -
        ∫ y in (0 : ℝ)..x, S.k y * S.k (y - u)) = thetaGammaPolarCrossingTerm S x u := by
    rw [intervalIntegral.integral_interval_sub_left hi.intervalIntegrable hi.intervalIntegrable]
    rfl
  simpa only [id_eq, he, sub_self, mul_zero] using (h₁.sub h₂).const_mul (thetaGammaPolarScalingKernel u)

/-- The full signed continuous current vanishes at the infinite boundary. -/
theorem tendsto_thetaGammaPolarCrossingCurrent_atTop (S : ThetaSource) :
    Tendsto (thetaGammaPolarCrossingCurrent S) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_thetaGammaPolarCrossingTerm_bound S
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (fun u => C ^ 2 * thetaGammaPolarCrossingMajorant u)
    (Eventually.of_forall fun x => (measurable_thetaGammaPolarCrossingTerm S x).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hb x u hu)
    (integrable_thetaGammaPolarCrossingMajorant.integrableOn.const_mul (C ^ 2))
    (Eventually.of_forall fun u => tendsto_thetaGammaPolarCrossingTerm_atTop S u)
  convert! h using 1
  simp only [integral_zero]

end RHTower.ThetaSourceWard
