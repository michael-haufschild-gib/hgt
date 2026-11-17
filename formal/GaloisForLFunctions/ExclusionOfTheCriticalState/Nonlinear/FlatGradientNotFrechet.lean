import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralDifferential
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexRigidity

/-!
# The flat L² gradient is not Fréchet differentiable at zero

Shrinking interval indicators retain unit amplitude while their L² norm
tends to zero. On each fixed indicator ray the flat gradient has zero
derivative at the origin, but on the unit-amplitude indicators its norm
is a fixed positive multiple of the input norm. Thus scalar smoothness
does not improve the global C¹ energy to a differentiable L² gradient.
-/

open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

/-- A unit-amplitude spike with support length `t²`. -/
def intervalSpike (t : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (s := Ioc 0 (t ^ 2)) measurableSet_Ioc measure_Ioc_lt_top.ne 1

private theorem intervalSpike_coe (t : ℝ) :
    (intervalSpike t : ℝ → ℝ) =ᵐ[volume] (Ioc 0 (t ^ 2)).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

/-- Concentration makes the Hilbert norm arbitrarily small without changing amplitude. -/
theorem intervalSpike_norm (t : ℝ) : ‖intervalSpike t‖ = |t| := by
  rw [intervalSpike, norm_indicatorConstLp (by norm_num) (by norm_num)]
  rw [Real.volume_real_Ioc, sub_zero, max_eq_left (sq_nonneg t)]
  norm_num only [norm_one, ENNReal.toReal_ofNat, one_mul]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

/-- Every spike ray has an exact scalar functional calculus. -/
theorem gradientLp_intervalSpike (t s : ℝ) :
    gradientLp (s • intervalSpike t) = gradient s • intervalSpike t := by
  apply Lp.ext
  filter_upwards [gradient_contraction.coeFn_compLp gradient_zero (s • intervalSpike t),
    Lp.coeFn_smul s (intervalSpike t), Lp.coeFn_smul (gradient s) (intervalSpike t),
    intervalSpike_coe t] with x hcomp hs hg hv
  change ((gradient_contraction.compLp gradient_zero (s • intervalSpike t)) x) = _
  rw [hcomp]
  change gradient ((s • intervalSpike t) x) = (gradient s • intervalSpike t) x
  rw [hs, hg]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hv]
  by_cases hx : x ∈ Ioc 0 (t ^ 2)
  · simp only [Set.indicator_of_mem hx, mul_one]
  · simp only [Set.indicator_of_notMem hx, mul_zero, gradient_zero]

private theorem gradientLp_zero : gradientLp (0 : Lp ℝ 2 (volume : Measure ℝ)) = 0 :=
  gradient_contraction.compLp_zero gradient_zero

private theorem derivative_annihilates_spike
    (L : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ))
    (hL : HasFDerivAt gradientLp L 0) (t : ℝ) : L (intervalSpike t) = 0 := by
  have hline : HasDerivAt (fun s : ℝ => s • intervalSpike t) (intervalSpike t) 0 := by
    have hd := (ContinuousLinearMap.toSpanSingleton ℝ (intervalSpike t)).hasFDerivAt.hasDerivAt
      (x := (0 : ℝ))
    have he : (ContinuousLinearMap.toSpanSingleton ℝ (intervalSpike t) :
        ℝ → Lp ℝ 2 (volume : Measure ℝ)) = (fun s => s • intervalSpike t) := by
      funext s
      exact ContinuousLinearMap.toSpanSingleton_apply ℝ (intervalSpike t) s
    rw [he] at hd
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hd
  have hbase : HasFDerivAt gradientLp L ((fun s : ℝ => s • intervalSpike t) 0) := by
    simpa only [zero_smul] using hL
  have hcomp := hbase.comp_hasDerivAt 0 hline
  have he : gradientLp ∘ (fun s : ℝ => s • intervalSpike t) =
      fun s => gradient s • intervalSpike t := by
    funext s
    exact gradientLp_intervalSpike t s
  rw [he] at hcomp
  have hflat : HasDerivAt (fun s => gradient s • intervalSpike t) 0 0 := by
    simpa only [expNegInvGlue.zero, zero_smul] using
      (gradient_hasDerivAt 0).smul_const (intervalSpike t)
  exact hcomp.unique hflat

/-- The globally Lipschitz L² gradient fails to be Fréchet differentiable even at zero. -/
theorem gradientLp_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ (gradientLp : Lp ℝ 2 (volume : Measure ℝ) →
      Lp ℝ 2 (volume : Measure ℝ)) 0 := by
  intro h
  let L := fderiv ℝ (gradientLp : Lp ℝ 2 (volume : Measure ℝ) →
    Lp ℝ 2 (volume : Measure ℝ)) 0
  have hL : HasFDerivAt gradientLp L 0 := h.hasFDerivAt
  have hg : 0 < gradient 1 := by
    have hn : gradient 1 ≠ 0 := by
      intro he
      have hz := (gradient_zero_iff 1).mp he
      norm_num at hz
    exact lt_of_le_of_ne (gradient_nonneg 1) (Ne.symm hn)
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.mp hL
  have hb := Asymptotics.isLittleO_iff.mp ho (show 0 < gradient 1 / 2 by positivity)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hb
  have hnorm : ‖intervalSpike (δ / 2)‖ = δ / 2 := by
    rw [intervalSpike_norm, abs_of_pos (half_pos hδ)]
  have hs := hball (y := intervalSpike (δ / 2)) (by
    rw [dist_zero_right, hnorm]
    linarith only [hδ])
  rw [zero_add, gradientLp_zero, sub_zero, derivative_annihilates_spike L hL,
    sub_zero] at hs
  have he : gradientLp (intervalSpike (δ / 2)) = gradient 1 • intervalSpike (δ / 2) := by
    simpa only [one_smul] using gradientLp_intervalSpike (δ / 2) 1
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hg, hnorm] at hs
  nlinarith only [hs, mul_pos hg hδ]

/-- Concentration prevents second Fréchet smoothness of the integral energy. -/
theorem integralEnergy_not_contDiffAt_two :
    ¬ ContDiffAt ℝ 2 (integralEnergy : Lp ℝ 2 (volume : Measure ℝ) → ℝ) 0 := by
  intro h
  have hd : DifferentiableAt ℝ
      (fderiv ℝ (integralEnergy : Lp ℝ 2 (volume : Measure ℝ) → ℝ)) 0 :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let R := InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure ℝ))
  have he : (fun f : Lp ℝ 2 (volume : Measure ℝ) => R.symm (fderiv ℝ integralEnergy f)) =
      gradientLp := by
    funext f
    rw [(integralEnergy_hasFDerivAt f).fderiv]
    have hr : innerSL ℝ (gradientLp f) = R (gradientLp f) := by
      ext v
      rw [InnerProductSpace.toDual_apply_apply]
      rfl
    rw [hr, R.symm_apply_apply]
  apply gradientLp_not_differentiableAt_zero
  rw [← he]
  exact R.symm.differentiableAt.comp 0 hd

/-- The integral energy is C¹ with a contracting gradient, but that gradient has no derivative at zero. -/
theorem integralEnergy_sharp_first_order_regularity :
    ContDiff ℝ 1 (integralEnergy : Lp ℝ 2 (volume : Measure ℝ) → ℝ) ∧
      LipschitzWith 1 (gradientLp : Lp ℝ 2 (volume : Measure ℝ) → Lp ℝ 2 (volume : Measure ℝ)) ∧
      ¬ DifferentiableAt ℝ (gradientLp : Lp ℝ 2 (volume : Measure ℝ) →
        Lp ℝ 2 (volume : Measure ℝ)) 0 :=
  ⟨integralEnergy_contDiff_one, gradientLp_contraction, gradientLp_not_differentiableAt_zero⟩

#print axioms intervalSpike_norm
#print axioms gradientLp_intervalSpike
#print axioms gradientLp_not_differentiableAt_zero
#print axioms integralEnergy_not_contDiffAt_two
#print axioms integralEnergy_sharp_first_order_regularity
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
