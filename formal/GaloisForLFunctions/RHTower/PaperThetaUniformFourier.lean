import GaloisForLFunctions.RHTower.PaperThetaFourierEquicontinuity
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Exact uniform Fourier recovery of the seam-corrected theta mode

The native L¹ derivative pays equicontinuity of the full symmetric source
sums. Compactness upgrades their proven pointwise recovery to uniform recovery,
with the original coefficients and the literal frequency window unchanged.
Continuity of uniform limits gives the converse native admission criterion.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL
open HedenmalmThetaSource HedenmalmQuantile

theorem sourcePartialSum_zero (N : ℕ) (t : ℝ) : sourcePartialSum 0 N t = -1 := by
  rw [sourcePartialSum_eq_derivative_convolution ⟨0, Or.inl rfl⟩ N t]
  have he : closedQuantileMode 0 = fun _ : ℝ => (-1 : ℂ) := funext closedQuantileMode_zero
  simp [he]

private theorem corrected_circle_on_closed_interval (z : ℂ) (t : Icc (0 : ℝ) 1) :
    seamCorrectedCircleMode z (Period.circle t.val) = closedQuantileMode z t.val := by
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · rw [seamCorrectedCircleMode_eq_closedQuantileMode,
      Period.coord_circle_eq ⟨t.property.1, ht⟩]
  · rw [ht, show Period.circle 1 = Period.circle 0 by
      simpa only [zero_add] using Period.periodic_circle 0]
    rw [seamCorrectedCircleMode_eq_closedQuantileMode,
      Period.coord_circle_eq (by norm_num [Period.unitInt]),
      (closedQuantileMode_endpoints z).1, (closedQuantileMode_endpoints z).2]

theorem closed_interval_recovery (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (t : Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => sourcePartialSum z.val N t.val) atTop
      (𝓝 (closedQuantileMode z.val t.val)) := by
  rcases z.property with hz | hz
  · simp only [hz, sourcePartialSum_zero, closedQuantileMode_zero]
    exact tendsto_const_nhds
  · simpa only [symmetricPartialSum_seamCorrectedCircleMode, ← sourcePartialSum_eq_all,
      corrected_circle_on_closed_interval] using
      circle_everywhere_recovery ⟨z.val, hz⟩ (Period.circle t.val)

/-- Full symmetric sums converge uniformly across the closed quantile interval, including its seam. -/
theorem closed_interval_uniform_recovery (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    TendstoUniformlyOn (fun N : ℕ => sourcePartialSum z.val N)
      (closedQuantileMode z.val) atTop (Icc (0 : ℝ) 1) := by
  have he : Equicontinuous (fun N : ℕ => fun t : Icc (0 : ℝ) 1 => sourcePartialSum z.val N t.val) :=
    (equicontinuous_restrict_iff _).mpr ((equicontinuous_sourcePartialSum z).equicontinuousOn _)
  have hp : Tendsto (fun N : ℕ => fun t : Icc (0 : ℝ) 1 => sourcePartialSum z.val N t.val)
      atTop (𝓝 (fun t : Icc (0 : ℝ) 1 => closedQuantileMode z.val t.val)) :=
    tendsto_pi_nhds.mpr (closed_interval_recovery z)
  have hu := UniformFun.tendsto_iff_tendstoUniformly.mp
    ((he.tendsto_uniformFun_iff_pi atTop _).mpr hp)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hu

/-- Uniform recovery on the actual circle retains every original flat-source Fourier coefficient. -/
theorem circle_uniform_recovery (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    TendstoUniformly (fun N : ℕ => symmetricPartialSum (seamCorrectedCircleMode z.val) N)
      (seamCorrectedCircleMode z.val) atTop := by
  have hc (x : Torus) : Period.coord x ∈ Icc (0 : ℝ) 1 := by
    have hx := (AddCircle.measurableEquivIco (2 * Real.pi) 0 x).property
    refine ⟨div_nonneg hx.1 Real.two_pi_pos.le, ?_⟩
    apply (div_le_one Real.two_pi_pos).mpr
    exact le_of_lt (by simpa only [zero_add] using hx.2)
  let c : Torus → Icc (0 : ℝ) 1 := fun x => ⟨Period.coord x, hc x⟩
  have hu := (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp
    (closed_interval_uniform_recovery z)).comp c
  have hcoord (x : Torus) : Period.circle (Period.coord x) = x := by
    unfold Period.circle Period.coord
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ Real.two_pi_pos.ne']
    exact AddCircle.coe_equivIco
  have hs (N : ℕ) (x : Torus) : sourcePartialSum z.val N (Period.coord x) =
      symmetricPartialSum (seamCorrectedCircleMode z.val) N x := by
    rw [sourcePartialSum_eq_all, hcoord, symmetricPartialSum_seamCorrectedCircleMode]
  dsimp only [Function.comp_def, c] at hu
  simpa only [hs, ← seamCorrectedCircleMode_eq_closedQuantileMode] using hu

/-- Uniform recovery has precisely the original divisor-or-zero selector. -/
theorem circle_uniform_recovery_iff (z : ℂ) :
    TendstoUniformly (fun N : ℕ => symmetricPartialSum (seamCorrectedCircleMode z) N)
      (seamCorrectedCircleMode z) atTop ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro h
    apply (continuous_seamCorrectedCircleMode_iff z).mp
    exact h.continuous (Eventually.of_forall
      (fun N => continuous_symmetricPartialSum (seamCorrectedCircleMode z) N)).frequently
  · intro hz
    exact circle_uniform_recovery ⟨z, hz⟩

/-- The original source-relative mode is recovered uniformly on the entire unbounded real line. -/
theorem relative_source_uniform_recovery (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    TendstoUniformly (fun N : ℕ => fun x : ℝ => sourcePartialSum z.val N (thetaSource.cdfFun x))
      (flatQuotient z.val) atTop := by
  let c : ℝ → Icc (0 : ℝ) 1 := fun x =>
    ⟨thetaSource.cdfFun x, (thetaSource.cdfFun_mem_Ioo x).1.le, (thetaSource.cdfFun_mem_Ioo x).2.le⟩
  have hu := (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp
    (closed_interval_uniform_recovery z)).comp c
  have he (x : ℝ) : closedQuantileMode z.val (thetaSource.cdfFun x) = flatQuotient z.val x := by
    rw [closedQuantileMode_interior z.val ⟨_, thetaSource.cdfFun_mem_Ioo x⟩,
      flatModePullback_eq_flatQuotient, thetaSource.quantile_cdfFun]
  dsimp only [Function.comp_def, c] at hu
  simpa only [he] using hu

theorem norm_sourcePartialSum_le_coefficient_sum (z : ℂ) (N : ℕ) (t : ℝ) :
    ‖sourcePartialSum z N t‖ ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖sourceCoeff z k‖ := by
  unfold sourcePartialSum
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [norm_mul, Period.phase_unimod, mul_one]

/-- Even on the unbounded original coordinate, uniform recovery selects exactly divisor-or-zero. -/
theorem relative_source_uniform_recovery_iff (z : ℂ) :
    TendstoUniformly (fun N : ℕ => fun x : ℝ => sourcePartialSum z N (thetaSource.cdfFun x))
      (flatQuotient z) atTop ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := ((Metric.tendstoUniformly_iff.mp h) 1 zero_lt_one).exists
    apply (bounded_flatQuotient_iff z).mp
    refine ⟨1 + ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖sourceCoeff z k‖, fun x => ?_⟩
    have hd := hN x
    rw [dist_eq_norm] at hd
    calc
      ‖flatQuotient z x‖ ≤
          ‖flatQuotient z x - sourcePartialSum z N (thetaSource.cdfFun x)‖ +
            ‖sourcePartialSum z N (thetaSource.cdfFun x)‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          (flatQuotient z x - sourcePartialSum z N (thetaSource.cdfFun x))
          (sourcePartialSum z N (thetaSource.cdfFun x))
      _ ≤ _ := add_le_add hd.le (norm_sourcePartialSum_le_coefficient_sum z N _)
  · intro hz
    exact relative_source_uniform_recovery ⟨z, hz⟩

end RHTower.PaperThetaEndpoint
