import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonModeJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSpatialODE
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceFrequencyContinuation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceJetHolomorphy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalHorizonBound
import GaloisForLFunctions.HTGeometry.SymmetricHorizonGrowth

/-!
# Uniform outer bound of the continued horizon mode

Off the real frequency axis the horizon mode solves the homogeneous tortoise equation
`U'' = (w² + z_t (1/4 + χ²)) U`, so the symmetric horizon growth estimate bounds it on every
half-line `[T, 0)` by a coefficient that depends continuously on the frequency.  Compactness of a
closed frequency ball then gives one constant for a whole neighbourhood, up to spatial infinity,
without any convergence statement for the Gauss series at the boundary of its disc.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

theorem radialMode_false (w chi : ℂ) : radialMode false w chi = horizon w chi := by
  simp [radialMode]

theorem radialModeFirst_false (w chi : ℂ) : radialModeFirst false w chi = horizonFirst w chi := by
  simp [radialModeFirst]

theorem radialModeSecond_false (w chi : ℂ) :
    radialModeSecond false w chi = horizonSecond w chi := by
  simp [radialModeSecond]

/-- Tortoise derivatives of the continued horizon mode at every nonreal frequency. -/
theorem tortoiseMode_hasDerivAt_continued (w chi : ℂ) (t : ℝ) (ht : t < 0) :
    HasDerivAt (tortoiseMode false w chi) (tortoiseModeFirst false w chi t) t ∧
      HasDerivAt (tortoiseModeFirst false w chi) (tortoiseModeSecond false w chi t) t := by
  have hd := horizon_derivatives_continued (w := w) (chi := chi) (horizonCoordinate_interior t ht)
  have hc := horizonCoordinate_hasDerivAt t
  have hF := hd.1.scomp t hc
  have hF1 := hd.2.scomp t hc
  simp only [tortoiseModeFirst, tortoiseModeSecond, radialModeFirst_false, radialModeSecond_false]
  constructor
  · simpa only [Function.comp_def, Complex.real_smul] using! hF
  · apply (((coordinateFirst_hasDerivAt t).ofReal_comp).mul hF1).congr_deriv
    dsimp only [Function.comp_apply]
    simp only [Complex.real_smul]
    ring

/-- The continued horizon mode satisfies the homogeneous tortoise equation. -/
theorem tortoiseMode_equation_continued (w chi : ℂ) (hw : w.im ≠ 0) (t : ℝ) (ht : t < 0) :
    tortoiseModeSecond false w chi t =
      (w ^ 2 + (horizonCoordinate t:ℂ) * (1 / 4 + chi ^ 2)) * tortoiseMode false w chi t := by
  have hz := horizonCoordinate_interior t ht
  have he := horizon_equation_continued (w := w) (chi := chi) hw hz
  dsimp only [D4BMPhysicalMaster.radialJet] at he
  rw [mul_pow, Complex.I_sq] at he
  have hz0 : (horizonCoordinate t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  field_simp [hz0] at he
  simp only [tortoiseMode, tortoiseModeSecond, radialMode_false, radialModeFirst_false,
    radialModeSecond_false, coordinateFirst, coordinateSecond]
  have hu : (radialUnit t:ℂ) ^ 2 = 1 - (horizonCoordinate t:ℂ) := by
    simp only [horizonCoordinate, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
    ring
  push_cast
  simp only [mul_pow, hu] at he ⊢
  linear_combination (1 / 8:ℂ) * he

/-- Symmetric horizon growth bound for the continued horizon mode. -/
theorem tortoiseMode_horizon_growth_bound (w chi : ℂ) (hw : w.im ≠ 0) (t : ℝ) (ht : t < 0) :
    ‖tortoiseMode false w chi t‖ ≤
      symmetricHorizonGrowthCoefficient w (tortoiseMode false w chi (-1))
        (tortoiseModeFirst false w chi (-1)) (4 * ‖(1 / 4:ℂ) + chi ^ 2‖) 0 *
        Real.exp (-|w.re| * t) := by
  have hw0 : w ≠ 0 := by intro he; apply hw; simp [he]
  have hd (r : ℝ) (hr : r < 0) := tortoiseMode_hasDerivAt_continued w chi r hr
  have hV (r : ℝ) (hr : r < 0) : HasDerivAt (tortoiseModeFirst false w chi)
      (w ^ 2 * tortoiseMode false w chi r +
        ((horizonCoordinate r:ℂ) * (1 / 4 + chi ^ 2)) * tortoiseMode false w chi r - 0) r := by
    have h := (hd r hr).2
    rw [tortoiseMode_equation_continued w chi hw r hr] at h
    convert h using 1
    ring
  have hp (r : ℝ) (hr : r < 0) :
      ‖(horizonCoordinate r:ℂ) * ((1 / 4:ℂ) + chi ^ 2)‖ ≤
        (4 * ‖(1 / 4:ℂ) + chi ^ 2‖) * Real.exp (2 * r) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (horizonCoordinate_norm_le_exp r hr)
      (norm_nonneg _)).trans_eq (by ring)
  have hf (r : ℝ) (_ : r < 0) : ‖(0:ℂ)‖ ≤ (0:ℝ) * Real.exp ((w.re + 2) * r) := by simp
  exact forcedSecondOrder_horizon_bound_symmetric w hw0 (tortoiseMode false w chi)
    (tortoiseModeFirst false w chi) (fun r => (horizonCoordinate r:ℂ) * (1 / 4 + chi ^ 2))
    (fun _ => 0) _ 0 (by positivity) le_rfl (fun r hr => (hd r hr).1) hV hp hf t ht

/-- One constant bounds the continued horizon mode on a frequency neighbourhood and a whole
half-line `[T, 0)`, up to spatial infinity. -/
theorem tortoiseMode_outer_uniform_bound (w chi : ℂ) (hw : w.im ≠ 0) (T : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ u ∈ ball w R, ∀ t ∈ Ico T (0:ℝ),
      ‖tortoiseMode false u chi t‖ ≤ C := by
  have hi : ∀ᶠ u : ℂ in 𝓝 w, u.im ≠ 0 := Complex.continuous_im.continuousAt.eventually_ne hw
  obtain ⟨r, hr0, hrall⟩ := Metric.eventually_nhds_iff.mp hi
  let R := min (r / 2) 1
  have hR : 0 < R := lt_min (half_pos hr0) one_pos
  have hR1 : R ≤ 1 := min_le_right _ _
  have hstrip : ∀ u ∈ closedBall w R, u.im ≠ 0 := fun u hu =>
    hrall (lt_of_le_of_lt (mem_closedBall.mp hu)
      (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr0)))
  let A : ℝ := 4 * ‖(1 / 4:ℂ) + chi ^ 2‖
  let D (u : ℂ) : ℝ := symmetricHorizonGrowthCoefficient u (tortoiseMode false u chi (-1))
    (tortoiseModeFirst false u chi (-1)) A 0
  have hz1 : horizonCoordinate (-1) ∈ Ioo 0 1 := horizonCoordinate_interior (-1) (by norm_num)
  have hD : ContinuousOn D (closedBall w R) := by
    intro u hu
    have hui := hstrip u hu
    have hu0 : u ≠ 0 := by intro he; apply hui; simp [he]
    have hU : ContinuousAt (fun v => tortoiseMode false v chi (-1)) u := by
      have := (horizon_frequency_analyticAt u chi hui hz1).continuousAt
      simpa only [tortoiseMode, radialMode_false] using this
    have hV : ContinuousAt (fun v => tortoiseModeFirst false v chi (-1)) u := by
      have := ((horizonFirst_frequency_analyticAt u chi hui hz1).continuousAt).const_mul
        ((coordinateFirst (-1):ℝ):ℂ)
      simpa only [tortoiseModeFirst, radialModeFirst_false] using this
    exact ((symmetricHorizonGrowthCoefficient_continuousAt u _ _ A 0 hu0).comp_of_eq
      (continuousAt_id.prodMk (hU.prodMk (hV.prodMk
        (continuousAt_const.prodMk continuousAt_const)))) rfl).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall w R).exists_bound_of_continuousOn hD
  refine ⟨R, max C 0 * Real.exp ((‖w‖ + 1) * |T|), hR, by positivity, ?_⟩
  intro u hu t ht
  have hucb : u ∈ closedBall w R := ball_subset_closedBall hu
  have hui := hstrip u hucb
  have hb := tortoiseMode_horizon_growth_bound u chi hui t ht.2
  have hun : |u.re| ≤ ‖w‖ + 1 := by
    have hd : ‖u - w‖ < 1 := by
      have := mem_ball.mp hu
      rw [dist_eq_norm] at this
      exact this.trans_le hR1
    have := norm_sub_norm_le u w
    exact (Complex.abs_re_le_norm u).trans (by linarith)
  have htT : -t ≤ |T| := (neg_le_neg ht.1).trans (neg_le_abs T)
  refine hb.trans ?_
  have hDu : D u ≤ max C 0 := by
    have := hC u hucb
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  refine mul_le_mul hDu (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (le_max_right _ _)
  calc -|u.re| * t = |u.re| * (-t) := by ring
    _ ≤ (‖w‖ + 1) * |T| := mul_le_mul hun htT (by linarith [ht.2]) (by positivity)

end
end RHTower.D4BMJointSource
