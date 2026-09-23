import GaloisForLFunctions.Bottcher.Brolin.RieszFlux
import GaloisForLFunctions.HTGeometry.HardyDiskSpace

/-!
# Holomorphic mean square on a complex ball

Gutzmer's circle identity is integrated in polar coordinates to give the planar mean-square
inequality.  Haar translation then moves the estimate from the origin to an arbitrary center.
-/

open Complex Filter Metric Real Topology
open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Polar shell formula for a continuous real density on a centered complex ball. -/
theorem integral_ball_continuous_eq_shell (g : ℂ → ℝ) (hg : Continuous g) (R : ℝ) :
    (∫ z in Metric.ball (0 : ℂ) R, g z) =
      ∫ ρ in Set.Ioo 0 R, ρ • ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        g (circleMap 0 ρ θ) := by
  have hsymm : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
    have heq : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
        fun p => circleMap 0 p.1 p.2 := by
      funext p
      rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    rw [heq, show (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) from by
          funext p; simp [circleMap]]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  let q : ℝ × ℝ → ℝ := fun p => p.1 • g (Complex.polarCoord.symm p)
  have hcq : Continuous q := continuous_fst.smul (hg.comp hsymm)
  have hInt : IntegrableOn q (Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    apply (hcq.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := (0 : ℝ)) (b := R)).prod
        (isCompact_Icc (a := -Real.pi) (b := Real.pi)))).mono_set
    exact Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hfub : (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, q p) =
      ∫ ρ in Set.Ioo 0 R, ∫ θ in Set.Ioo (-Real.pi) Real.pi, q (ρ, θ) :=
    setIntegral_prod q hInt
  rw [Bottcher.integral_ball_eq_polar g R, hfub]
  refine setIntegral_congr_fun measurableSet_Ioo (fun ρ _ => ?_)
  show (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      ρ • g (Complex.polarCoord.symm (ρ, θ))) =
    ρ • ∫ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap 0 ρ θ)
  rw [integral_smul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  rw [show Complex.polarCoord.symm (ρ, θ) = circleMap 0 ρ θ from by
    rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]]

/-- Every holomorphic circle mean square dominates the value at its center. -/
theorem circle_integral_normSq_ge_center
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    2 * Real.pi * ‖F 0‖ ^ (2 : ℕ) ≤
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, ‖F (circleMap 0 ρ θ)‖ ^ (2 : ℕ) := by
  let R : ℝ := ρ + 1
  have hρR : ρ < R := by dsimp [R]; linarith
  have hgz := hasSum_circleAverage_normSq_diskCoeffOn hF.differentiableOn hρ hρR
  have hsum := hgz.summable
  have hfirst : ‖diskCoeff F 0‖ ^ (2 : ℕ) * ρ ^ (2 * 0) ≤
      ∑' k, ‖diskCoeff F k‖ ^ (2 : ℕ) * ρ ^ (2 * k) := by
    exact hsum.le_tsum 0 (by
      intro i hi
      rw [show 2 * i = i * 2 by omega, pow_mul]
      positivity)
  rw [hgz.tsum_eq] at hfirst
  have hcenter : diskCoeff F 0 = F 0 := by simp [diskCoeff]
  rw [hcenter] at hfirst
  norm_num at hfirst
  have hper : Function.Periodic
      (fun θ : ℝ => ‖F (circleMap 0 ρ θ)‖ ^ (2 : ℕ)) (2 * Real.pi) := by
    intro θ
    change ‖F (circleMap 0 ρ (θ + 2 * Real.pi))‖ ^ (2 : ℕ) =
      ‖F (circleMap 0 ρ θ)‖ ^ (2 : ℕ)
    rw [(periodic_circleMap 0 ρ θ)]
  rw [Bottcher.integral_Ioo_pi_eq_zero_two_pi hper]
  have htwopi : 0 < 2 * Real.pi := by positivity
  calc
    2 * Real.pi * ‖F 0‖ ^ (2 : ℕ) ≤
        2 * Real.pi * (Real.pi⁻¹ * (1 / 2) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖F (circleMap 0 ρ θ)‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hfirst htwopi.le
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖F (circleMap 0 ρ θ)‖ ^ (2 : ℕ) := by
      field_simp

/-- Planar holomorphic mean-square inequality at the origin. -/
theorem normSq_center_mul_area_le_integral_ball
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) {R : ℝ} (hR : 0 < R) :
    Real.pi * R ^ (2 : ℕ) * ‖F 0‖ ^ (2 : ℕ) ≤
      ∫ z in Metric.ball (0 : ℂ) R, ‖F z‖ ^ (2 : ℕ) := by
  rw [integral_ball_continuous_eq_shell (fun z => ‖F z‖ ^ (2 : ℕ))
    (hF.continuous.norm.pow 2) R]
  let lhs : ℝ → ℝ := fun ρ => ρ • (2 * Real.pi * ‖F 0‖ ^ (2 : ℕ))
  let rhs : ℝ → ℝ := fun ρ => ρ • ∫ θ in Set.Ioo (-Real.pi) Real.pi,
    ‖F (circleMap 0 ρ θ)‖ ^ (2 : ℕ)
  have hlhs : IntegrableOn lhs (Set.Ioo 0 R) := by
    apply ((continuous_id.smul continuous_const).continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := R))).mono_set Ioo_subset_Icc_self
  let q : ℝ × ℝ → ℝ := fun p => p.1 • ‖F (circleMap 0 p.1 p.2)‖ ^ (2 : ℕ)
  have hcq : Continuous q := by
    have hcircle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
      rw [show (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
          fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) from by
            funext p; simp [circleMap]]
      exact (Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
    exact continuous_fst.smul ((hF.continuous.comp hcircle).norm.pow 2)
  have hq : IntegrableOn q (Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    apply (hcq.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := (0 : ℝ)) (b := R)).prod
        (isCompact_Icc (a := -Real.pi) (b := Real.pi)))).mono_set
    exact Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hq' : Integrable q
      ((volume.restrict (Set.Ioo 0 R)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hq
  have hrhs : IntegrableOn rhs (Set.Ioo 0 R) := by
    have ho := hq'.integral_prod_left
    change Integrable rhs (volume.restrict (Set.Ioo 0 R))
    have heq : rhs = fun ρ =>
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, q (ρ, θ) := by
      funext ρ
      simp only [rhs, q]
      rw [integral_smul]
    rw [heq]
    exact ho
  have hmono : (∫ ρ in Set.Ioo 0 R, lhs ρ) ≤
      ∫ ρ in Set.Ioo 0 R, rhs ρ := by
    change Integrable lhs (volume.restrict (Set.Ioo 0 R)) at hlhs
    change Integrable rhs (volume.restrict (Set.Ioo 0 R)) at hrhs
    apply MeasureTheory.integral_mono_ae hlhs hrhs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    exact smul_le_smul_of_nonneg_left
      (circle_integral_normSq_ge_center F hF hρ.1.le) hρ.1.le
  have hlhs_eval : (∫ ρ in Set.Ioo 0 R, lhs ρ) =
      Real.pi * R ^ (2 : ℕ) * ‖F 0‖ ^ (2 : ℕ) := by
    rw [show (∫ ρ in Set.Ioo 0 R, lhs ρ) = ∫ ρ in (0 : ℝ)..R, lhs ρ by
      rw [intervalIntegral.integral_of_le hR.le]
      exact setIntegral_congr_set Ioo_ae_eq_Ioc]
    simp only [lhs, smul_eq_mul]
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [← hlhs_eval]
  exact hmono

/-- Planar holomorphic mean-square inequality at an arbitrary center. -/
theorem normSq_value_mul_area_le_integral_ball
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Real.pi * R ^ (2 : ℕ) * ‖F c‖ ^ (2 : ℕ) ≤
      ∫ z in Metric.ball c R, ‖F z‖ ^ (2 : ℕ) := by
  let Fc : ℂ → ℂ := fun z => F (z + c)
  have hFc : Differentiable ℂ Fc := by
    dsimp [Fc]
    fun_prop
  have hmean := normSq_center_mul_area_le_integral_ball Fc hFc hR
  have hshift :
      (∫ z in Metric.ball (0 : ℂ) R, ‖Fc z‖ ^ (2 : ℕ)) =
        ∫ z in Metric.ball c R, ‖F z‖ ^ (2 : ℕ) := by
    have hball0 : MeasurableSet (Metric.ball (0 : ℂ) R) := measurableSet_ball
    have hballc : MeasurableSet (Metric.ball c R) := measurableSet_ball
    rw [← integral_indicator hball0, ← integral_indicator hballc]
    calc
      (∫ z : ℂ, (Metric.ball (0 : ℂ) R).indicator (fun z => ‖Fc z‖ ^ (2 : ℕ)) z) =
          ∫ z : ℂ, (Metric.ball c R).indicator (fun z => ‖F z‖ ^ (2 : ℕ)) (z + c) := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ Metric.ball (0 : ℂ) R
        · have hzc : z + c ∈ Metric.ball c R := by
            rw [Metric.mem_ball, dist_eq_norm]
            simpa [add_sub_cancel_right] using hz
          rw [Set.indicator_of_mem hz, Set.indicator_of_mem hzc]
        · have hzc : z + c ∉ Metric.ball c R := by
            intro h
            apply hz
            rw [Metric.mem_ball, dist_eq_norm] at h ⊢
            simpa [add_sub_cancel_right] using h
          rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hzc]
      _ = ∫ z : ℂ, (Metric.ball c R).indicator (fun z => ‖F z‖ ^ (2 : ℕ)) z :=
        MeasureTheory.integral_add_right_eq_self _ c
  simpa [Fc, hshift] using hmean

end GaloisForLFunctions.HTGeometry
