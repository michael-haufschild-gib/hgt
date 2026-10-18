import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailReadout
import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq

/-! Local disk sampling for the literal factorial tail readout.  The helpers
localize the corpus Gutzmer argument; the public theorem discharges every
analytic hypothesis on the actual zeta divisor. -/

open Complex Filter Metric Real Topology MeasureTheory Set
open _root_.Zeta23 GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

/-- Every holomorphic circle mean square dominates the value at its center. -/
private theorem local_circle_integral_normSq_ge_center
    (F : ℂ → ℂ) {R : ℝ} (hF : DifferentiableOn ℂ F (Metric.ball 0 R))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    2 * Real.pi * ‖F 0‖ ^ (2 : ℕ) ≤
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, ‖F (circleMap 0 ρ θ)‖ ^ (2 : ℕ) := by
  have hgz := hasSum_circleAverage_normSq_diskCoeffOn hF hρ hρR
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
private theorem local_normSq_center_mul_area_le_integral_ball
    (F : ℂ → ℂ) (hcF : Continuous F) {R : ℝ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R)) (hR : 0 < R) :
    Real.pi * R ^ (2 : ℕ) * ‖F 0‖ ^ (2 : ℕ) ≤
      ∫ z in Metric.ball (0 : ℂ) R, ‖F z‖ ^ (2 : ℕ) := by
  rw [integral_ball_continuous_eq_shell (fun z => ‖F z‖ ^ (2 : ℕ))
    (hcF.norm.pow 2) R]
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
    exact continuous_fst.smul ((hcF.comp hcircle).norm.pow 2)
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
      (local_circle_integral_normSq_ge_center F hF hρ.1.le hρ.2) hρ.1.le
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
private theorem local_normSq_value_mul_area_le_integral_ball
    (F : ℂ → ℂ) (hcF : Continuous F) (c : ℂ) {R : ℝ}
    (hF : DifferentiableOn ℂ F (Metric.ball c R)) (hR : 0 < R) :
    Real.pi * R ^ (2 : ℕ) * ‖F c‖ ^ (2 : ℕ) ≤
      ∫ z in Metric.ball c R, ‖F z‖ ^ (2 : ℕ) := by
  let Fc : ℂ → ℂ := fun z => F (z + c)
  have hFc : DifferentiableOn ℂ Fc (Metric.ball 0 R) := by
    apply hF.comp (show DifferentiableOn ℂ (fun z : ℂ => z+c) (Metric.ball 0 R) from
      (show Differentiable ℂ (fun z : ℂ => z+c) by fun_prop).differentiableOn)
    intro z hz
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  have hcFc : Continuous Fc := hcF.comp (continuous_id.add continuous_const)
  have hmean := local_normSq_center_mul_area_le_integral_ball Fc hcFc hFc hR
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

/-- A continuous extension used only to apply the polar-coordinate integral formula. -/
private def readoutClamp (s : ℂ) : ℂ :=
  (max s.re (-1/2) : ℝ) + (s.im : ℂ)*Complex.I

private theorem readoutClamp_continuous : Continuous readoutClamp := by
  unfold readoutClamp
  fun_prop

private theorem readoutClamp_mem (s : ℂ) : -1 < (readoutClamp s).re := by
  have hm := le_max_right s.re (-1/2 : ℝ)
  simp only [readoutClamp, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  linarith

private theorem readoutClamp_eq {s : ℂ} (hs : -1/2 ≤ s.re) : readoutClamp s = s := by
  rw [readoutClamp, max_eq_left hs]
  exact Complex.re_add_im s

/-- Centers in the ordinary zero strip, without a zero-location hypothesis. -/
abbrev FactorialSamplingCenter := {s : ℂ // 0 ≤ s.re ∧ s.re ≤ 1}

/-- Radius `1/4` stays inside the actual readout's admitted half-plane. -/
theorem factorialTailReadout_disk_mean_square (n : ℕ) (ρ : FactorialSamplingCenter) :
    Real.pi / 16 * ‖factorialTailReadout n (ρ : ℂ)‖^2 ≤
      ∫ s in Metric.ball (ρ : ℂ) (1/4), ‖factorialTailReadout n s‖^2 := by
  have hρ := ρ.2
  have hball (s : ℂ) (hs : s ∈ Metric.ball (ρ : ℂ) (1/4)) : -1/4 < s.re := by
    have hd : ‖s-(ρ : ℂ)‖ < (1/4 : ℝ) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hs
    have hr := (abs_le.mp (Complex.abs_re_le_norm (s-(ρ : ℂ)))).1
    simp only [Complex.sub_re] at hr
    linarith
  let F : ℂ → ℂ := factorialTailReadout n ∘ readoutClamp
  have hcF : Continuous F := (factorialTailReadout_analyticOnNhd n).continuousOn.comp_continuous
    readoutClamp_continuous readoutClamp_mem
  have he (s : ℂ) (hs : s ∈ Metric.ball (ρ : ℂ) (1/4)) :
      F s = factorialTailReadout n s := by
    dsimp [F]
    rw [readoutClamp_eq (by linarith only [hball s hs])]
  have hdF : DifferentiableOn ℂ F (Metric.ball (ρ : ℂ) (1/4)) := by
    have hd := (factorialTailReadout_analyticOnNhd n).differentiableOn.mono
      (show Metric.ball (ρ : ℂ) (1/4) ⊆ {s : ℂ | -1 < s.re} from
        fun s hs => by have := hball s hs; change -1 < s.re; linarith)
    exact hd.congr he
  have hm := local_normSq_value_mul_area_le_integral_ball F hcF (ρ : ℂ) hdF (by norm_num)
  have hcenter : (ρ : ℂ) ∈ Metric.ball (ρ : ℂ) (1/4) := Metric.mem_ball_self (by norm_num)
  rw [he _ hcenter] at hm
  have hint : (∫ s in Metric.ball (ρ : ℂ) (1/4), ‖F s‖^2) =
      ∫ s in Metric.ball (ρ : ℂ) (1/4), ‖factorialTailReadout n s‖^2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro s hs
    change ‖F s‖^2 = ‖factorialTailReadout n s‖^2
    rw [he s hs]
  rw [hint] at hm
  norm_num at hm ⊢
  convert hm using 1
  ring

/-- The local mean-square estimate applies at every actual nontrivial zero. -/
theorem factorialTailReadout_zero_disk_mean_square (n : ℕ) (ρ : zetaZeroConfig.carrier) :
    Real.pi / 16 * ‖factorialTailReadout n (ρ : ℂ)‖^2 ≤
      ∫ s in Metric.ball (ρ : ℂ) (1/4), ‖factorialTailReadout n s‖^2 :=
  factorialTailReadout_disk_mean_square n ⟨ρ, zetaZeroConfig.strip (ρ : ℂ) ρ.2⟩

end
end GaloisForLFunctions.ArithmeticPositivityTheory
