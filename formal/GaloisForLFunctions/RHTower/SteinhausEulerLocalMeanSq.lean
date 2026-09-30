import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq
import GaloisForLFunctions.RHTower.SteinhausEulerSpatialPartition
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Local planar mean square for finite Steinhaus Euler products

BAG C20.8. Localize the polar mean-square argument through a continuous Tietze
extension, prove the literal Euler product holomorphic on the positive half-plane,
and specialize to the critical-line discs used by the spatial moment estimate.
-/

open Complex Filter Metric Real Topology
open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower
open SteinhausModel
open GaloisForLFunctions.RHTower

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

private theorem local_normSq_center_mul_area_le_integral_ball
    (F : ℂ → ℂ) (hcont : Continuous F) {R : ℝ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R)) (hR : 0 < R) :
    Real.pi * R ^ (2 : ℕ) * ‖F 0‖ ^ (2 : ℕ) ≤
      ∫ z in Metric.ball (0 : ℂ) R, ‖F z‖ ^ (2 : ℕ) := by
  rw [integral_ball_continuous_eq_shell (fun z => ‖F z‖ ^ (2 : ℕ))
    (hcont.norm.pow 2) R]
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
    exact continuous_fst.smul ((hcont.comp hcircle).norm.pow 2)
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

/-- The planar mean-square inequality needs holomorphy only inside the disc and continuity
on its boundary. A continuous Tietze extension supplies the global polar integrand. -/
theorem norm_sq_value_mul_area_le_integral_ball_local (F : ℂ → ℂ) (c : ℂ) {R : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F (Metric.ball c R))
    (hcont : ContinuousOn F (Metric.closedBall c R)) :
    Real.pi * R ^ 2 * ‖F c‖ ^ 2 ≤ ∫ z in Metric.ball c R, ‖F z‖ ^ 2 := by
  let f : C(Metric.closedBall c R, ℂ) := ⟨fun z => F z, hcont.restrict⟩
  obtain ⟨G, hG⟩ := f.exists_restrict_eq isClosed_closedBall
  have heq (z : ℂ) (hz : z ∈ Metric.closedBall c R) : G z = F z := by
    exact congrArg (fun H : C(Metric.closedBall c R, ℂ) => H ⟨z, hz⟩) hG
  have hDG : DifferentiableOn ℂ G (Metric.ball c R) :=
    hF.congr fun z hz => heq z (Metric.ball_subset_closedBall hz)
  let Gc : ℂ → ℂ := fun z => G (z + c)
  have hGc : Continuous Gc := G.continuous.comp (continuous_id.add_const c)
  have hDGc : DifferentiableOn ℂ Gc (Metric.ball 0 R) := by
    apply hDG.comp (differentiable_id.add_const c).differentiableOn
    intro z hz
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_right, id_eq] using hz
  have hmean := local_normSq_center_mul_area_le_integral_ball Gc hGc hDGc hR
  have hshift : (∫ z in Metric.ball (0 : ℂ) R, ‖Gc z‖ ^ 2) =
      ∫ z in Metric.ball c R, ‖G z‖ ^ 2 := by
    have hball0 : MeasurableSet (Metric.ball (0 : ℂ) R) := measurableSet_ball
    have hballc : MeasurableSet (Metric.ball c R) := measurableSet_ball
    rw [← integral_indicator hball0, ← integral_indicator hballc]
    calc
      (∫ z : ℂ, (Metric.ball (0 : ℂ) R).indicator (fun z => ‖Gc z‖ ^ 2) z) =
          ∫ z : ℂ, (Metric.ball c R).indicator (fun z => ‖G z‖ ^ 2) (z + c) := by
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
      _ = ∫ z : ℂ, (Metric.ball c R).indicator (fun z => ‖G z‖ ^ 2) z :=
        MeasureTheory.integral_add_right_eq_self _ c
  rw [hshift] at hmean
  have hInt : (∫ z in Metric.ball c R, ‖G z‖ ^ 2) =
      ∫ z in Metric.ball c R, ‖F z‖ ^ 2 := by
    exact setIntegral_congr_fun measurableSet_ball fun z hz => by
      rw [heq z (Metric.ball_subset_closedBall hz)]
  rw [hInt] at hmean
  have hcenter : G c = F c := heq c (Metric.mem_closedBall_self hR.le)
  simpa only [Gc, zero_add, hcenter] using hmean

private theorem steinhausEulerDenominator_ne_zero {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) (ω : Omega) : 1 - steinhausEulerPrimeTerm s ω p ≠ 0 := by
  have hn : ‖steinhausEulerPrimeTerm s ω p‖ < 1 := by
    rw [steinhausEulerPrimeTerm, norm_mul, norm_X, one_mul,
      Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact (prime_rpow_neg_le_rho hs hp).trans_lt (randomEulerRho_lt_one hs)
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hn
  exact lt_irrefl _ hn

/-- Every literal finite Steinhaus Euler product is holomorphic on the positive half-plane. -/
theorem differentiableOn_steinhausFiniteEulerProduct (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ω : Omega) :
    DifferentiableOn ℂ (fun s => steinhausFiniteEulerProduct P s ω) {s | 0 < s.re} := by
  unfold steinhausFiniteEulerProduct
  apply DifferentiableOn.fun_finsetProd
  intro p hp s hs
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hp0)
  have hden : DifferentiableAt ℂ (fun z : ℂ => 1 - X p ω * (p : ℂ) ^ (-z)) s :=
    (differentiableAt_const 1).sub ((differentiableAt_const (X p ω)).mul hpow)
  exact (hden.inv (steinhausEulerDenominator_ne_zero (hP p hp) hs ω)).differentiableWithinAt

/-- The actual finite Euler product satisfies local planar mean square on every disc
whose closure lies in the positive half-plane. -/
theorem norm_sq_steinhausFiniteEulerProduct_mul_area_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ω : Omega) (c : ℂ) {R : ℝ}
    (hR : 0 < R) (hRc : R < c.re) :
    Real.pi * R ^ 2 * ‖steinhausFiniteEulerProduct P c ω‖ ^ 2 ≤
      ∫ z in Metric.ball c R, ‖steinhausFiniteEulerProduct P z ω‖ ^ 2 := by
  have hsub : Metric.closedBall c R ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    have hn : ‖z - c‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hr := (neg_le_abs (z - c).re).trans (Complex.abs_re_le_norm (z - c))
    simp only [Complex.sub_re] at hr
    change 0 < z.re
    linarith
  have hF := differentiableOn_steinhausFiniteEulerProduct P hP ω
  exact norm_sq_value_mul_area_le_integral_ball_local _ c hR
    (hF.mono (Metric.ball_subset_closedBall.trans hsub)) (hF.continuousOn.mono hsub)

/-- Canonical critical-line discs use the radius already matched to the exact moment estimate. -/
theorem norm_sq_steinhausFiniteEulerProduct_spatial_ball {N : ℕ} (hN : 3 ≤ N)
    (ω : Omega) (t : ℝ) :
    Real.pi * steinhausEulerSpatialRadius N ^ 2 *
        ‖steinhausFiniteEulerProduct (Nat.primesBelow N) ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ ^ 2 ≤
      ∫ z in Metric.ball ((1 / 2 : ℂ) + (t : ℂ) * I) (steinhausEulerSpatialRadius N),
        ‖steinhausFiniteEulerProduct (Nat.primesBelow N) z ω‖ ^ 2 := by
  apply norm_sq_steinhausFiniteEulerProduct_mul_area_le _
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2) ω _ (steinhausEulerSpatialRadius_pos hN)
  have hr := steinhausEulerSpatialRadius_le hN
  norm_num
  linarith

end RHTower
