import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceCurvatureCalculus
import GaloisForLFunctions.HTGeometry.PlanarLogNormIntegrability
import GaloisForLFunctions.RHTower.RiemannTower
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Regularized xi potentials and their positive source density

A positive regulator removes every logarithmic singularity. Its curvature is
pointwise nonnegative and uses only xi and its derivative. Local logarithmic
integrability supplies domination as the regulator tends to zero, including
zeros of arbitrary multiplicity.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower HTGeometry

/-- A fixed positive regulator sequence tending to zero. -/
def sourceRegulator (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem sourceRegulator_pos (n : ℕ) : 0 < sourceRegulator n := by
  unfold sourceRegulator
  positivity

theorem sourceRegulator_le_one (n : ℕ) : sourceRegulator n ≤ 1 := by
  unfold sourceRegulator
  exact (div_le_one (by positivity)).2 (by linarith only [Nat.cast_nonneg (α := ℝ) n])

theorem tendsto_sourceRegulator : Tendsto sourceRegulator atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- A smooth potential defined from the arithmetic entire function. -/
def xiLogPotential (ε : ℝ) (z : ℂ) : ℝ := radialLogPotential ε (xi z)

/-- Positive arithmetic curvature density, before any divisor evaluation. -/
def xiCurvatureDensity (ε : ℝ) (z : ℂ) : ℝ :=
  ε * Complex.normSq (deriv xi z) / (Complex.normSq (xi z) + ε) ^ 2

theorem xiCurvatureDensity_nonneg {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    0 ≤ xiCurvatureDensity ε z :=
  div_nonneg (mul_nonneg hε (Complex.normSq_nonneg _)) (sq_nonneg _)

theorem contDiff_xiLogPotential {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (xiLogPotential ε) :=
  (contDiff_radialLogPotential hε).comp
    (xi_differentiable.contDiff.restrict_scalars ℝ)

/-- The literal planar Laplacian is twice the positive arithmetic density. -/
theorem laplacian_xiLogPotential {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Δ (xiLogPotential ε) z = 2 * xiCurvatureDensity ε z := by
  rw [show xiLogPotential ε = radialLogPotential ε ∘ xi from rfl,
    laplacian_real_holomorphic_comp _ _ (contDiff_radialLogPotential hε)
      xi_differentiable, laplacian_radialLogPotential hε]
  unfold xiCurvatureDensity
  ring

/-- The only possible singularities of the limit potential are locally integrable. -/
theorem integrableOn_xi_log_norm (c : ℂ) (R : ℝ) :
    IntegrableOn (fun z => Real.log ‖xi z‖) (closedBall c |R|) := by
  apply meromorphic_integrableOn_log_norm
    (xi_analyticOnNhd_univ.mono (Set.subset_univ _) |>.meromorphicOn)
  intro z
  rw [(xi_analyticOnNhd_univ z (Set.mem_univ _)).meromorphicOrderAt_eq,
    ← ENat.coe_toNat (xi_order_ne_top z)]
  exact WithTop.coe_ne_top

/-- The discrete xi zero set has zero planar measure. -/
theorem xi_ne_zero_ae : ∀ᵐ z : ℂ, xi z ≠ 0 := by
  have h : ∀ᵐ z : ℂ ∂(volume.restrict (Set.univ : Set ℂ)), xi z ≠ 0 :=
    ae_restrict_le_codiscreteWithin MeasurableSet.univ xi_ne_zero_codiscrete
  rwa [Measure.restrict_univ] at h

private theorem half_log_bound {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |(1 / 2 : ℝ) * Real.log (r ^ 2 + ε)| ≤ r + |Real.log r| := by
  have hq : 0 < r ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg r) hε
  have hlo := Real.log_le_log (sq_pos_of_pos hr) (le_add_of_nonneg_right hε.le)
  rw [Real.log_pow] at hlo
  have hqle : r ^ 2 + ε ≤ (r + 1) ^ 2 := by nlinarith only [hr, hε1]
  have hhi := Real.log_le_log hq hqle
  rw [Real.log_pow] at hhi
  norm_num only [Nat.cast_ofNat] at hlo hhi
  have hup := Real.log_le_sub_one_of_pos (by linarith only [hr] : 0 < r + 1)
  have ha := neg_abs_le (Real.log r)
  have hb := abs_nonneg (Real.log r)
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo, hhi, hup, ha, hb, hr]

/-- A regulator-independent local majorant; the zero set is handled separately in measure. -/
theorem xiLogPotential_bound (n : ℕ) {z : ℂ} (hz : xi z ≠ 0) :
    ‖xiLogPotential (sourceRegulator n) z‖ ≤ ‖xi z‖ + |Real.log ‖xi z‖| := by
  have hs : (xi z).re ^ 2 + (xi z).im ^ 2 = ‖xi z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [xiLogPotential, radialLogPotential, hs, Real.norm_eq_abs]
  exact half_log_bound (norm_pos_iff.mpr hz) (sourceRegulator_pos n)
    (sourceRegulator_le_one n)

/-- Off the discrete divisor, the smooth potential tends to the exact logarithmic norm. -/
theorem tendsto_xiLogPotential {z : ℂ} (hz : xi z ≠ 0) :
    Tendsto (fun n => xiLogPotential (sourceRegulator n) z) atTop
      (𝓝 (Real.log ‖xi z‖)) := by
  have hs : (xi z).re ^ 2 + (xi z).im ^ 2 = ‖xi z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have harg : Tendsto (fun n => ‖xi z‖ ^ 2 + sourceRegulator n) atTop
      (𝓝 (‖xi z‖ ^ 2)) := by
    simpa only [add_zero] using tendsto_const_nhds.add tendsto_sourceRegulator
  have hlog := (Real.continuousAt_log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))).tendsto.comp harg
  have he : (1 / 2 : ℝ) * Real.log (‖xi z‖ ^ 2) = Real.log ‖xi z‖ := by
    rw [Real.log_pow]
    ring
  simpa only [xiLogPotential, radialLogPotential, hs, he, Function.comp_apply] using
    hlog.const_mul (1 / 2 : ℝ)

/-- Local convergence against every continuous weight, including discs containing multiple zeros. -/
theorem tendsto_integral_xiLogPotential_on_disc (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (c : ℂ) (R : ℝ) :
    Tendsto (fun n => ∫ z in closedBall c |R|,
      xiLogPotential (sourceRegulator n) z * ψ z) atTop
        (𝓝 (∫ z in closedBall c |R|, Real.log ‖xi z‖ * ψ z)) := by
  have hi := ((xi_differentiable.continuous.norm.continuousOn.integrableOn_compact
    (isCompact_closedBall c |R|)).add (integrableOn_xi_log_norm c R).norm).mul_continuousOn
      hψ.norm.continuousOn (isCompact_closedBall c |R|)
  have hzero : ∀ᵐ z : ℂ ∂(volume.restrict (closedBall c |R|)), xi z ≠ 0 :=
    ae_restrict_of_ae xi_ne_zero_ae
  apply tendsto_integral_of_dominated_convergence
    (fun z => (‖xi z‖ + ‖Real.log ‖xi z‖‖) * ‖ψ z‖)
    (fun n => ((contDiff_xiLogPotential (sourceRegulator_pos n)).continuous.mul
      hψ).aestronglyMeasurable.restrict) hi
  · intro n
    filter_upwards [hzero] with z hz
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using xiLogPotential_bound n hz) (norm_nonneg _)
  · filter_upwards [hzero] with z hz
    exact (tendsto_xiLogPotential hz).mul_const (ψ z)

/-- Compact-test convergence of the actual arithmetic potentials, with no zero-free support condition. -/
theorem tendsto_integral_xiLogPotential (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ z, xiLogPotential (sourceRegulator n) z * ψ z) atTop
      (𝓝 (∫ z, Real.log ‖xi z‖ * ψ z)) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hs : tsupport ψ ⊆ closedBall (0 : ℂ) |R| :=
    hR.trans (closedBall_subset_closedBall (le_abs_self R))
  have heq (g : ℂ → ℝ) :
      (∫ z in closedBall (0 : ℂ) |R|, g z * ψ z) = ∫ z, g z * ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), mul_zero]
  simpa only [heq] using tendsto_integral_xiLogPotential_on_disc ψ hψ 0 R

end GaloisForLFunctions.ConjugateDiagonalGeometry
