import GaloisForLFunctions.BiScaleUncertainty.LogarithmicPathKernel
import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearAndMultiplicativeGraphUncertainty
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Exact path-congestion transfer for diffuse and countable-line edge measures

A concrete mixture of weighted Lebesgue edges and countably many weighted lag
lines is automatically s-finite. Tonelli transports its entire jump energy to
the additive logarithmic Dirichlet density, with an exact nonnegative slack.
All total energies are extended nonnegative integrals; no finiteness or analytic
admission premise is imposed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

/-- Concrete diffuse weights and countably many weighted horizontal lag lines. -/
structure EdgeMixture where
  diffuseWeight : Edge → ℝ≥0∞
  lag : ℕ → ℝ
  lineWeight : ℕ → ℝ → ℝ≥0∞

def diffuseMeasure (D : EdgeMixture) : Measure Edge :=
  ((volume.restrict (Ioi (0 : ℝ))).prod volume).withDensity D.diffuseWeight

def lineMeasure (D : EdgeMixture) (n : ℕ) : Measure Edge :=
  Measure.map (fun u : ℝ => (D.lag n,u)) (volume.withDensity (D.lineWeight n))

def edgeMeasure (D : EdgeMixture) : Measure Edge :=
  diffuseMeasure D + Measure.sum (lineMeasure D)

instance sFinite_diffuseMeasure (D : EdgeMixture) : SFinite (diffuseMeasure D) := by
  unfold diffuseMeasure
  infer_instance

instance sFinite_lineMeasure (D : EdgeMixture) (n : ℕ) : SFinite (lineMeasure D n) := by
  unfold lineMeasure
  infer_instance

instance sFinite_edgeMeasure (D : EdgeMixture) : SFinite (edgeMeasure D) := by
  unfold edgeMeasure
  infer_instance

def congestion (D : EdgeMixture) (y : ℝ) : ℝ≥0∞ := ∫⁻ e, pathKernel e y ∂edgeMeasure D

theorem measurable_congestion (D : EdgeMixture) : Measurable (congestion D) :=
  measurable_pathKernel.lintegral_prod_left

def jumpEnergy (D : EdgeMixture) (q : Velocity) : ℝ≥0∞ := ∫⁻ e, jump q e ∂edgeMeasure D

def slackEnergy (D : EdgeMixture) (q : Velocity) : ℝ≥0∞ := ∫⁻ e, slack q e ∂edgeMeasure D

def congestionEnergy (D : EdgeMixture) (q : Velocity) : ℝ≥0∞ :=
  ∫⁻ y, congestion D y*density q y

/-- Tonelli applies to the constructed measure, without an energy-integrability premise. -/
theorem congestionEnergy_eq_budget (D : EdgeMixture) (q : Velocity) :
    congestionEnergy D q = ∫⁻ e, budget q e ∂edgeMeasure D := by
  calc
    _ = ∫⁻ y, ∫⁻ e, pathKernel e y*density q y ∂edgeMeasure D := by
      apply lintegral_congr
      intro y
      exact (lintegral_mul_const (density q y) (measurable_pathKernel_left y)).symm
    _ = _ := (lintegral_lintegral_swap
      (μ := edgeMeasure D) (ν := volume)
      (measurable_pathKernel.mul ((measurable_density q).comp measurable_snd)).aemeasurable).symm

/-- Exact energy transfer with a nonnegative remainder, including infinite total energies. -/
theorem congestionEnergy_eq_jump_add_slack (D : EdgeMixture) (q : Velocity) :
    congestionEnergy D q = jumpEnergy D q+slackEnergy D q := by
  rw [congestionEnergy_eq_budget]
  calc
    _ = ∫⁻ e, jump q e+slack q e ∂edgeMeasure D := by
      apply lintegral_congr
      intro e
      exact (jump_add_slack q e).symm
    _ = _ := lintegral_add_left (measurable_jump q) (slack q)

/-- The congestion-weighted density is the actual logarithmic derivative density. -/
theorem congestionEnergy_eq_derivative (D : EdgeMixture) (q : Velocity) :
    congestionEnergy D q = ∫⁻ y, congestion D y *
      ENNReal.ofReal (Real.exp (-y)*(deriv (logPrimitive q) y)^2) := by
  apply lintegral_congr_ae
  filter_upwards [ae_velocityDensity_eq_derivative q] with y hy
  rw [density, hy]

theorem derivativeEnergy_eq_jump_add_slack (D : EdgeMixture) (q : Velocity) :
    (∫⁻ y, congestion D y * ENNReal.ofReal (Real.exp (-y)*(deriv (logPrimitive q) y)^2)) =
      jumpEnergy D q+slackEnergy D q := by
  rw [← congestionEnergy_eq_derivative, congestionEnergy_eq_jump_add_slack]

theorem jumpEnergy_le_derivativeEnergy (D : EdgeMixture) (q : Velocity) :
    jumpEnergy D q ≤ ∫⁻ y, congestion D y *
      ENNReal.ofReal (Real.exp (-y)*(deriv (logPrimitive q) y)^2) := by
  rw [derivativeEnergy_eq_jump_add_slack]
  exact le_add_of_nonneg_right zero_le

private theorem lintegral_edgeMeasure (D : EdgeMixture) (g : Edge → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ e, g e ∂edgeMeasure D) = (∫⁻ e, g e ∂diffuseMeasure D) +
      ∑' n, ∫⁻ u, g (D.lag n,u) ∂volume.withDensity (D.lineWeight n) := by
  rw [edgeMeasure, lintegral_add_measure, lintegral_sum_measure]
  congr 1
  apply tsum_congr
  intro n
  exact lintegral_map hg (measurable_const.prodMk measurable_id)

/-- The entire countable family is retained, rather than a finite edge truncation. -/
theorem jumpEnergy_eq_diffuse_add_lines (D : EdgeMixture) (q : Velocity) :
    jumpEnergy D q = (∫⁻ e, jump q e ∂diffuseMeasure D) +
      ∑' n, ∫⁻ u, jump q (D.lag n,u) ∂volume.withDensity (D.lineWeight n) :=
  lintegral_edgeMeasure D (jump q) (measurable_jump q)

theorem congestion_eq_diffuse_add_lines (D : EdgeMixture) (y : ℝ) :
    congestion D y = (∫⁻ e, pathKernel e y ∂diffuseMeasure D) +
      ∑' n, ∫⁻ u, pathKernel (D.lag n,u) y ∂volume.withDensity (D.lineWeight n) :=
  lintegral_edgeMeasure D (fun e => pathKernel e y) (measurable_pathKernel_left y)

/-- Four times the opposite-sign endpoint pairing, retaining an arbitrary added constant. -/
def nodalCost (q : Velocity) (c : ℝ) (e : Edge) : ℝ≥0∞ := ENNReal.ofReal (4 *
  (max (c+logPrimitive q (e.2+e.1)) 0 * max (-(c+logPrimitive q e.2)) 0 +
   max (-(c+logPrimitive q (e.2+e.1))) 0 * max (c+logPrimitive q e.2) 0))

theorem measurable_nodalCost (q : Velocity) (c : ℝ) : Measurable (nodalCost q c) := by
  have hf := (continuous_logPrimitive q).measurable
  unfold nodalCost
  fun_prop

theorem nodalCost_le_jump (q : Velocity) (c : ℝ) (e : Edge) : nodalCost q c e ≤ jump q e := by
  apply ENNReal.ofReal_le_ofReal
  have h := four_mul_nodal_cross_le_mulJump_sq
    (fun j : ℕ => if j = 1 then c+logPrimitive q e.2 else c+logPrimitive q (e.2+e.1)) 2 1
  simpa [seqPos, seqNeg, mulJump] using h

def nodalEnergy (D : EdgeMixture) (q : Velocity) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ e, nodalCost q c e ∂edgeMeasure D

theorem nodalEnergy_le_jumpEnergy (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    nodalEnergy D q c ≤ jumpEnergy D q :=
  lintegral_mono (nodalCost_le_jump q c)

/-- Infinite diffuse and arithmetic nodal attraction is controlled by additive regularity. -/
theorem nodalEnergy_le_derivativeEnergy (D : EdgeMixture) (q : Velocity) (c : ℝ) :
    nodalEnergy D q c ≤ ∫⁻ y, congestion D y *
      ENNReal.ofReal (Real.exp (-y)*(deriv (logPrimitive q) y)^2) :=
  (nodalEnergy_le_jumpEnergy D q c).trans (jumpEnergy_le_derivativeEnergy D q)

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
