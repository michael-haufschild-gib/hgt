import GaloisForLFunctions.HTGeometry.EinastoGammaMoments
import GaloisForLFunctions.HTGeometry.SpinTorsionSectorArithmetic

/-!
# Einasto radial gravity and its de Sitter core

Applies the mass construction of arXiv:2608.23600v1 to actual Lean derivatives:
the radial Einstein identity, second derivative, and finite central limits of
the spherical-lapse Ricci and Kretschmann expressions. Ricci follows the sign
convention printed in equation (9). These are the stated scalar expressions;
this module does not construct a spacetime metric tensor or its connection.

The limiting Kretschmann value agrees with the existing FLRW formula at `w=-1`.
This connects the radial density construction to the corpus's homogeneous
curvature arithmetic for every positive Einasto shape and length scale.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoMetric (d l a r : ℝ) : ℝ := 1 - 2 * einastoMass d l a r / r

theorem einastoMetric_core (d l a r : ℝ) :
    einastoMetric d l a r = 1 - 2 * r ^ 2 * einastoCore d l a r := by
  rw [einastoMetric, einastoMass_core]
  by_cases hr : r = 0
  · simp [hr]
  · field_simp

theorem einastoMetric_continuous (d l a : ℝ) : Continuous (einastoMetric d l a) := by
  simp only [funext (einastoMetric_core d l a)]
  exact continuous_const.sub ((continuous_const.mul (continuous_id.pow 2)).mul
    (einastoCore_continuous d l a))

theorem einastoMetric_zero (d l a : ℝ) : einastoMetric d l a 0 = 1 := by
  simp [einastoMetric_core]

theorem einastoMetric_flat_core_limit (d l a : ℝ) :
    Tendsto (einastoMetric d l a) (𝓝 0) (𝓝 1) := by
  simpa only [einastoMetric_zero] using (einastoMetric_continuous d l a).continuousAt.tendsto (x := 0)

theorem einastoMetric_quadratic_core_limit (d l a : ℝ) :
    Tendsto (fun t => (1 - einastoMetric d l a (exp t)) / exp t ^ 2) atBot
      (𝓝 (8 * Real.pi * exp d / 3)) := by
  have h := (einastoCore_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoCore_zero] at h
  have heq : (fun t => (1 - einastoMetric d l a (exp t)) / exp t ^ 2) =
      (fun t => 2 * einastoCore d l a (exp t)) := by
    funext t
    rw [einastoMetric_core]
    field_simp
    ring
  rw [heq]
  rw [show 8 * Real.pi * exp d / 3 = 2 * (4 * Real.pi * exp d / 3) by ring]
  exact h.const_mul 2

theorem einastoMetric_derivative (d l a t : ℝ) :
    HasDerivAt (einastoMetric d l a)
      (2 * einastoMass d l a (exp t) / exp t ^ 2 -
        8 * Real.pi * exp t * einastoDensity d l a (exp t)) (exp t) := by
  have h := (((einastoMass_derivative d l a (exp t)).const_mul 2).div
    (hasDerivAt_id (exp t)) (exp_ne_zero t)).const_sub 1
  apply h.congr_deriv
  dsimp
  field_simp
  ring

theorem einastoMetric_radial_Einstein_law (d l a t : ℝ) :
    1 - einastoMetric d l a (exp t) - exp t * deriv (einastoMetric d l a) (exp t) =
      8 * Real.pi * exp t ^ 2 * einastoDensity d l a (exp t) := by
  rw [(einastoMetric_derivative d l a t).deriv, einastoMetric]
  field_simp
  ring

def einastoSlope (d l a r : ℝ) : ℝ :=
  exp (-a) * (r / exp l) ^ exp (-a) * einastoDensity d l a r

theorem einastoSlope_continuous (d l a : ℝ) : Continuous (einastoSlope d l a) := by
  exact (continuous_const.mul ((continuous_rpow_const (exp_pos (-a)).le).comp
    (continuous_id.div_const (exp l)))).mul (einastoDensity_continuous d l a)

theorem einastoSlope_zero (d l a : ℝ) : einastoSlope d l a 0 = 0 := by
  simp [einastoSlope, Real.zero_rpow (exp_ne_zero (-a))]

theorem einastoDensity_derivative (d l a t : ℝ) :
    HasDerivAt (einastoDensity d l a) (-einastoSlope d l a (exp t) / exp t) (exp t) := by
  have hp : 0 < exp t / exp l := by positivity
  have h := ((((hasDerivAt_rpow_const (p := exp (-a)) (Or.inl hp.ne')).comp (exp t)
    ((hasDerivAt_id (exp t)).div_const (exp l))).neg).exp).const_mul (exp d)
  apply h.congr_deriv
  dsimp [einastoSlope, einastoDensity]
  rw [rpow_sub hp, rpow_one]
  field_simp

theorem einastoMetric_second_derivative (d l a t : ℝ) :
    HasDerivAt (deriv (einastoMetric d l a))
      (-4 * einastoCore d l a (exp t) + 8 * Real.pi * einastoSlope d l a (exp t)) (exp t) := by
  have h := (((einastoMass_derivative d l a (exp t)).const_mul 2).div
    ((hasDerivAt_id (exp t)).pow 2) (pow_ne_zero 2 (exp_ne_zero t))).sub
    (((hasDerivAt_id (exp t)).const_mul (8 * Real.pi)).mul (einastoDensity_derivative d l a t))
  have hd : HasDerivAt (fun r => 2 * einastoMass d l a r / r ^ 2 -
      8 * Real.pi * r * einastoDensity d l a r)
      (-4 * einastoCore d l a (exp t) + 8 * Real.pi * einastoSlope d l a (exp t)) (exp t) := by
    apply h.congr_deriv
    dsimp
    rw [einastoMass_core]
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have he := (einastoMetric_derivative d l a (log r)).deriv
  simpa only [exp_log hr] using he

/-- Equation (9) of arXiv:2608.23600, in its stated Ricci-sign convention. -/
def einastoRadialRicci (d l a r : ℝ) : ℝ :=
  deriv (deriv (einastoMetric d l a)) r + 4 * deriv (einastoMetric d l a) r / r +
    2 * (einastoMetric d l a r - 1) / r ^ 2

/-- The standard spherical-lapse Kretschmann expression, using actual Lean derivatives. -/
def einastoRadialKretschmann (d l a r : ℝ) : ℝ :=
  (deriv (deriv (einastoMetric d l a)) r) ^ 2 +
    4 * (deriv (einastoMetric d l a) r / r) ^ 2 +
    4 * ((1 - einastoMetric d l a r) / r ^ 2) ^ 2

theorem einastoRadialRicci_eq (d l a t : ℝ) :
    einastoRadialRicci d l a (exp t) =
      8 * Real.pi * (einastoSlope d l a (exp t) - 4 * einastoDensity d l a (exp t)) := by
  rw [einastoRadialRicci, (einastoMetric_second_derivative d l a t).deriv,
    (einastoMetric_derivative d l a t).deriv, einastoMetric_core, einastoMass_core]
  field_simp
  ring

theorem einastoRadialKretschmann_eq (d l a t : ℝ) :
    einastoRadialKretschmann d l a (exp t) =
      (-4 * einastoCore d l a (exp t) + 8 * Real.pi * einastoSlope d l a (exp t)) ^ 2 +
      4 * (2 * einastoCore d l a (exp t) - 8 * Real.pi * einastoDensity d l a (exp t)) ^ 2 +
      16 * einastoCore d l a (exp t) ^ 2 := by
  rw [einastoRadialKretschmann, (einastoMetric_second_derivative d l a t).deriv,
    (einastoMetric_derivative d l a t).deriv, einastoMetric_core, einastoMass_core]
  field_simp
  ring

theorem einastoRadialRicci_core_limit (d l a : ℝ) :
    Tendsto (fun t => einastoRadialRicci d l a (exp t)) atBot (𝓝 (-32 * Real.pi * exp d)) := by
  have hd := (einastoDensity_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot
  have hs := (einastoSlope_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoDensity_zero] at hd
  rw [einastoSlope_zero] at hs
  simp only [einastoRadialRicci_eq]
  have h := (hs.sub (hd.const_mul 4)).const_mul (8 * Real.pi)
  rw [show 8 * Real.pi * (0 - 4 * exp d) = -32 * Real.pi * exp d by ring] at h
  exact h

theorem einastoRadialKretschmann_core_limit (d l a : ℝ) :
    Tendsto (fun t => einastoRadialKretschmann d l a (exp t)) atBot
      (𝓝 (512 * Real.pi ^ 2 * exp d ^ 2 / 3)) := by
  have hd := (einastoDensity_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot
  have hs := (einastoSlope_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot
  have hc := (einastoCore_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot
  rw [einastoDensity_zero] at hd
  rw [einastoSlope_zero] at hs
  rw [einastoCore_zero] at hc
  have h := ((((hc.const_mul (-4)).add (hs.const_mul (8 * Real.pi))).pow 2).add
    ((((hc.const_mul 2).sub (hd.const_mul (8 * Real.pi))).pow 2).const_mul 4))
  have hh := h.add ((hc.pow 2).const_mul 16)
  simp only [einastoRadialKretschmann_eq]
  have heq : (-4 * (4 * Real.pi * exp d / 3) + 8 * Real.pi * 0) ^ 2 +
      4 * (2 * (4 * Real.pi * exp d / 3) - 8 * Real.pi * exp d) ^ 2 +
      16 * (4 * Real.pi * exp d / 3) ^ 2 = 512 * Real.pi ^ 2 * exp d ^ 2 / 3 := by ring
  rw [heq] at hh
  exact hh

theorem einasto_deSitter_flrw_curvature (d : ℝ) :
    flrwKretschmann 0 d (-1) = 512 * Real.pi ^ 2 * exp d ^ 2 / 3 := by
  unfold flrwKretschmann flrwKretschmannBracket
  rw [two_mul d, exp_add]
  norm_num
  ring

theorem einastoRadialKretschmann_flrw_limit (d l a : ℝ) :
    Tendsto (fun t => einastoRadialKretschmann d l a (exp t)) atBot
      (𝓝 (flrwKretschmann 0 d (-1))) := by
  rw [einasto_deSitter_flrw_curvature]
  exact einastoRadialKretschmann_core_limit d l a

end GaloisForLFunctions.HTGeometry
