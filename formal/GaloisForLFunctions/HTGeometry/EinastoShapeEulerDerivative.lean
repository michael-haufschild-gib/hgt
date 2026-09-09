import GaloisForLFunctions.HTGeometry.EinastoShapeSource

/-!
# Weighted radial derivatives of the actual Einasto source factors

The Green inverse needs r E'(r), not a bounded E'(r). For the shape-dependent
quadratic source, build continuous extensions of r N'(r) and r A'(r), where
N is its normalized source factor and A is the algebraic sign defect. Both
weighted derivatives vanish at the center for every positive Einasto exponent.
All derivatives come from the actual density, mass integral, and metric.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Differentiate the actual enclosed-density factor, with its exact removable numerator. -/
theorem einastoCore_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoCore d l a)
      ((4 * Real.pi * einastoDensity d l a (exp t) - 3 * einastoCore d l a (exp t)) / exp t) (exp t) := by
  have h := (einastoMass_derivative d l a (exp t)).div
    ((hasDerivAt_id (exp t)).pow 3) (pow_ne_zero 3 (exp_ne_zero t))
  simp only [Pi.div_def, Pi.pow_apply, id_eq] at h
  have hd : HasDerivAt (fun r => einastoMass d l a r / r ^ 3)
      ((4 * Real.pi * einastoDensity d l a (exp t) - 3 * einastoCore d l a (exp t)) / exp t) (exp t) := by
    apply h.congr_deriv
    rw [einastoMass_core]
    norm_num only [Nat.cast_ofNat]
    field_simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  rw [einastoMass_core]
  field_simp [hr.ne']

/-- Continuous expression for the Euler derivative r N'(r). -/
def einastoShapeSourceFactorEuler (d l a r : ℝ) : ℝ :=
  let q := exp (-a)
  let u := einastoProfilePower l a r
  let ρ := einastoDensity d l a r
  let f := einastoMetric d l a r
  let c := einastoCore d l a r
  let v := 2 * c - 8 * Real.pi * ρ
  let w := q + 4 - q * u
  let b := (q + 1) * (q + 4) - q * (3 * q + 5) * u + q ^ 2 * u ^ 2
  let ρE := -q * u * ρ
  let fE := r ^ 2 * v
  let vE := 2 * (4 * Real.pi * ρ - 3 * c) - 8 * Real.pi * ρE
  let bE := -q ^ 2 * (3 * q + 5) * u + 2 * q ^ 3 * u ^ 2
  (4 * Real.pi * (2 * ρ * ρE) * q * r ^ 2 * (q * u - 4) +
    4 * Real.pi * ρ ^ 2 * q * (2 * r ^ 2) * (q * u - 4) +
    4 * Real.pi * ρ ^ 2 * q * r ^ 2 * (q ^ 2 * u)) -
  (2 * fE * q * ρ * b + 2 * f * q * ρE * b + 2 * f * q * ρ * bE) -
  (q * ρE * r ^ 2 * v * w + q * ρ * (2 * r ^ 2) * v * w +
    q * ρ * r ^ 2 * vE * w + q * ρ * r ^ 2 * v * (-q ^ 2 * u))

/-- Continuous expression for the Euler derivative of the algebraic sign defect. -/
def einastoShapeSourceDefectEuler (d l a σ r : ℝ) : ℝ :=
  (σ - 1) * (2 * einastoShapeRicci d l a r *
    (8 * Real.pi * exp (-a) * einastoDensity d l a r * einastoProfilePower l a r *
      (exp (-a) + 4 - exp (-a) * einastoProfilePower l a r))) / (16 * Real.pi)

theorem einastoShapeSourceFactorEuler_continuous (d l a : ℝ) :
    Continuous (einastoShapeSourceFactorEuler d l a) := by
  have hD := einastoDensity_continuous d l a
  have hU := einastoProfilePower_continuous l a
  have hf := einastoMetric_continuous d l a
  have hC := einastoCore_continuous d l a
  unfold einastoShapeSourceFactorEuler
  dsimp only
  fun_prop

theorem einastoShapeSourceDefectEuler_continuous (d l a σ : ℝ) :
    Continuous (einastoShapeSourceDefectEuler d l a σ) := by
  have hR := einastoShapeRicci_continuous d l a
  have hD := einastoDensity_continuous d l a
  have hU := einastoProfilePower_continuous l a
  unfold einastoShapeSourceDefectEuler
  fun_prop

theorem einastoShapeSourceFactorEuler_core (d l a : ℝ) : einastoShapeSourceFactorEuler d l a 0 = 0 := by
  unfold einastoShapeSourceFactorEuler
  rw [einastoProfilePower_zero]
  ring

theorem einastoShapeSourceDefectEuler_core (d l a σ : ℝ) : einastoShapeSourceDefectEuler d l a σ 0 = 0 := by
  unfold einastoShapeSourceDefectEuler
  rw [einastoProfilePower_zero]
  ring

/-- The normalized source's actual derivative is the proved Euler extension divided by radius. -/
theorem einastoShapeSourceFactor_hasDerivAt (d l a t : ℝ) :
    HasDerivAt (einastoShapeSourceFactor d l a)
      (einastoShapeSourceFactorEuler d l a (exp t) / exp t) (exp t) := by
  have hD := einastoDensity_derivative d l a t
  have hU := einastoProfilePower_hasDerivAt l a t
  have hf := einastoMetricFirstJet_hasDerivAt d l a t
  have hC := einastoCore_hasDerivAt d l a t
  have hX := (hasDerivAt_id (exp t)).pow 2
  have hA := (hU.const_mul (exp (-a))).sub_const 4
  have hB := ((hU.const_mul (exp (-a) * (3 * exp (-a) + 5))).const_sub
    ((exp (-a) + 1) * (exp (-a) + 4))).add ((hU.pow 2).const_mul (exp (-a) ^ 2))
  have hV := (hC.const_mul 2).sub (hD.const_mul (8 * Real.pi))
  have hW := (hU.const_mul (exp (-a))).const_sub (exp (-a) + 4)
  have h1 := (((((hD.pow 2).const_mul (4 * Real.pi)).mul_const (exp (-a))).mul hX).mul hA)
  have h2 := ((((hf.const_mul 2).mul_const (exp (-a))).mul hD).mul hB)
  have h3 := ((((hD.const_mul (exp (-a))).mul hX).mul hV).mul hW)
  have h := (h1.sub h2).sub h3
  simp only [Pi.mul_def, Pi.sub_def, Pi.add_def, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  unfold einastoShapeSourceFactorEuler einastoSlope einastoMetricFirstJet einastoProfilePower
  dsimp only
  norm_num only [Nat.cast_ofNat, pow_one]
  field_simp

theorem einastoShapeSourceDefect_hasDerivAt (d l a σ t : ℝ) :
    HasDerivAt (einastoShapeSourceDefect d l a σ)
      (einastoShapeSourceDefectEuler d l a σ (exp t) / exp t) (exp t) := by
  have h := (((einastoShapeRicci_hasDerivAt d l a t).pow 2).const_mul (σ - 1)).div_const (16 * Real.pi)
  simp only [Pi.pow_apply] at h
  apply h.congr_deriv
  unfold einastoShapeSourceDefectEuler einastoShapeRicciSlope
  norm_num only [Nat.cast_ofNat, pow_one]
  field_simp

/-- The derivative may be unbounded, but its radial weight always vanishes. -/
theorem einastoShapeSourceFactor_weighted_derivative_limit (d l a : ℝ) :
    Tendsto (fun t => exp t * deriv (einastoShapeSourceFactor d l a) (exp t)) atBot (𝓝 0) := by
  have he : (fun t => exp t * deriv (einastoShapeSourceFactor d l a) (exp t)) =
      (fun t => einastoShapeSourceFactorEuler d l a (exp t)) := by
    funext t
    rw [(einastoShapeSourceFactor_hasDerivAt d l a t).deriv]
    field_simp
  rw [he, ← einastoShapeSourceFactorEuler_core d l a]
  exact (einastoShapeSourceFactorEuler_continuous d l a).continuousAt.tendsto.comp tendsto_exp_atBot

theorem einastoShapeSourceDefect_weighted_derivative_limit (d l a σ : ℝ) :
    Tendsto (fun t => exp t * deriv (einastoShapeSourceDefect d l a σ) (exp t)) atBot (𝓝 0) := by
  have he : (fun t => exp t * deriv (einastoShapeSourceDefect d l a σ) (exp t)) =
      (fun t => einastoShapeSourceDefectEuler d l a σ (exp t)) := by
    funext t
    rw [(einastoShapeSourceDefect_hasDerivAt d l a σ t).deriv]
    field_simp
  rw [he, ← einastoShapeSourceDefectEuler_core d l a σ]
  exact (einastoShapeSourceDefectEuler_continuous d l a σ).continuousAt.tendsto.comp tendsto_exp_atBot

end GaloisForLFunctions.HTGeometry
