import GaloisForLFunctions.HTGeometry.ChargedWaveFlux

/-!
# Exact charged-step scattering and interface regularity

An explicit application of the signed-channel flux mechanism in arXiv:2608.21406,
Theorem 1 and equations (27)--(31). Positive momenta are parameterized exponentially;
the incident amplitude is one, and the transmitted local frequency is negative.
The constructed field has amplified reflection, conserved actual current, a C¹
interface, and an exact integrated radial equation. It is not twice differentiable
at the potential jump. This is an electrostatic step model, not a calculation of
the reflection coefficient of the paper's smooth black-hole potential.
-/

noncomputable section
open Complex Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Positive infinity momentum, strictly above the magnitude of the negative horizon channel. -/
def chargedStepMomentum (a b : ℝ) : ℝ := Real.exp a + Real.exp b

def chargedStepReflection (a b : ℝ) : ℝ := 1 + 2 * Real.exp b / Real.exp a

def chargedStepTransmission (a b : ℝ) : ℝ := 2 + 2 * Real.exp b / Real.exp a

def chargedStepLeftWave (a b : ℝ) : ℝ → ℂ :=
  chargedChannelWave (chargedStepTransmission a b : ℂ) 0 (-Real.exp b)

def chargedStepRightWave (a b : ℝ) : ℝ → ℂ :=
  chargedChannelWave 1 (chargedStepReflection a b : ℂ) (chargedStepMomentum a b)

def chargedStepWave (a b x : ℝ) : ℂ :=
  if x ≤ 0 then chargedStepLeftWave a b x else chargedStepRightWave a b x

def chargedStepWave1 (a b x : ℝ) : ℂ :=
  if x ≤ 0 then deriv (chargedStepLeftWave a b) x else deriv (chargedStepRightWave a b) x

def chargedStepChemicalPotential (a b x : ℝ) : ℝ :=
  if x ≤ 0 then Real.exp a + 2 * Real.exp b else 0

theorem chargedStepMomentum_pos (a b : ℝ) : 0 < chargedStepMomentum a b := by
  unfold chargedStepMomentum
  positivity

theorem chargedStepReflection_gt_one (a b : ℝ) : 1 < chargedStepReflection a b := by
  unfold chargedStepReflection
  have hp : 0 < 2 * Real.exp b / Real.exp a := by positivity
  linarith

theorem chargedStepTransmission_pos (a b : ℝ) : 0 < chargedStepTransmission a b := by
  unfold chargedStepTransmission
  positivity

theorem chargedStep_value_matching (a b : ℝ) : 1 + chargedStepReflection a b = chargedStepTransmission a b := by
  unfold chargedStepReflection chargedStepTransmission
  ring

theorem chargedStep_slope_matching (a b : ℝ) :
    chargedStepMomentum a b * (chargedStepReflection a b - 1) =
      Real.exp b * chargedStepTransmission a b := by
  unfold chargedStepMomentum chargedStepReflection chargedStepTransmission
  field_simp
  ring

theorem chargedStep_amplitude_flux_identity (a b : ℝ) :
    chargedStepMomentum a b * (chargedStepReflection a b ^ 2 - 1) =
      Real.exp b * chargedStepTransmission a b ^ 2 := by
  unfold chargedStepMomentum chargedStepReflection chargedStepTransmission
  field_simp
  ring

theorem chargedStep_interface_value (a b : ℝ) : chargedStepLeftWave a b 0 = chargedStepRightWave a b 0 := by
  simp only [chargedStepLeftWave, chargedStepRightWave, chargedChannelWave, FDNLS.staggerPhase, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one, add_zero]
  exact_mod_cast (chargedStep_value_matching a b).symm

theorem chargedStep_interface_derivative (a b : ℝ) :
    deriv (chargedStepLeftWave a b) 0 = deriv (chargedStepRightWave a b) 0 := by
  rw [chargedStepLeftWave, chargedStepRightWave,
    (chargedChannelWave_derivative (chargedStepTransmission a b : ℂ) 0 (-Real.exp b) 0).deriv,
    (chargedChannelWave_derivative 1 (chargedStepReflection a b : ℂ) (chargedStepMomentum a b) 0).deriv]
  simp only [FDNLS.staggerPhase, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, zero_sub,
    Complex.ofReal_neg]
  have h := congrArg Complex.ofReal (chargedStep_slope_matching a b)
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one] at h
  linear_combination -I * h

private theorem chargedStepLeftWave_differentiable (a b x : ℝ) :
    HasDerivAt (chargedStepLeftWave a b) (deriv (chargedStepLeftWave a b) x) x := by
  unfold chargedStepLeftWave
  exact (chargedChannelWave_derivative _ _ _ x).differentiableAt.hasDerivAt

private theorem chargedStepRightWave_differentiable (a b x : ℝ) :
    HasDerivAt (chargedStepRightWave a b) (deriv (chargedStepRightWave a b) x) x := by
  unfold chargedStepRightWave
  exact (chargedChannelWave_derivative _ _ _ x).differentiableAt.hasDerivAt

/-- Both analytic branches have the same actual derivative at the interface. -/
theorem chargedStepWave_derivative_zero (a b : ℝ) :
    HasDerivAt (chargedStepWave a b) (deriv (chargedStepLeftWave a b) 0) 0 := by
  have hl : HasDerivWithinAt (chargedStepWave a b) (deriv (chargedStepLeftWave a b) 0) (Iic 0) 0 := by
    apply (chargedStepLeftWave_differentiable a b 0).hasDerivWithinAt.congr
    · intro x hx
      simp only [chargedStepWave, if_pos (show x ≤ 0 from hx)]
    · simp only [chargedStepWave, le_refl, if_true]
  have hr : HasDerivWithinAt (chargedStepWave a b) (deriv (chargedStepRightWave a b) 0) (Ici 0) 0 := by
    apply (chargedStepRightWave_differentiable a b 0).hasDerivWithinAt.congr
    · intro x hx
      by_cases h : x ≤ 0
      · have he : x = 0 := le_antisymm h hx
        subst x
        simpa only [chargedStepWave, le_refl, if_true] using chargedStep_interface_value a b
      · simp only [chargedStepWave, if_neg h]
    · simpa only [chargedStepWave, le_refl, if_true] using chargedStep_interface_value a b
  have hu := hl.union (hr.congr_deriv (chargedStep_interface_derivative a b).symm)
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hu

/-- The constructed scattering field is differentiable through the charged interface. -/
theorem chargedStepWave_derivative (a b x : ℝ) :
    HasDerivAt (chargedStepWave a b) (chargedStepWave1 a b x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have he : chargedStepWave a b =ᶠ[𝓝 x] chargedStepLeftWave a b := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp only [chargedStepWave, if_pos hy.le]
    simpa only [chargedStepWave1, if_pos hx.le] using
      (chargedStepLeftWave_differentiable a b x).congr_of_eventuallyEq he
  · subst x
    simpa only [chargedStepWave1, le_refl, if_true] using chargedStepWave_derivative_zero a b
  · have he : chargedStepWave a b =ᶠ[𝓝 x] chargedStepRightWave a b := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp only [chargedStepWave, if_neg (not_le.mpr hy)]
    simpa only [chargedStepWave1, if_neg (not_le.mpr hx)] using
      (chargedStepRightWave_differentiable a b x).congr_of_eventuallyEq he

theorem chargedStepWave_continuous (a b : ℝ) : Continuous (chargedStepWave a b) :=
  (show Differentiable ℝ (chargedStepWave a b) from fun x => (chargedStepWave_derivative a b x).differentiableAt).continuous

theorem chargedStepLeftWave_flux (a b x : ℝ) :
    complexRadialFlux (chargedStepLeftWave a b) x = Real.exp b * chargedStepTransmission a b ^ 2 := by
  rw [chargedStepLeftWave, chargedChannelWave_flux]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_sub]
  ring

theorem chargedStepRightWave_flux (a b x : ℝ) :
    complexRadialFlux (chargedStepRightWave a b) x = Real.exp b * chargedStepTransmission a b ^ 2 := by
  rw [chargedStepRightWave, chargedChannelWave_flux]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_one, one_pow]
  exact chargedStep_amplitude_flux_identity a b

/-- The negative-frequency transmitted channel and amplified reflection have identical actual flux. -/
theorem chargedStepWave_flux (a b x : ℝ) :
    complexRadialFlux (chargedStepWave a b) x = Real.exp b * chargedStepTransmission a b ^ 2 := by
  rw [complexRadialFlux, (chargedStepWave_derivative a b x).deriv]
  by_cases hx : x ≤ 0
  · simp only [chargedStepWave, chargedStepWave1, if_pos hx]
    exact chargedStepLeftWave_flux a b x
  · simp only [chargedStepWave, chargedStepWave1, if_neg hx]
    exact chargedStepRightWave_flux a b x

theorem chargedStepWave_flux_conserved (a b x : ℝ) :
    HasDerivAt (complexRadialFlux (chargedStepWave a b)) 0 x := by
  simp only [funext (chargedStepWave_flux a b)]
  exact hasDerivAt_const x _

theorem chargedStepWave_flux_pos (a b x : ℝ) : 0 < complexRadialFlux (chargedStepWave a b) x := by
  rw [chargedStepWave_flux]
  exact mul_pos (Real.exp_pos b) (sq_pos_of_pos (chargedStepTransmission_pos a b))

/-- Conserved positive current rules out zeros of the entire joined scattering field. -/
theorem chargedStepWave_ne_zero (a b x : ℝ) : chargedStepWave a b x ≠ 0 := by
  intro h
  have hp := chargedStepWave_flux_pos a b x
  simp only [complexRadialFlux, h, map_zero, zero_mul, Complex.zero_im] at hp
  exact lt_irrefl 0 hp

theorem chargedStep_reflection_power_gt_one (a b : ℝ) : chargedStepReflection a b ^ 2 > 1 := by
  have h := chargedStepReflection_gt_one a b
  nlinarith

theorem chargedStep_horizon_frequency (a b u : ℝ) :
    chargedStepMomentum a b - chargedStepChemicalPotential a b (-Real.exp u) = -Real.exp b := by
  simp only [chargedStepMomentum, chargedStepChemicalPotential, if_pos (neg_nonpos.mpr (Real.exp_pos u).le)]
  ring

theorem chargedStep_infinity_frequency (a b u : ℝ) :
    chargedStepMomentum a b - chargedStepChemicalPotential a b (Real.exp u) = chargedStepMomentum a b := by
  simp only [chargedStepChemicalPotential, if_neg (not_le.mpr (Real.exp_pos u)), sub_zero]

/-- Negative local frequency carries negative gauge-covariant charge density on the transmitted side. -/
theorem chargedStep_transmitted_charge_neg (a b u : ℝ) :
    (chargedStepMomentum a b - chargedStepChemicalPotential a b (-Real.exp u)) *
      ‖chargedStepWave a b (-Real.exp u)‖ ^ 2 < 0 := by
  rw [chargedStep_horizon_frequency]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos b))
    (sq_pos_of_pos (norm_pos_iff.mpr (chargedStepWave_ne_zero a b _)))

/-- Positive local frequency carries positive gauge-covariant density on the incident side. -/
theorem chargedStep_incident_charge_pos (a b u : ℝ) :
    (chargedStepMomentum a b - chargedStepChemicalPotential a b (Real.exp u)) *
      ‖chargedStepWave a b (Real.exp u)‖ ^ 2 > 0 := by
  rw [chargedStep_infinity_frequency]
  exact mul_pos (chargedStepMomentum_pos a b)
    (sq_pos_of_pos (norm_pos_iff.mpr (chargedStepWave_ne_zero a b _)))


/-- The physical first derivative is continuous, including across the potential jump. -/
theorem chargedStepWave_continuous_derivative (a b : ℝ) :
    Continuous (deriv (chargedStepWave a b)) := by
  rw [show deriv (chargedStepWave a b) = chargedStepWave1 a b from
    funext fun x => (chargedStepWave_derivative a b x).deriv]
  unfold chargedStepWave1
  apply Continuous.if
  · intro x hx
    have hx0 : x = 0 := frontier_Iic_subset 0 hx
    subst x
    exact chargedStep_interface_derivative a b
  · exact (show Differentiable ℝ (deriv (chargedStepLeftWave a b)) from
      fun x => (chargedChannelWave_second_derivative _ _ _ x).differentiableAt).continuous
  · exact (show Differentiable ℝ (deriv (chargedStepRightWave a b)) from
      fun x => (chargedChannelWave_second_derivative _ _ _ x).differentiableAt).continuous

theorem chargedStepWave_contDiff_one (a b : ℝ) : ContDiff ℝ 1 (chargedStepWave a b) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (chargedStepWave_derivative a b x).differentiableAt,
    chargedStepWave_continuous_derivative a b⟩

/-- The actual second derivative on every point of the transmitted half-line. -/
theorem chargedStepWave_second_derivative_left (a b u : ℝ) :
    HasDerivAt (deriv (chargedStepWave a b))
      (-((-Real.exp b : ℝ) : ℂ) ^ 2 * chargedStepWave a b (-Real.exp u)) (-Real.exp u) := by
  have hx : -Real.exp u < 0 := neg_neg_of_pos (Real.exp_pos u)
  have he : deriv (chargedStepWave a b) =ᶠ[𝓝 (-Real.exp u)]
      deriv (chargedStepLeftWave a b) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    rw [(chargedStepWave_derivative a b y).deriv]
    simp only [chargedStepWave1, if_pos hy.le]
  simpa only [chargedStepWave, if_pos hx.le, chargedStepLeftWave] using
    (chargedChannelWave_second_derivative (chargedStepTransmission a b : ℂ) 0
      (-Real.exp b) (-Real.exp u)).congr_of_eventuallyEq he

/-- The actual second derivative on every point of the incident half-line. -/
theorem chargedStepWave_second_derivative_right (a b u : ℝ) :
    HasDerivAt (deriv (chargedStepWave a b))
      (-(chargedStepMomentum a b : ℂ) ^ 2 * chargedStepWave a b (Real.exp u)) (Real.exp u) := by
  have hx := Real.exp_pos u
  have he : deriv (chargedStepWave a b) =ᶠ[𝓝 (Real.exp u)]
      deriv (chargedStepRightWave a b) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [(chargedStepWave_derivative a b y).deriv]
    simp only [chargedStepWave1, if_neg (not_le.mpr hy)]
  simpa only [chargedStepWave, if_neg (not_le.mpr hx), chargedStepRightWave] using
    (chargedChannelWave_second_derivative 1 (chargedStepReflection a b : ℂ)
      (chargedStepMomentum a b) (Real.exp u)).congr_of_eventuallyEq he

theorem chargedStepWave_equation_left (a b u : ℝ) :
    deriv (deriv (chargedStepWave a b)) (-Real.exp u) +
      ((chargedStepMomentum a b - chargedStepChemicalPotential a b (-Real.exp u) : ℝ) : ℂ) ^ 2 *
        chargedStepWave a b (-Real.exp u) = 0 := by
  rw [(chargedStepWave_second_derivative_left a b u).deriv, chargedStep_horizon_frequency]
  ring

theorem chargedStepWave_equation_right (a b u : ℝ) :
    deriv (deriv (chargedStepWave a b)) (Real.exp u) +
      ((chargedStepMomentum a b - chargedStepChemicalPotential a b (Real.exp u) : ℝ) : ℂ) ^ 2 *
        chargedStepWave a b (Real.exp u) = 0 := by
  rw [(chargedStepWave_second_derivative_right a b u).deriv, chargedStep_infinity_frequency]
  ring


/-- Integrated curvature of the transmitted analytic branch. -/
theorem chargedStepLeftWave_integrated_equation (a b r : ℝ) :
    (∫ x in r..0, -((-Real.exp b : ℝ) : ℂ) ^ 2 * chargedStepLeftWave a b x) =
      deriv (chargedStepLeftWave a b) 0 - deriv (chargedStepLeftWave a b) r := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact chargedChannelWave_second_derivative _ _ _ x
  · exact (continuous_const.mul (show Continuous (chargedStepLeftWave a b) from
      (show Differentiable ℝ (chargedStepLeftWave a b) from
        fun x => (chargedStepLeftWave_differentiable a b x).differentiableAt).continuous)).intervalIntegrable _ _

/-- Integrated curvature of the incident and reflected analytic branch. -/
theorem chargedStepRightWave_integrated_equation (a b r : ℝ) :
    (∫ x in 0..r, -(chargedStepMomentum a b : ℂ) ^ 2 * chargedStepRightWave a b x) =
      deriv (chargedStepRightWave a b) r - deriv (chargedStepRightWave a b) 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact chargedChannelWave_second_derivative _ _ _ x
  · exact (continuous_const.mul (show Continuous (chargedStepRightWave a b) from
      (show Differentiable ℝ (chargedStepRightWave a b) from
        fun x => (chargedStepRightWave_differentiable a b x).differentiableAt).continuous)).intervalIntegrable _ _

/-- Exact integrated equation through the interface: no additional jump source is required. -/
theorem chargedStepWave_interface_balance (a b u v : ℝ) :
    (∫ x in (-Real.exp u)..0, -((-Real.exp b : ℝ) : ℂ) ^ 2 * chargedStepLeftWave a b x) +
      (∫ x in 0..Real.exp v, -(chargedStepMomentum a b : ℂ) ^ 2 * chargedStepRightWave a b x) =
        deriv (chargedStepWave a b) (Real.exp v) - deriv (chargedStepWave a b) (-Real.exp u) := by
  rw [chargedStepLeftWave_integrated_equation, chargedStepRightWave_integrated_equation,
    (chargedStepWave_derivative a b (Real.exp v)).deriv,
    (chargedStepWave_derivative a b (-Real.exp u)).deriv, chargedStep_interface_derivative]
  simp only [chargedStepWave1, if_neg (not_le.mpr (Real.exp_pos v)),
    if_pos (neg_nonpos.mpr (Real.exp_pos u).le)]
  ring

/-- Sharp interface regularity: the wave is C¹, but its first derivative has no derivative at zero. -/
theorem chargedStepWave_not_twice_differentiable (a b : ℝ) :
    ¬ DifferentiableAt ℝ (deriv (chargedStepWave a b)) 0 := by
  intro hd
  have hl : HasDerivWithinAt (deriv (chargedStepWave a b))
      (-((-Real.exp b : ℝ) : ℂ)^2 * chargedStepLeftWave a b 0) (Iic 0) 0 := by
    apply (chargedChannelWave_second_derivative (chargedStepTransmission a b : ℂ) 0
      (-Real.exp b) 0).hasDerivWithinAt.congr
    · intro x hx
      rw [(chargedStepWave_derivative a b x).deriv]
      simp only [chargedStepWave1, if_pos (show x ≤ 0 from hx), chargedStepLeftWave]
    · rw [(chargedStepWave_derivative a b 0).deriv]
      simp only [chargedStepWave1, le_refl, if_true, chargedStepLeftWave]
  have hr : HasDerivWithinAt (deriv (chargedStepWave a b))
      (-(chargedStepMomentum a b : ℂ)^2 * chargedStepRightWave a b 0) (Ici 0) 0 := by
    apply (chargedChannelWave_second_derivative 1 (chargedStepReflection a b : ℂ)
      (chargedStepMomentum a b) 0).hasDerivWithinAt.congr
    · intro x hx
      rw [(chargedStepWave_derivative a b x).deriv]
      by_cases h : x ≤ 0
      · have he : x = 0 := le_antisymm h hx
        subst x
        simpa only [chargedStepWave1, le_refl, if_true, chargedStepRightWave] using
          chargedStep_interface_derivative a b
      · simp only [chargedStepWave1, if_neg h, chargedStepRightWave]
    · rw [(chargedStepWave_derivative a b 0).deriv]
      simpa only [chargedStepWave1, le_refl, if_true, chargedStepRightWave] using
        chargedStep_interface_derivative a b
  have he := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _ hl hd.hasDerivAt.hasDerivWithinAt
  have he' := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hr hd.hasDerivAt.hasDerivWithinAt
  have hcoeff : -((-Real.exp b : ℝ) : ℂ)^2 = -(chargedStepMomentum a b : ℂ)^2 := by
    apply mul_right_cancel₀ (show chargedStepLeftWave a b 0 ≠ 0 by
      simpa only [chargedStepWave, le_refl, if_true] using chargedStepWave_ne_zero a b 0)
    rw [chargedStep_interface_value] at he ⊢
    exact he.trans he'.symm
  have hreal := congrArg Complex.re hcoeff
  simp only [neg_sq, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    Complex.ofReal_re] at hreal
  unfold chargedStepMomentum at hreal
  have ha := Real.exp_pos a
  have hb := Real.exp_pos b
  nlinarith

end GaloisForLFunctions.HTGeometry
