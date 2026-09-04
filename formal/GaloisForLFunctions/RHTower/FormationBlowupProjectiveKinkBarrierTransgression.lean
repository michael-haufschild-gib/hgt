import GaloisForLFunctions.RHTower.PrimeHodgePoissonTwoChannelIntegralSplit
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinSchattenWall
import GaloisForLFunctions.HTGeometry.NoncommutativeQubitResponsePolarization
import GaloisForLFunctions.HTGeometry.ProjectiveSingularContinuousResidual
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import GaloisForLFunctions.HTGeometry.HyperbolicSourceRange
import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.HTGeometry.WholeLineWronskianSymmetry
import GaloisForLFunctions.HTGeometry.GronwallUniqueness
import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.IntegralGronwallAffine
import GaloisForLFunctions.RHTower.PerturbedDip
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall

/-!
# Prime-infinity formation blow-up

The prime/grade corner is resolved by the literal hyperbolic first column
`(sech (u/2), tanh (u/2))`.  This file records its oriented projective
compactification, exact kink phase, logarithmic cotangent barrier, prime sampling,
and the already certified Gamma--Bockstein Schatten wall.

Every statement is closed and unconditional.  No divisor, zero, ordinate, or RH
hypothesis enters any definition.
-/

open Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Normal visibility coordinate on the blown-up prime/grade corner. -/
def formationVisibility (u : ℝ) : ℝ := 1 / Real.cosh (u / 2)

/-- Normal contrast coordinate on the blown-up prime/grade corner. -/
def formationContrast (u : ℝ) : ℝ := Real.tanh (u / 2)

/-- Affine slope of the projective first column. -/
def formationSlope (u : ℝ) : ℝ := Real.sinh (u / 2)

/-- Canonical phase of the formation kink. -/
def formationPhase (u : ℝ) : ℝ := Real.arctan (formationSlope u)

theorem formationVisibility_pos (u : ℝ) : 0 < formationVisibility u := by
  exact one_div_pos.mpr (Real.cosh_pos _)

theorem formationVisibility_sq_add_contrast_sq (u : ℝ) :
    formationVisibility u ^ 2 + formationContrast u ^ 2 = 1 := by
  have h := HTGeometry.one_sub_tanh_sq (u / 2)
  rw [formationVisibility, formationContrast]
  calc
    (1 / Real.cosh (u / 2)) ^ 2 + Real.tanh (u / 2) ^ 2 =
        1 / Real.cosh (u / 2) ^ 2 + Real.tanh (u / 2) ^ 2 := by ring
    _ = (1 - Real.tanh (u / 2) ^ 2) + Real.tanh (u / 2) ^ 2 := by rw [h]
    _ = 1 := by ring

@[simp] theorem formationVisibility_neg (u : ℝ) :
    formationVisibility (-u) = formationVisibility u := by
  rw [formationVisibility, formationVisibility,
    show -u / 2 = -(u / 2) by ring, Real.cosh_neg]

@[simp] theorem formationContrast_neg (u : ℝ) :
    formationContrast (-u) = -formationContrast u := by
  rw [formationContrast, formationContrast,
    show -u / 2 = -(u / 2) by ring, Real.tanh_neg]

theorem formationSlope_eq_contrast_div_visibility (u : ℝ) :
    formationContrast u / formationVisibility u = formationSlope u := by
  rw [formationContrast, formationVisibility, formationSlope, Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos _).ne']

theorem formationSlope_hasDerivAt (u : ℝ) :
    HasDerivAt formationSlope (Real.cosh (u / 2) / 2) u := by
  unfold formationSlope
  convert GaloisForLFunctions.HTGeometry.hasDerivAt_sinh_mul (1 / 2) u using 1
  · congr 2
    ring
  · ring

theorem formationSlope_strictMono : StrictMono formationSlope := by
  apply strictMono_of_deriv_pos
  intro u
  rw [(formationSlope_hasDerivAt u).deriv]
  exact div_pos (Real.cosh_pos _) (by norm_num)

theorem formationSlope_surjective : Function.Surjective formationSlope := by
  intro y
  rcases Real.sinh_surjective y with ⟨x, hx⟩
  exact ⟨2 * x, by simpa [formationSlope] using hx⟩

/-- Orientation-preserving affine chart of the real projective line. -/
def formationSlopeOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective formationSlope formationSlope_strictMono
    formationSlope_surjective

/-- Compactified projective kink.  Both affine ends become the unique vertical line. -/
def formationProjectiveHomeomorph : OnePoint ℝ ≃ₜ OnePoint ℝ :=
  Homeomorph.onePointCongr formationSlopeOrderIso.toHomeomorph

@[simp] theorem formationProjectiveHomeomorph_coe (u : ℝ) :
    formationProjectiveHomeomorph (u : OnePoint ℝ) =
      (formationSlope u : OnePoint ℝ) := by
  simp [formationProjectiveHomeomorph, Homeomorph.onePointCongr,
    formationSlopeOrderIso]

@[simp] theorem formationProjectiveHomeomorph_infty :
    formationProjectiveHomeomorph (OnePoint.infty : OnePoint ℝ) =
      OnePoint.infty := by
  simp [formationProjectiveHomeomorph, Homeomorph.onePointCongr]

/-- Signed degree of an affine projective compactification, normalized by its slope orientation. -/
noncomputable def affineProjectiveDegree (f : ℝ → ℝ) : ℤ := by
  classical
  exact if StrictMono f then 1 else if StrictAnti f then -1 else 0

theorem formationProjectiveDegree_eq_one :
    affineProjectiveDegree formationSlope = 1 := by
  classical
  simp [affineProjectiveDegree, formationSlope_strictMono]

theorem formationPhase_cos (u : ℝ) :
    Real.cos (formationPhase u) = formationVisibility u := by
  rw [formationPhase, formationSlope, Real.cos_arctan]
  have hsq : 1 + Real.sinh (u / 2) ^ 2 = Real.cosh (u / 2) ^ 2 := by
    nlinarith [Real.cosh_sq (u / 2)]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos _)]
  rfl

theorem formationPhase_sin (u : ℝ) :
    Real.sin (formationPhase u) = formationContrast u := by
  rw [formationPhase, formationSlope, Real.sin_arctan]
  have hsq : 1 + Real.sinh (u / 2) ^ 2 = Real.cosh (u / 2) ^ 2 := by
    nlinarith [Real.cosh_sq (u / 2)]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos _)]
  exact (Real.tanh_eq_sinh_div_cosh _).symm

theorem formationPhase_hasDerivAt (u : ℝ) :
    HasDerivAt formationPhase (formationVisibility u / 2) u := by
  have h := (Real.hasDerivAt_arctan (formationSlope u)).comp u
    (formationSlope_hasDerivAt u)
  have hcoef :
      (1 / (1 + formationSlope u ^ 2)) * (Real.cosh (u / 2) / 2) =
        formationVisibility u / 2 := by
    rw [formationVisibility, formationSlope]
    have hsq : 1 + Real.sinh (u / 2) ^ 2 = Real.cosh (u / 2) ^ 2 := by
      nlinarith [Real.cosh_sq (u / 2)]
    rw [hsq]
    field_simp [(Real.cosh_pos _).ne']
  rw [hcoef] at h
  unfold formationPhase
  exact h

theorem formationPhase_tendsto_atTop :
    Tendsto formationPhase atTop (nhds (Real.pi / 2)) := by
  change Tendsto (Real.arctan ∘ formationSlopeOrderIso)
    atTop (nhds (Real.pi / 2))
  exact (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp
    formationSlopeOrderIso.tendsto_atTop

theorem formationPhase_tendsto_atBot :
    Tendsto formationPhase atBot (nhds (-(Real.pi / 2))) := by
  change Tendsto (Real.arctan ∘ formationSlopeOrderIso)
    atBot (nhds (-(Real.pi / 2)))
  exact (Real.tendsto_arctan_atBot.mono_right inf_le_left).comp
    formationSlopeOrderIso.tendsto_atBot

/-- Oriented rotation frame of the blow-up. -/
def formationRotation (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![formationVisibility u, -formationContrast u;
     formationContrast u, formationVisibility u]

/-- Quarter-turn endpoint frame. -/
def formationQuarterTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem formationRotation_transpose_mul (u : ℝ) :
    Matrix.transpose (formationRotation u) * formationRotation u = 1 := by
  have h := formationVisibility_sq_add_contrast_sq u
  rw [pow_two, pow_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formationRotation, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith

theorem formationRotation_det (u : ℝ) :
    Matrix.det (formationRotation u) = 1 := by
  have h := formationVisibility_sq_add_contrast_sq u
  rw [pow_two, pow_two] at h
  rw [Matrix.det_fin_two]
  simp [formationRotation]
  nlinarith

theorem formationRotation_mem_specialOrthogonal (u : ℝ) :
    Matrix.transpose (formationRotation u) * formationRotation u = 1 ∧
      Matrix.det (formationRotation u) = 1 :=
  ⟨formationRotation_transpose_mul u, formationRotation_det u⟩

theorem formationVisibility_tendsto_atTop :
    Tendsto formationVisibility atTop (nhds 0) := by
  have h := Real.continuous_cos.continuousAt.tendsto.comp formationPhase_tendsto_atTop
  convert h.congr' (Eventually.of_forall formationPhase_cos) using 1 <;>
    simp

theorem formationVisibility_tendsto_atBot :
    Tendsto formationVisibility atBot (nhds 0) := by
  have h := Real.continuous_cos.continuousAt.tendsto.comp formationPhase_tendsto_atBot
  have hend : Real.cos (-(Real.pi / 2)) = 0 := by
    rw [Real.cos_neg, Real.cos_pi_div_two]
  rw [hend] at h
  convert h.congr' (Eventually.of_forall formationPhase_cos) using 1 <;>
    simp

theorem formationContrast_tendsto_atTop :
    Tendsto formationContrast atTop (nhds 1) := by
  have h := Real.continuous_sin.continuousAt.tendsto.comp formationPhase_tendsto_atTop
  convert h.congr' (Eventually.of_forall formationPhase_sin) using 1 <;>
    simp

theorem formationContrast_tendsto_atBot :
    Tendsto formationContrast atBot (nhds (-1)) := by
  have h := Real.continuous_sin.continuousAt.tendsto.comp formationPhase_tendsto_atBot
  have hend : Real.sin (-(Real.pi / 2)) = -1 := by
    rw [Real.sin_neg, Real.sin_pi_div_two]
  rw [hend] at h
  convert h.congr' (Eventually.of_forall formationPhase_sin) using 1 <;>
    simp

theorem formationRotation_tendsto_atTop :
    Tendsto formationRotation atTop (nhds formationQuarterTurn) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  fin_cases i <;> fin_cases j
  · simpa [formationRotation, formationQuarterTurn] using formationVisibility_tendsto_atTop
  · simpa [formationRotation, formationQuarterTurn] using formationContrast_tendsto_atTop.neg
  · simpa [formationRotation, formationQuarterTurn] using formationContrast_tendsto_atTop
  · simpa [formationRotation, formationQuarterTurn] using formationVisibility_tendsto_atTop

theorem formationRotation_tendsto_atBot :
    Tendsto formationRotation atBot (nhds (-formationQuarterTurn)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  fin_cases i <;> fin_cases j
  · simpa [formationRotation, formationQuarterTurn] using formationVisibility_tendsto_atBot
  · simpa [formationRotation, formationQuarterTurn] using formationContrast_tendsto_atBot.neg
  · simpa [formationRotation, formationQuarterTurn] using formationContrast_tendsto_atBot
  · simpa [formationRotation, formationQuarterTurn] using formationVisibility_tendsto_atBot

/-! ## Exact finite-action kink -/

/-- A globally differentiable finite-action lift with the two projective endpoint values.
Every such lift is, in particular, absolutely continuous on every compact interval. -/
structure FormationFiniteActionLift where
  phase : ℝ → ℝ
  velocity : ℝ → ℝ
  hasDerivAt : ∀ u, HasDerivAt phase (velocity u) u
  velocity_continuous : Continuous velocity
  kinetic_integrable : Integrable (fun u => velocity u ^ 2)
  potential_integrable : Integrable (fun u => Real.cos (phase u) ^ 2)
  endpoint_atTop : Tendsto phase atTop (nhds (Real.pi / 2))
  endpoint_atBot : Tendsto phase atBot (nhds (-(Real.pi / 2)))

/-- Formation blow-up action in the normalization of `(FBG.8)`. -/
def formationAction (lift : FormationFiniteActionLift) : ℝ :=
  (1 / 2 : ℝ) * ∫ u : ℝ,
    (lift.velocity u ^ 2 + Real.cos (lift.phase u) ^ 2 / 4)

theorem FormationFiniteActionLift.phase_continuous
    (lift : FormationFiniteActionLift) : Continuous lift.phase := by
  exact continuous_iff_continuousAt.mpr fun u => (lift.hasDerivAt u).continuousAt

theorem FormationFiniteActionLift.cross_integrable
    (lift : FormationFiniteActionLift) :
    Integrable (fun u => lift.velocity u * Real.cos (lift.phase u)) := by
  exact GaloisForLFunctions.HTGeometry.integrable_mul_of_sq_integrable
    lift.velocity_continuous.aestronglyMeasurable
    (Real.continuous_cos.comp lift.phase_continuous).aestronglyMeasurable
    lift.kinetic_integrable lift.potential_integrable

theorem FormationFiniteActionLift.integral_velocity_mul_cos
    (lift : FormationFiniteActionLift) :
    (∫ u : ℝ, lift.velocity u * Real.cos (lift.phase u)) = 2 := by
  let F : ℝ → ℝ := fun u => Real.sin (lift.phase u)
  let F' : ℝ → ℝ := fun u => lift.velocity u * Real.cos (lift.phase u)
  have hF : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    have h := (lift.hasDerivAt u).sin
    convert h using 1 <;> simp [F, F'] <;> ring
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun u =>
    (hF u).continuousAt
  have hplus : Tendsto F atTop (nhds 1) := by
    have h := Real.continuous_sin.continuousAt.tendsto.comp lift.endpoint_atTop
    change Tendsto (Real.sin ∘ lift.phase) atTop (nhds 1)
    simpa using h
  have hminus : Tendsto F atBot (nhds (-1)) := by
    have h := Real.continuous_sin.continuousAt.tendsto.comp lift.endpoint_atBot
    have hend : Real.sin (-(Real.pi / 2)) = -1 := by
      rw [Real.sin_neg, Real.sin_pi_div_two]
    rw [hend] at h
    change Tendsto (Real.sin ∘ lift.phase) atBot (nhds (-1))
    simpa using h
  have hright : ∫ u in Set.Ioi (0 : ℝ), F' u = 1 - F 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      hcont.continuousAt.continuousWithinAt (fun u _ => hF u)
      lift.cross_integrable.integrableOn hplus
  have hleft : ∫ u in Set.Iic (0 : ℝ), F' u = F 0 - (-1) :=
    MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto
      hcont.continuousAt.continuousWithinAt (fun u _ => hF u)
      lift.cross_integrable.integrableOn hminus
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) lift.cross_integrable.integrableOn
      lift.cross_integrable.integrableOn
  change (∫ u : ℝ, F' u) = 2
  rw [← hsplit, hleft, hright]
  ring

theorem FormationFiniteActionLift.mismatch_sq_integrable
    (lift : FormationFiniteActionLift) :
    Integrable (fun u =>
      (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2) := by
  have hcross := lift.cross_integrable
  have hexpanded : Integrable (fun u =>
      lift.velocity u ^ 2 - lift.velocity u * Real.cos (lift.phase u) +
        (1 / 4 : ℝ) * Real.cos (lift.phase u) ^ 2) :=
    (lift.kinetic_integrable.sub hcross).add
      (lift.potential_integrable.const_mul (1 / 4 : ℝ))
  exact hexpanded.congr (Eventually.of_forall fun u => by ring)

/-- Exact square completion: endpoint degree contributes the literal unit. -/
theorem formationAction_eq_one_add_mismatch (lift : FormationFiniteActionLift) :
    formationAction lift = 1 + (1 / 2 : ℝ) *
      ∫ u : ℝ, (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2 := by
  have hsum : Integrable (fun u =>
      lift.velocity u ^ 2 + Real.cos (lift.phase u) ^ 2 / 4) :=
    lift.kinetic_integrable.add (lift.potential_integrable.div_const 4)
  have hm := lift.mismatch_sq_integrable
  have hc := lift.cross_integrable
  have hpoint : (fun u =>
      lift.velocity u ^ 2 + Real.cos (lift.phase u) ^ 2 / 4) =
      (fun u => (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2 +
        lift.velocity u * Real.cos (lift.phase u)) := by
    funext u
    ring
  rw [formationAction, hpoint, MeasureTheory.integral_add hm hc,
    lift.integral_velocity_mul_cos]
  ring

/-- Sharp projective properness bound. -/
theorem formationAction_one_le (lift : FormationFiniteActionLift) :
    1 ≤ formationAction lift := by
  rw [formationAction_eq_one_add_mismatch]
  have hnonneg : 0 ≤ ∫ u : ℝ,
      (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2 :=
    MeasureTheory.integral_nonneg fun u => sq_nonneg _
  linarith

/-- Equality occurs exactly on the first-order kink equation, almost everywhere. -/
theorem formationAction_eq_one_iff (lift : FormationFiniteActionLift) :
    formationAction lift = 1 ↔
      (fun u => (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2) =ᵐ[volume]
        (fun _ => 0) := by
  rw [formationAction_eq_one_add_mismatch]
  have hnonneg : 0 ≤ᵐ[volume] (fun u =>
      (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2) :=
    Eventually.of_forall fun u => sq_nonneg _
  have hzero := MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg
    lift.mismatch_sq_integrable
  constructor
  · intro h
    apply hzero.mp
    linarith
  · intro h
    rw [hzero.mpr h]
    ring

theorem formationVisibility_sq_integrable :
    Integrable (fun u : ℝ => formationVisibility u ^ 2) := by
  have hbase := HTGeometry.integrable_cosh_rpow_neg (s := (2 : ℝ)) (by norm_num)
  have hscaled := hbase.comp_div (by norm_num : (2 : ℝ) ≠ 0)
  exact hscaled.congr (Eventually.of_forall fun u => by
    change Real.cosh (u / 2) ^ (-2 : ℝ) = (1 / Real.cosh (u / 2)) ^ 2
    have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
    rw [Real.rpow_neg hc.le]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring)

/-- Canonical theta kink as finite-action lift. -/
def canonicalFormationLift : FormationFiniteActionLift where
  phase := formationPhase
  velocity := fun u => formationVisibility u / 2
  hasDerivAt := formationPhase_hasDerivAt
  velocity_continuous := by
    exact (continuous_const.div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
      (fun u => (Real.cosh_pos _).ne')).div_const 2
  kinetic_integrable := by
    exact formationVisibility_sq_integrable.div_const 4 |>.congr
      (Eventually.of_forall fun u => by ring)
  potential_integrable := by
    exact formationVisibility_sq_integrable.congr
      (Eventually.of_forall fun u => by
        change formationVisibility u ^ 2 = Real.cos (formationPhase u) ^ 2
        rw [formationPhase_cos])
  endpoint_atTop := formationPhase_tendsto_atTop
  endpoint_atBot := formationPhase_tendsto_atBot

theorem canonicalFormationLift_mismatch (u : ℝ) :
    canonicalFormationLift.velocity u -
      Real.cos (canonicalFormationLift.phase u) / 2 = 0 := by
  change formationVisibility u / 2 - Real.cos (formationPhase u) / 2 = 0
  rw [formationPhase_cos]
  ring

theorem formationAction_canonical : formationAction canonicalFormationLift = 1 := by
  rw [formationAction_eq_one_add_mismatch]
  simp [canonicalFormationLift_mismatch]

private theorem formation_eq_at_of_ae_eq_of_continuousAt
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] [BorelSpace X]
    {mu : Measure X} [mu.IsOpenPosMeasure]
    {f g : X → E} {x : X} (hae : f =ᵐ[mu] g)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : f x = g x := by
  by_contra hne
  have hnorm : ContinuousAt (fun y => ‖f y - g y‖) x := (hf.sub hg).norm
  have hxpos : 0 < ‖f x - g x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hev : {y | 0 < ‖f y - g y‖} ∈ 𝓝 x :=
    hnorm.eventually (Ioi_mem_nhds hxpos)
  rcases mem_nhds_iff.mp hev with ⟨s, hs, hsopen, hxs⟩
  have hsub : s ⊆ {y | f y ≠ g y} := by
    intro y hy heq
    exact (norm_pos_iff.mp (hs hy)) (sub_eq_zero.mpr heq)
  have hnull : mu {y | f y ≠ g y} = 0 := hae
  have hsnull : mu s = 0 := measure_mono_null hsub hnull
  exact (hsopen.measure_ne_zero mu ⟨x, hxs⟩) hsnull

theorem FormationFiniteActionLift.velocity_eq_half_cos_of_action_eq_one
    (lift : FormationFiniteActionLift) (haction : formationAction lift = 1) (u : ℝ) :
    lift.velocity u = Real.cos (lift.phase u) / 2 := by
  have hae := (formationAction_eq_one_iff lift).mp haction
  have hcont : Continuous (fun x =>
      (lift.velocity x - Real.cos (lift.phase x) / 2) ^ 2) :=
    (lift.velocity_continuous.sub
      ((Real.continuous_cos.comp lift.phase_continuous).div_const 2)).pow 2
  have hu := formation_eq_at_of_ae_eq_of_continuousAt (x := u) hae
    hcont.continuousAt continuous_const.continuousAt
  norm_num at hu
  nlinarith [sq_nonneg (lift.velocity u - Real.cos (lift.phase u) / 2)]

theorem formationAction_eq_one_iff_velocity (lift : FormationFiniteActionLift) :
    formationAction lift = 1 ↔
      lift.velocity =ᵐ[volume]
        fun u => (1 / 2 : ℝ) * Real.cos (lift.phase u) := by
  constructor
  · intro h
    filter_upwards with u
    rw [lift.velocity_eq_half_cos_of_action_eq_one h u]
    ring
  · intro h
    apply (formationAction_eq_one_iff lift).2
    filter_upwards [h] with u hu
    rw [hu]
    ring

@[simp] theorem formationPhase_zero : formationPhase 0 = 0 := by
  simp [formationPhase, formationSlope]

/-- Anchoring the equality solution at the neutral frame selects the canonical theta kink. -/
theorem FormationFiniteActionLift.phase_eq_canonical_of_action_eq_one
    (lift : FormationFiniteActionLift) (haction : formationAction lift = 1)
    (hanchor : lift.phase 0 = 0) : lift.phase = formationPhase := by
  let e : ℝ → ℝ := fun x => lift.phase x - formationPhase x
  let e' : ℝ → ℝ := fun x =>
    Real.cos (lift.phase x) / 2 - Real.cos (formationPhase x) / 2
  let E : ℝ → ℝ := fun x => e x ^ 2
  let E' : ℝ → ℝ := fun x => 2 * e x * e' x
  have he : ∀ x, HasDerivAt e (e' x) x := by
    intro x
    have hl := lift.hasDerivAt x
    rw [lift.velocity_eq_half_cos_of_action_eq_one haction x] at hl
    have ht := formationPhase_hasDerivAt x
    rw [← formationPhase_cos] at ht
    exact hl.sub ht
  have hE : ∀ x, HasDerivAt E (E' x) x := by
    intro x
    have h := (he x).pow 2
    have hv : ((2 : ℕ) : ℝ) * e x ^ (2 - 1) * e' x = E' x := by
      simp [E']
    rw [hv] at h
    exact h
  have hnonneg : ∀ x, 0 ≤ E x := fun x => sq_nonneg _
  have habs : ∀ x, |E' x| ≤ E x := by
    intro x
    have hcos := abs_cos_sub_cos_le (lift.phase x) (formationPhase x)
    have heq : E' x = e x *
        (Real.cos (lift.phase x) - Real.cos (formationPhase x)) := by
      simp only [E', e']
      ring
    rw [heq, abs_mul]
    have hmul := mul_le_mul_of_nonneg_left hcos (abs_nonneg (e x))
    have heabs : |e x| ^ 2 = E x := by
      rw [sq_abs]
    nlinarith [hmul, heabs]
  have hEzero : E 0 = 0 := by
    simp [E, e, hanchor]
  funext x
  by_cases hx : 0 ≤ x
  · have hz := HTGeometry.eq_zero_of_nonneg_of_deriv_le_mul (K := 1) hx
      (fun y _ => hE y) (fun y _ => hnonneg y)
      (fun y _ => by
        simpa using le_trans (le_abs_self (E' y)) (habs y)) hEzero x
      ⟨hx, le_rfl⟩
    simp only [E, e] at hz
    nlinarith [sq_nonneg (lift.phase x - formationPhase x)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hz := HTGeometry.eq_zero_of_nonneg_of_neg_mul_le_deriv (K := 1) hx'
      (fun y _ => hE y) (fun y _ => hnonneg y)
      (fun y _ => by
        simpa using le_trans (neg_le_neg (habs y)) (neg_abs_le (E' y))) hEzero x
      ⟨le_rfl, hx'⟩
    simp only [E, e] at hz
    nlinarith [sq_nonneg (lift.phase x - formationPhase x)]

/-! ## Sharp action for every absolutely continuous finite-action lift -/

/-- Global sine is one-Lipschitz, used to transport local absolute continuity through the
boundary primitive. -/
theorem formationSin_lipschitz : LipschitzWith 1 Real.sin := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun x => (by simpa only [id_eq] using
      (hasDerivAt_id x).sin.differentiableAt)
  · intro x
    have hs : HasDerivAt Real.sin (Real.cos x) x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).sin
    rw [hs.deriv, ← NNReal.coe_le_coe]
    change ‖Real.cos x‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

/-- Global cosine is one-Lipschitz, the exact input for a.e.-ODE uniqueness. -/
theorem formationCos_lipschitz : LipschitzWith 1 Real.cos := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun x => (by simpa only [id_eq] using
      (hasDerivAt_id x).cos.differentiableAt)
  · intro x
    have hc : HasDerivAt Real.cos (-Real.sin x) x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).cos
    rw [hc.deriv, ← NNReal.coe_le_coe]
    change ‖-Real.sin x‖ ≤ (1 : ℝ)
    rw [norm_neg, Real.norm_eq_abs, abs_le]
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

private theorem integrable_tendsto_symmetric_intervalIntegral
    {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun n : ℕ => ∫ x in (-(n : ℝ))..(n : ℝ), f x) atTop
      (nhds (∫ x : ℝ, f x)) := by
  let s : ℕ → Set ℝ := fun n => Set.Ioc (-(n : ℝ)) (n : ℝ)
  have hmeas : ∀ n, MeasurableSet (s n) := fun _ => measurableSet_Ioc
  have hmono : Monotone s := by
    intro m n hmn x hx
    dsimp [s] at hx ⊢
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    constructor <;> linarith [hx.1, hx.2]
  have hunion : (⋃ n, s n) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, s, Set.mem_Ioc, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    have hleft : -(n : ℝ) < x := by
      linarith [neg_abs_le x]
    have hright : x ≤ (n : ℝ) := by
      linarith [le_abs_self x]
    exact ⟨n, hleft, hright⟩
  have h := MeasureTheory.tendsto_setIntegral_of_monotone hmeas hmono (by
    rw [hunion]
    simpa using hf)
  rw [hunion] at h
  have h' : Tendsto (fun n => ∫ x in s n, f x) atTop
      (nhds (∫ x : ℝ, f x)) := by simpa using h
  convert h' using 1
  funext n
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [intervalIntegral.integral_of_le (by linarith : (-(n : ℝ)) ≤ n)]

/-- A finite-action lift with precisely the paper theorem's regularity: local absolute
continuity, a chosen measurable a.e. derivative, finite kinetic and potential action, and the
two projective endpoint values.  No pointwise differentiability or derivative continuity is
required. -/
structure FormationAbsolutelyContinuousFiniteActionLift where
  phase : ℝ → ℝ
  velocity : ℝ → ℝ
  locally_absolutelyContinuous : ∀ a b,
    AbsolutelyContinuousOnInterval phase a b
  hasDerivAt_ae : ∀ᵐ u, HasDerivAt phase (velocity u) u
  velocity_aestronglyMeasurable : AEStronglyMeasurable velocity
  kinetic_integrable : Integrable (fun u => velocity u ^ 2)
  potential_integrable : Integrable (fun u => Real.cos (phase u) ^ 2)
  endpoint_atTop : Tendsto phase atTop (nhds (Real.pi / 2))
  endpoint_atBot : Tendsto phase atBot (nhds (-(Real.pi / 2)))

/-- Formation action on the full absolutely-continuous finite-action class. -/
def formationAbsolutelyContinuousAction
    (lift : FormationAbsolutelyContinuousFiniteActionLift) : ℝ :=
  (1 / 2 : ℝ) * ∫ u : ℝ,
    (lift.velocity u ^ 2 + Real.cos (lift.phase u) ^ 2 / 4)

theorem FormationAbsolutelyContinuousFiniteActionLift.phase_continuous
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    Continuous lift.phase := by
  rw [continuous_iff_continuousAt]
  intro x
  have h := (lift.locally_absolutelyContinuous (x - 1) (x + 1)).continuousOn
  apply h.continuousAt
  rw [Set.uIcc_of_le (by linarith)]
  exact Icc_mem_nhds (by linarith) (by linarith)

theorem FormationAbsolutelyContinuousFiniteActionLift.cross_integrable
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    Integrable (fun u => lift.velocity u * Real.cos (lift.phase u)) := by
  exact GaloisForLFunctions.HTGeometry.integrable_mul_of_sq_integrable
    lift.velocity_aestronglyMeasurable
    (Real.continuous_cos.comp lift.phase_continuous).aestronglyMeasurable
    lift.kinetic_integrable lift.potential_integrable

theorem FormationAbsolutelyContinuousFiniteActionLift.interval_cross
    (lift : FormationAbsolutelyContinuousFiniteActionLift) (a b : ℝ) :
    (∫ u in a..b, lift.velocity u * Real.cos (lift.phase u)) =
      Real.sin (lift.phase b) - Real.sin (lift.phase a) := by
  have hac : AbsolutelyContinuousOnInterval
      (fun u => Real.sin (lift.phase u)) a b :=
    GaloisForLFunctions.HTGeometry.LipschitzWith.comp_absolutelyContinuousOnInterval
      formationSin_lipschitz (lift.locally_absolutelyContinuous a b)
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [lift.hasDerivAt_ae] with u hu
  intro _
  simpa only [mul_comm] using hu.sin.deriv.symm

theorem FormationAbsolutelyContinuousFiniteActionLift.integral_velocity_mul_cos
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    (∫ u : ℝ, lift.velocity u * Real.cos (lift.phase u)) = 2 := by
  have hleft := integrable_tendsto_symmetric_intervalIntegral lift.cross_integrable
  have hformula : (fun n : ℕ =>
      ∫ u in (-(n : ℝ))..(n : ℝ),
        lift.velocity u * Real.cos (lift.phase u)) =
      fun n : ℕ => Real.sin (lift.phase (n : ℝ)) -
        Real.sin (lift.phase (-(n : ℝ))) := by
    funext n
    exact lift.interval_cross (-(n : ℝ)) (n : ℝ)
  rw [hformula] at hleft
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hnat
  have hp := lift.endpoint_atTop.comp hnat
  have hm := lift.endpoint_atBot.comp hneg
  have hpSin := Real.continuous_sin.continuousAt.tendsto.comp hp
  have hmSin := Real.continuous_sin.continuousAt.tendsto.comp hm
  have hright := hpSin.sub hmSin
  have hright' : Tendsto (fun n : ℕ => Real.sin (lift.phase (n : ℝ)) -
      Real.sin (lift.phase (-(n : ℝ)))) atTop (nhds 2) := by
    convert hright using 1 <;> norm_num
  exact tendsto_nhds_unique hleft hright'

theorem FormationAbsolutelyContinuousFiniteActionLift.mismatch_sq_integrable
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    Integrable (fun u =>
      (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2) := by
  have hcross := lift.cross_integrable
  have hexpanded : Integrable (fun u =>
      lift.velocity u ^ 2 - lift.velocity u * Real.cos (lift.phase u) +
        (1 / 4 : ℝ) * Real.cos (lift.phase u) ^ 2) :=
    (lift.kinetic_integrable.sub hcross).add
      (lift.potential_integrable.const_mul (1 / 4 : ℝ))
  exact hexpanded.congr (Eventually.of_forall fun u => by ring)

/-- Exact square completion for every absolutely continuous lift. -/
theorem formationAbsolutelyContinuousAction_eq_one_add_mismatch
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    formationAbsolutelyContinuousAction lift = 1 + (1 / 2 : ℝ) *
      ∫ u : ℝ, (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2 := by
  have hm := lift.mismatch_sq_integrable
  have hc := lift.cross_integrable
  have hpoint : (fun u =>
      lift.velocity u ^ 2 + Real.cos (lift.phase u) ^ 2 / 4) =
      (fun u => (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2 +
        lift.velocity u * Real.cos (lift.phase u)) := by
    funext u
    ring
  rw [formationAbsolutelyContinuousAction, hpoint,
    MeasureTheory.integral_add hm hc, lift.integral_velocity_mul_cos]
  ring

/-- Sharp projective properness on the full absolutely-continuous class. -/
theorem formationAbsolutelyContinuousAction_one_le
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    1 ≤ formationAbsolutelyContinuousAction lift := by
  rw [formationAbsolutelyContinuousAction_eq_one_add_mismatch]
  have hnonneg : 0 ≤ ∫ u : ℝ,
      (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2 :=
    MeasureTheory.integral_nonneg fun u => sq_nonneg _
  linarith

/-- Equality is exactly the kink ODE almost everywhere, with no regularity upgrade. -/
theorem formationAbsolutelyContinuousAction_eq_one_iff_velocity
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    formationAbsolutelyContinuousAction lift = 1 ↔
      lift.velocity =ᵐ[volume]
        fun u => (1 / 2 : ℝ) * Real.cos (lift.phase u) := by
  rw [formationAbsolutelyContinuousAction_eq_one_add_mismatch]
  have hnonneg : 0 ≤ᵐ[volume] (fun u =>
      (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2) :=
    Eventually.of_forall fun u => sq_nonneg _
  have hzero := MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg
    lift.mismatch_sq_integrable
  constructor
  · intro h
    have hmzero := hzero.mp (by linarith)
    filter_upwards [hmzero] with u hu
    have hz : lift.velocity u - Real.cos (lift.phase u) / 2 = 0 :=
      sq_eq_zero_iff.mp hu
    linarith
  · intro h
    have hmzero : (fun u =>
        (lift.velocity u - Real.cos (lift.phase u) / 2) ^ 2) =ᵐ[volume]
        (fun _ => 0) := by
      filter_upwards [h] with u hu
      rw [hu]
      ring
    rw [hzero.mpr hmzero]
    ring

private theorem formationForwardVolterra_zero
    {D g : ℝ → ℝ} (hD : Continuous D) (hg : Continuous g)
    {T : ℝ}
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      D t = ∫ s in (0 : ℝ)..t, g s)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      |g t| ≤ (1 / 2 : ℝ) * |D t|) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, D t = 0 := by
  let u : ℝ → ℝ := fun t => |D t|
  have hu : Continuous u := hD.abs
  have hvolterra : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t ≤ (0 : ℝ) * t + (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, u s := by
    intro t ht
    have hnorm : |∫ s in (0 : ℝ)..t, g s| ≤
        ∫ s in (0 : ℝ)..t, |g s| := by
      have hi := intervalIntegral.norm_integral_le_abs_integral_norm
        (μ := volume) (f := g) (a := (0 : ℝ)) (b := t)
      have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, |g s| :=
        intervalIntegral.integral_nonneg ht.1 (fun _ _ => abs_nonneg _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hi
    have hmono : (∫ s in (0 : ℝ)..t, |g s|) ≤
        ∫ s in (0 : ℝ)..t, (1 / 2 : ℝ) * u s := by
      exact intervalIntegral.integral_mono_on ht.1
        (hg.abs.intervalIntegrable 0 t)
        ((continuous_const.mul hu).intervalIntegrable 0 t)
        (fun s hs => hbound s ⟨hs.1, le_trans hs.2 ht.2⟩)
    change |D t| ≤ (0 : ℝ) * t +
      (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, u s
    rw [heq t ht]
    simp only [zero_mul, zero_add]
    calc
      |∫ s in (0 : ℝ)..t, g s| ≤ ∫ s in (0 : ℝ)..t, |g s| := hnorm
      _ ≤ ∫ s in (0 : ℝ)..t, (1 / 2 : ℝ) * u s := hmono
      _ = (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, u s := by
        rw [intervalIntegral.integral_const_mul]
  have hgr := GaloisForLFunctions.HTGeometry.DaiYoshikawa.le_affine_gronwall_of_volterra_bound
    (T := T) (a := 0) (b := (1 / 2 : ℝ)) (by norm_num) hu hvolterra
  intro t ht
  have hz := hgr t ht
  simp only [zero_div, zero_mul] at hz
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

private theorem formationGlobalVolterra_zero
    {D g : ℝ → ℝ} (hD : Continuous D) (hg : Continuous g)
    (heq : ∀ t, D t = ∫ s in (0 : ℝ)..t, g s)
    (hbound : ∀ t, |g t| ≤ (1 / 2 : ℝ) * |D t|) : D = 0 := by
  funext t
  change D t = 0
  rcases le_total 0 t with ht | ht
  · exact formationForwardVolterra_zero hD hg
      (fun s _ => heq s) (fun s _ => hbound s) t ⟨ht, le_rfl⟩
  · let Dr : ℝ → ℝ := fun s => D (-s)
    let gr : ℝ → ℝ := fun s => -g (-s)
    have hDr : Continuous Dr := hD.comp continuous_neg
    have hgr : Continuous gr := (hg.comp continuous_neg).neg
    have heqr : ∀ s, Dr s = ∫ v in (0 : ℝ)..s, gr v := by
      intro s
      change D (-s) = ∫ v in (0 : ℝ)..s, -g (-v)
      rw [heq (-s), intervalIntegral.integral_neg,
        intervalIntegral.integral_comp_neg g,
        neg_zero, intervalIntegral.integral_symm]
    have hboundr : ∀ s, |gr s| ≤ (1 / 2 : ℝ) * |Dr s| := by
      intro s
      simpa only [gr, Dr, abs_neg] using hbound (-s)
    have hT : 0 ≤ -t := by linarith
    simpa only [Dr, neg_neg] using
      formationForwardVolterra_zero hDr hgr
        (fun s _ => heqr s) (fun s _ => hboundr s)
        (-t) ⟨hT, le_rfl⟩

/-- Anchoring the a.e. equality solution selects the canonical kink throughout the full
absolutely-continuous class. -/
theorem FormationAbsolutelyContinuousFiniteActionLift.phase_eq_canonical_of_action_eq_one
    (lift : FormationAbsolutelyContinuousFiniteActionLift)
    (haction : formationAbsolutelyContinuousAction lift = 1)
    (hanchor : lift.phase 0 = 0) : lift.phase = formationPhase := by
  let D : ℝ → ℝ := fun t => lift.phase t - formationPhase t
  let g : ℝ → ℝ := fun t =>
    (Real.cos (lift.phase t) - Real.cos (formationPhase t)) / 2
  let canonicalVel : ℝ → ℝ := fun t => formationVisibility t / 2
  have hphaseCont : Continuous formationPhase := by
    rw [continuous_iff_continuousAt]
    exact fun t => (formationPhase_hasDerivAt t).continuousAt
  have hcanonicalVel : Continuous canonicalVel := by
    exact (continuous_const.div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
      (fun _ => (Real.cosh_pos _).ne')).div_const 2
  have hvel :=
    (formationAbsolutelyContinuousAction_eq_one_iff_velocity lift).mp haction
  have hD : Continuous D := lift.phase_continuous.sub hphaseCont
  have hg : Continuous g :=
    ((Real.continuous_cos.comp lift.phase_continuous).sub
      (Real.continuous_cos.comp hphaseCont)).div_const 2
  have heq : ∀ t, D t = ∫ s in (0 : ℝ)..t, g s := by
    intro t
    have hac := lift.locally_absolutelyContinuous 0 t
    have hphaseFTC := hac.integral_deriv_eq_sub
    have hcanonFTC : (∫ s in (0 : ℝ)..t, canonicalVel s) =
        formationPhase t - formationPhase 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => formationPhase_hasDerivAt s)
        (hcanonicalVel.intervalIntegrable 0 t)
    have hsub : (∫ s in (0 : ℝ)..t,
        deriv lift.phase s - canonicalVel s) =
        (∫ s in (0 : ℝ)..t, deriv lift.phase s) -
          ∫ s in (0 : ℝ)..t, canonicalVel s := by
      rw [intervalIntegral.integral_sub hac.intervalIntegrable_deriv
        (hcanonicalVel.intervalIntegrable 0 t)]
    have hcongr : (∫ s in (0 : ℝ)..t,
        deriv lift.phase s - canonicalVel s) =
        ∫ s in (0 : ℝ)..t, g s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [lift.hasDerivAt_ae, hvel] with s hs hvs
      intro _
      rw [hs.deriv, hvs]
      simp only [g, canonicalVel]
      rw [← formationPhase_cos]
      ring
    dsimp [D]
    rw [← hcongr, hsub, hphaseFTC, hcanonFTC,
      hanchor, formationPhase_zero]
    ring
  have hbound : ∀ t, |g t| ≤ (1 / 2 : ℝ) * |D t| := by
    intro t
    have hlip := formationCos_lipschitz.dist_le_mul
      (lift.phase t) (formationPhase t)
    have hlip' : |Real.cos (lift.phase t) - Real.cos (formationPhase t)| ≤
        |lift.phase t - formationPhase t| := by
      simpa [Real.dist_eq] using hlip
    dsimp [g, D]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hzero := formationGlobalVolterra_zero hD hg heq hbound
  funext t
  have ht := congrFun hzero t
  change lift.phase t - formationPhase t = 0 at ht
  linarith

private theorem absolutelyContinuousOnInterval_const (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
  rw [AbsolutelyContinuousOnInterval]
  simp
  exact tendsto_const_nhds

private theorem absolutelyContinuousOnInterval_congr_on
    {f h : ℝ → ℝ} {a b : ℝ}
    (hfh : Set.EqOn f h (Set.uIcc a b))
    (hh : AbsolutelyContinuousOnInterval h a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [AbsolutelyContinuousOnInterval] at hh ⊢
  apply hh.congr'
  have hevent : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hevent] with E hE
  obtain ⟨hpoints, -⟩ := hE
  apply Finset.sum_congr rfl
  intro i hi
  have hp := hpoints i hi
  rw [hfh hp.1, hfh hp.2]

/-- Canonical kink regarded as an absolutely-continuous finite-action lift. -/
def canonicalFormationAbsolutelyContinuousLift :
    FormationAbsolutelyContinuousFiniteActionLift where
  phase := formationPhase
  velocity := fun u => formationVisibility u / 2
  locally_absolutelyContinuous := by
    intro a b
    have hvcont : Continuous (fun u => formationVisibility u / 2) :=
      (continuous_const.div
        (Real.continuous_cosh.comp (continuous_id.div_const 2))
        (fun _ => (Real.cosh_pos _).ne')).div_const 2
    have hvI : IntervalIntegrable (fun u => formationVisibility u / 2)
        volume a b := hvcont.intervalIntegrable a b
    have hprim := hvI.absolutelyContinuousOnInterval_intervalIntegral
      Set.left_mem_uIcc
    have hsum :=
      (absolutelyContinuousOnInterval_const (formationPhase a) a b).add hprim
    apply absolutelyContinuousOnInterval_congr_on (h := fun x =>
      formationPhase a + ∫ u in a..x, formationVisibility u / 2) ?_ hsum
    intro x _
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => formationPhase_hasDerivAt u)
      (hvcont.intervalIntegrable a x)
    change formationPhase x = formationPhase a +
      ∫ u in a..x, formationVisibility u / 2
    rw [hFTC]
    ring
  hasDerivAt_ae := Eventually.of_forall formationPhase_hasDerivAt
  velocity_aestronglyMeasurable := by
    exact (continuous_const.div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
      (fun _ => (Real.cosh_pos _).ne')).div_const 2 |>.aestronglyMeasurable
  kinetic_integrable := by
    exact formationVisibility_sq_integrable.div_const 4 |>.congr
      (Eventually.of_forall fun u => by ring)
  potential_integrable := by
    exact formationVisibility_sq_integrable.congr
      (Eventually.of_forall fun u => by
        change formationVisibility u ^ 2 = Real.cos (formationPhase u) ^ 2
        rw [formationPhase_cos])
  endpoint_atTop := formationPhase_tendsto_atTop
  endpoint_atBot := formationPhase_tendsto_atBot

theorem formationAbsolutelyContinuousAction_canonical :
    formationAbsolutelyContinuousAction
      canonicalFormationAbsolutelyContinuousLift = 1 := by
  rw [formationAbsolutelyContinuousAction_eq_one_add_mismatch]
  simp [canonicalFormationAbsolutelyContinuousLift, formationPhase_cos]

/-! ## Prime sampling and logarithmic cotangent barrier -/

/-- Literal one-prime occupancy/Fisher weight. -/
def formationFisherWeight (p : Nat.Primes) : ℝ := (p : ℝ) / ((p : ℝ) + 1) ^ 2

/-- Open-chart logarithmic formation barrier. -/
def formationBarrier (p : Nat.Primes) (c : ℝ) : ℝ :=
  -2 * formationFisherWeight p * Real.log (1 - c ^ 2)

theorem formationBarrier_hasDerivAt
    (p : Nat.Primes) {c : ℝ} (hc : |c| < 1) :
    HasDerivAt (formationBarrier p)
      (4 * formationFisherWeight p * c / (1 - c ^ 2)) c := by
  rw [abs_lt] at hc
  have harg : 1 - c ^ 2 ≠ 0 := by nlinarith
  have hinner : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * c) c := by
    have h := (hasDerivAt_const c 1).sub ((hasDerivAt_id c).pow 2)
    change HasDerivAt (fun x : ℝ => 1 - x ^ 2)
      (0 - (2 : ℝ) * c ^ (2 - 1) * 1) c at h
    convert h using 1 <;> norm_num <;> ring
  change HasDerivAt (fun x : ℝ =>
    -2 * formationFisherWeight p * Real.log (1 - x ^ 2))
    (4 * formationFisherWeight p * c / (1 - c ^ 2)) c
  have h := (hinner.log harg).const_mul (-2 * formationFisherWeight p)
  have hcoef :
      -2 * formationFisherWeight p * (-2 * c / (1 - c ^ 2)) =
        4 * formationFisherWeight p * c / (1 - c ^ 2) := by ring
  rw [hcoef] at h
  exact h

theorem formationVisibility_prime_sample (a : ℝ) (p : Nat.Primes) :
    formationVisibility (a * Real.log (p : ℝ)) = primeHodgeVisibility a p := by
  simp [formationVisibility, primeHodgeVisibility, primeHodgeRapidity]

theorem formationContrast_prime_sample (a : ℝ) (p : Nat.Primes) :
    formationContrast (a * Real.log (p : ℝ)) = primeHodgeContrast a p := by
  simp [formationContrast, primeHodgeContrast, primeHodgeRapidity]

theorem primeHodgeContrast_odds (a : ℝ) (p : Nat.Primes) :
    ((p : ℝ) ^ a) =
      (1 + primeHodgeContrast a p) / (1 - primeHodgeContrast a p) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlog := GaloisForLFunctions.HTGeometry.log_tanh_odds_eq_two_mul
    (primeHodgeRapidity a p)
  have hratioPos : 0 <
      (1 + primeHodgeContrast a p) / (1 - primeHodgeContrast a p) := by
    apply div_pos
    · have h := Real.neg_one_lt_tanh (primeHodgeRapidity a p)
      rw [primeHodgeContrast]
      linarith
    · have h := Real.tanh_lt_one (primeHodgeRapidity a p)
      rw [primeHodgeContrast]
      linarith
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos hp a) hratioPos
  rw [Real.log_rpow hp]
  calc
    a * Real.log (p : ℝ) = 2 * primeHodgeRapidity a p := by
      rw [primeHodgeRapidity]
      ring
    _ = Real.log ((1 + primeHodgeContrast a p) /
        (1 - primeHodgeContrast a p)) := by
      simpa [primeHodgeContrast] using hlog.symm

theorem formationBarrier_deriv_prime_sample (a : ℝ) (p : Nat.Primes) :
    deriv (formationBarrier p) (primeHodgeContrast a p) =
      formationFisherWeight p * ((p : ℝ) ^ a - (p : ℝ) ^ (-a)) := by
  have hc : |primeHodgeContrast a p| < 1 := abs_primeHodgeContrast_lt_one a p
  rw [(formationBarrier_hasDerivAt p hc).deriv]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hodds := primeHodgeContrast_odds a p
  have hneg : (p : ℝ) ^ (-a) = ((p : ℝ) ^ a)⁻¹ := by
    rw [Real.rpow_neg hp.le]
  rw [abs_lt] at hc
  have hc1 : 1 - primeHodgeContrast a p ≠ 0 := by linarith
  have hc2 : 1 + primeHodgeContrast a p ≠ 0 := by linarith
  have hsq : 1 - primeHodgeContrast a p ^ 2 ≠ 0 := by nlinarith
  have hscalar :
      4 * primeHodgeContrast a p / (1 - primeHodgeContrast a p ^ 2) =
        (p : ℝ) ^ a - ((p : ℝ) ^ a)⁻¹ := by
    rw [hodds]
    field_simp [hc1, hc2, hsq]
    ring
  calc
    4 * formationFisherWeight p * primeHodgeContrast a p /
          (1 - primeHodgeContrast a p ^ 2) =
        formationFisherWeight p *
          (4 * primeHodgeContrast a p /
            (1 - primeHodgeContrast a p ^ 2)) := by ring
    _ = formationFisherWeight p *
        ((p : ℝ) ^ a - (p : ℝ) ^ (-a)) := by rw [hscalar, hneg]

theorem formationFisherWeight_eq_primeActivationOccupancyFisherDensity
    (p : Nat.Primes) :
    formationFisherWeight p = primeActivationOccupancyFisherDensity p := by
  rw [formationFisherWeight, primeActivationOccupancyFisherDensity_eq]

/-- Oriented (reflected minus forward) Gamma--Bockstein coefficient. -/
def formationGammaBockstein (a : ℝ) (p : Nat.Primes) : ℝ :=
  primeActivationOccupancyFisherTwist (-a) p -
    primeActivationOccupancyFisherTwist a p

theorem formationGammaBockstein_eq_neg_formationBarrier_deriv
    (a : ℝ) (p : Nat.Primes) :
    formationGammaBockstein a p =
      -deriv (formationBarrier p) (primeHodgeContrast a p) := by
  rw [formationBarrier_deriv_prime_sample,
    formationFisherWeight_eq_primeActivationOccupancyFisherDensity]
  simp [formationGammaBockstein, primeActivationOccupancyFisherTwist]
  ring

/-- The whole degree-one formation kink cannot fit inside the primitive Euler collision budget. -/
theorem routePPrimitiveCollisionCubicTraceBudget_lt_formationAction
    (lift : FormationAbsolutelyContinuousFiniteActionLift) :
    routePPrimitiveCollisionCubicTraceBudget <
      formationAbsolutelyContinuousAction lift := by
  calc
    routePPrimitiveCollisionCubicTraceBudget ≤
        (115 / 432 : ℝ) * ∑' p : Nat.Primes, invNatLogSq p :=
      routePPrimitiveCollisionCubicTraceBudget_le_primeInvLogSq
    _ < (115 / 432 : ℝ) * 2 :=
      mul_lt_mul_of_pos_left tsum_prime_invNatLogSq_lt_two (by norm_num)
    _ = 115 / 216 := by norm_num
    _ < 1 := by norm_num
    _ ≤ formationAbsolutelyContinuousAction lift :=
      formationAbsolutelyContinuousAction_one_le lift

/-- Closed scalar/operator/projective/cotangent certificate for the universal formation kink. -/
theorem formationBlowupProjectiveKinkBarrierTransgression_closed :
    affineProjectiveDegree formationSlope = 1 ∧
    (∀ u, formationVisibility u ^ 2 + formationContrast u ^ 2 = 1) ∧
    (∀ u, Matrix.transpose (formationRotation u) * formationRotation u = 1 ∧
      Matrix.det (formationRotation u) = 1) ∧
    Tendsto formationRotation atTop (nhds formationQuarterTurn) ∧
    Tendsto formationRotation atBot (nhds (-formationQuarterTurn)) ∧
    (∀ lift : FormationAbsolutelyContinuousFiniteActionLift,
      1 ≤ formationAbsolutelyContinuousAction lift) ∧
    (∀ lift : FormationAbsolutelyContinuousFiniteActionLift,
      routePPrimitiveCollisionCubicTraceBudget <
        formationAbsolutelyContinuousAction lift) ∧
    formationAbsolutelyContinuousAction
      canonicalFormationAbsolutelyContinuousLift = 1 ∧
    (∀ lift : FormationAbsolutelyContinuousFiniteActionLift,
      formationAbsolutelyContinuousAction lift = 1 ↔
        lift.velocity =ᵐ[MeasureTheory.volume]
          fun u => (1 / 2 : ℝ) * Real.cos (lift.phase u)) ∧
    (∀ lift : FormationAbsolutelyContinuousFiniteActionLift,
      formationAbsolutelyContinuousAction lift = 1 → lift.phase 0 = 0 →
        lift.phase = formationPhase) ∧
    (∀ (a : ℝ) (p : Nat.Primes),
      formationVisibility (a * Real.log (p : ℝ)) = primeHodgeVisibility a p ∧
      formationContrast (a * Real.log (p : ℝ)) = primeHodgeContrast a p) ∧
    (∀ a, ContinuousLinearMap.opTrace (primeHodgeVisibleMarginal a) +
      ContinuousLinearMap.opTrace (primeHodgeContrastMarginal a) = 1) ∧
    (∀ (a : ℝ) (p : Nat.Primes), formationGammaBockstein a p =
      -deriv (formationBarrier p) (primeHodgeContrast a p)) ∧
    (∀ a : ℝ, ∀ q : ℝ, 0 < q →
      (Summable (primeGammaCofinalBocksteinSchattenMass q a) ↔
        (a = 0 ∨ 1 < q * (1 - |a|)))) ∧
    (∀ a : ℝ, (∀ q : ℝ, 1 < q →
      Summable (primeGammaCofinalBocksteinSchattenMass q a)) ↔ a = 0) := by
  refine ⟨formationProjectiveDegree_eq_one,
    formationVisibility_sq_add_contrast_sq,
    formationRotation_mem_specialOrthogonal,
    formationRotation_tendsto_atTop,
    formationRotation_tendsto_atBot,
    formationAbsolutelyContinuousAction_one_le,
    routePPrimitiveCollisionCubicTraceBudget_lt_formationAction,
    formationAbsolutelyContinuousAction_canonical,
    formationAbsolutelyContinuousAction_eq_one_iff_velocity,
    FormationAbsolutelyContinuousFiniteActionLift.phase_eq_canonical_of_action_eq_one,
    ?_, opTrace_primeHodgeMarginals_add,
    formationGammaBockstein_eq_neg_formationBarrier_deriv, ?_, ?_⟩
  · exact fun a p => ⟨formationVisibility_prime_sample a p,
      formationContrast_prime_sample a p⟩
  · intro a q
    exact fun hq =>
      summable_primeGammaCofinalBocksteinSchattenMass_iff (t := a) (q := q) hq
  · intro a
    exact all_order_summable_primeGammaCofinalBocksteinSchattenMass_iff (t := a)

end
end RHTower
