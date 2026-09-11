import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSelfChannelHorizonJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPrincipalChannelHorizonJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalContactHorizonFactor
import GaloisForLFunctions.HTGeometry.AnalyticJetGerm

/-!
# Analytic horizon-jet germ of the cleared temporal current

The horizon-mode leg of the continued temporal Einstein current has the radial density
`(-2u(λ-2)·f·g - u·g·F_h)·N` (`continuedPhysicalTimeAction_radial_density`).  Multiplying by the
self-channel clearing factor and dividing by `z^u` in the horizon coordinate gives the cleared
density core: a polynomial combination of the cleared self profile, the principal profiles, the
Gauss factor, the elementary amplitude profile and the reduced horizon quotient.  Every factor has
an analytic horizon-jet germ at the fundamental QNM, hence so does the density, by closure alone.
The identification with the actual current is proved in the companion module; nothing here
evaluates a physical current.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric Polynomial D4BMLaplaceRadial D4BMModularCore D4BMJointWave
  D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-! ## Profiles -/

/-- The Gauss factor of the horizon mode in the horizon coordinate. -/
def gaussProfile (q : XiZeroCopy) (u : ℂ) (z : ℝ) : ℂ :=
  gaussFactor u (physicalRadialFrequency q) false (z:ℂ)

/-- The frequency-free part of the reduced horizon quotient as a polynomial in the radial unit. -/
def horizonQuotientBase (s : ℂ) : Polynomial ℂ :=
  -2 * (1 + X) * X * (C ((5 * s ^ 2 + 15 * s + 4) / 4) + C (s * (s - 1) * (s + 2) ^ 2 / 4) * X ^ 2) +
    C (s * (s - 1) / 4) * (C (4 * s ^ 2) * (X - 1) * X ^ 3 + C (12 * s) * X ^ 2 * (X ^ 2 - 1) +
      C (2 * s) * (X + 1) * X ^ 3 + 6 * X * (X - 1) * (X + 1) ^ 2 + 6 * X ^ 3 * (X + 1)) -
    C (2 * (s + 1) * (s + 2) * (s * (s - 1) / 4)) * (1 + X) * X ^ 3

/-- The frequency-linear part of the reduced horizon quotient. -/
def horizonQuotientSlopePoly (s : ℂ) : Polynomial ℂ :=
  C (s * (s - 1) / 2) * X ^ 2 * (C (2 * s + 3) * X + 3)

theorem horizonQuotientBase_eval (s r : ℂ) :
    (horizonQuotientBase s).eval r = reducedHorizonPolynomial s r := by
  simp only [horizonQuotientBase, reducedHorizonPolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow, eval_neg, eval_one, eval_ofNat]
  ring

theorem horizonQuotientSlopePoly_eval (s r : ℂ) :
    (horizonQuotientSlopePoly s).eval r = s * (s - 1) / 2 * r ^ 2 * ((2 * s + 3) * r + 3) := by
  simp only [horizonQuotientSlopePoly, eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_ofNat]

/-- The reduced horizon quotient in the horizon coordinate. -/
def quotientProfile (q : XiZeroCopy) (branch : Bool) (u : ℂ) (z : ℝ) : ℂ :=
  reducedHorizonQuotient (physicalRate q branch) u (Real.sqrt (1 - z))

theorem quotientProfile_eq (q : XiZeroCopy) (branch : Bool) (u : ℂ) (z : ℝ) :
    quotientProfile q branch u z =
      ((horizonQuotientBase (physicalRate q branch)).eval (Real.sqrt (1 - z) : ℂ) +
        u * (horizonQuotientSlopePoly (physicalRate q branch)).eval (Real.sqrt (1 - z) : ℂ)) *
        ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ^ (-1 : ℂ) := by
  unfold quotientProfile reducedHorizonQuotient
  rw [horizonQuotientBase_eval, horizonQuotientSlopePoly_eval, Complex.cpow_neg_one]
  push_cast
  rw [div_eq_mul_inv]

/-- The self part of the cleared density: cleared self channel plus principal channels. -/
def selfPart (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ) (z : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q * selfClearedProfile q branch a u z +
    reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
      ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) /
        physicalAngularGap q q i * principalProfile q branch a i u z

/-- The cleared contact part of the density. -/
def contactPart (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ) (z : ℝ) : ℂ :=
  reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
    (amplitudeProfile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) u z *
        quotientProfile q branch u z * scalarResidualPeriod q (physicalAngularParameter q) +
      ∑ i : Fin 3, principalProfile q branch a i u z *
        scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i))

/-- The cleared density core: the cleared current divided by `z^u`. -/
def clearedDensityCore (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point)
    (u : ℂ) (z : ℝ) : ℂ :=
  modeAngularSquare (physicalModeAngularJet q zang) *
    ((-2 * u * (physicalAngularParameter q ^ 2 - 1 / 4 - 2) * selfPart q branch a u z -
      u * contactPart q branch a u z) * gaussProfile q u z)

/-- The cleared density in the horizon coordinate, including the Jacobian `1/(2√(1-z))`. -/
def clearedDensityProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point)
    (u : ℂ) (z : ℝ) : ℂ :=
  clearedDensityCore q branch a zang u z * ((Real.sqrt (1 - z))⁻¹ : ℂ) / 2

/-! ## Germs of the factors -/

theorem gaussProfile_germ (q : XiZeroCopy) (side : Bool) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (gaussProfile q) := by
  have hw : (physicalFundamentalFrequency q side).im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  obtain ⟨R, C, L, hR, hC, hL, hg⟩ := horizonGauss_uniform_second_bound
    (physicalFundamentalFrequency q side) (physicalRadialFrequency q) hw (b := 1 / 2) (by norm_num)
    (by norm_num)
  have hj : HasUniformJet2 (closedBall (physicalFundamentalFrequency q side) (R / 2)) (1 / 2)
      (gaussProfile q) (fun _ => 1) (fun u => horizonGaussFirstCoefficient u (physicalRadialFrequency q))
      C := by
    intro u hu z hz
    have hu' : u ∈ ball (physicalFundamentalFrequency q side) R := by
      have := mem_closedBall.mp hu; exact mem_ball.mpr (by linarith)
    exact (hg u hu').2 z ⟨hz.1.le, hz.2⟩
  exact AnalyticJet2At.of_jet (half_pos hR) (by norm_num) le_rfl analyticAt_const
    (horizonGaussFirstCoefficient_analyticAt _ (physicalRadialFrequency q) hw) hj

theorem quotientProfile_germ (q : XiZeroCopy) (branch : Bool) (w₀ : ℂ) :
    AnalyticJet2At w₀ (quotientProfile q branch) := by
  have hr := AnalyticJet2At.sqrt_one_sub w₀
  have hP := hr.polynomial_eval (horizonQuotientBase (physicalRate q branch))
  have hS := hr.polynomial_eval (horizonQuotientSlopePoly (physicalRate q branch))
  have hinv := AnalyticJet2At.cpow_one_add_sqrt (w₀ := w₀) (α := fun _ => (-1:ℂ)) analyticAt_const
  refine ((hP.add ((AnalyticJet2At.id w₀).mul hS)).mul hinv).congr (fun u z => ?_)
  rw [quotientProfile_eq]

theorem amplitudeProfile_germ (s a : ℂ) (T : ℂ → ℂ) {w₀ : ℂ} (hT : AnalyticAt ℂ T w₀) :
    AnalyticJet2At w₀ (amplitudeProfile s a T) :=
  ((AnalyticJet2At.cpow_one_add_sqrt (α := fun u => 2 * s - u)
      (analyticAt_const.sub analyticAt_id)).mul
    (AnalyticJet2At.const (k := fun u => a ^ 2 * T u) (analyticAt_const.mul hT))).congr
    (fun u z => by simp only [amplitudeProfile])

theorem selfClearedProfile_germ (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (selfClearedProfile q branch a) := by
  obtain ⟨R, b, bE, C, hR, hb, hbh, h₀, h₁, -, hj⟩ := selfClearedProfile_jet q branch side a
  exact AnalyticJet2At.of_jet hR hb hbh h₀ h₁ hj

theorem principalProfile_germ (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (i : Fin 3) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (principalProfile q branch a i) := by
  obtain ⟨R, b, bE, C, hR, hb, hbh, h₀, h₁, -, hj⟩ := principalProfile_jet q branch side a i
  exact AnalyticJet2At.of_jet hR hb hbh h₀ h₁ hj

/-- The cleared density has an analytic horizon-jet germ at the fundamental QNM. -/
theorem clearedDensityProfile_germ (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (clearedDensityProfile q branch a zang) := by
  have hw : (physicalFundamentalFrequency q side).im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hs : physicalFundamentalFrequency q side - 2 * physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hX := selfClearedProfile_germ q branch side a
  have hY0 := principalProfile_germ q branch side a 0
  have hY1 := principalProfile_germ q branch side a 1
  have hY2 := principalProfile_germ q branch side a 2
  have hg := gaussProfile_germ q side
  have hA := amplitudeProfile_germ (physicalRate q branch) a (continuedOnset (physicalRate q branch))
    (continuedOnset_analyticAt _ _ hs)
  have hQ := quotientProfile_germ q branch (physicalFundamentalFrequency q side)
  have hcF : AnalyticAt ℂ
      (fun u => reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch))
      (physicalFundamentalFrequency q side) := by
    unfold reducedGreenClearingFactor
    exact (analyticAt_id.sub analyticAt_const).neg.mul
      (connection_frequency_analyticAt _ _ hw)
  have hself : AnalyticJet2At (physicalFundamentalFrequency q side) (selfPart q branch a) := by
    have h1 := hX.const_mul (k := fun _ => physicalSelfSourceCoefficient q) analyticAt_const
    have h2 := hY0.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 0) / physicalAngularGap q q 0) analyticAt_const
    have h3 := hY1.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 1) / physicalAngularGap q q 1) analyticAt_const
    have h4 := hY2.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 2) / physicalAngularGap q q 2) analyticAt_const
    refine (h1.add (((h2.add h3).add h4).const_mul hcF)).congr (fun u z => ?_)
    simp only [selfPart, Fin.sum_univ_three]
    try ring
  have hcontact : AnalyticJet2At (physicalFundamentalFrequency q side) (contactPart q branch a) := by
    have h1 := (hA.mul hQ).const_mul
      (k := fun _ => scalarResidualPeriod q (physicalAngularParameter q)) analyticAt_const
    have h2 := hY0.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 0)) analyticAt_const
    have h3 := hY1.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 1)) analyticAt_const
    have h4 := hY2.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 2)) analyticAt_const
    refine ((h1.add ((h2.add h3).add h4)).const_mul hcF).congr (fun u z => ?_)
    simp only [contactPart, Fin.sum_univ_three]
    try ring
  have hcore : AnalyticJet2At (physicalFundamentalFrequency q side)
      (clearedDensityCore q branch a zang) := by
    have h1 := hself.const_mul
      (k := fun u => -2 * u * (physicalAngularParameter q ^ 2 - 1 / 4 - 2))
      ((analyticAt_const.mul analyticAt_id).mul analyticAt_const)
    have h2 := hcontact.const_mul (k := fun u => u) analyticAt_id
    have h3 := (h1.sub h2).mul hg
    refine (h3.const_mul (k := fun _ => modeAngularSquare (physicalModeAngularJet q zang))
      analyticAt_const).congr (fun u z => ?_)
    simp only [clearedDensityCore]
    try ring
  exact ((hcore.mul (AnalyticJet2At.inv_sqrt_one_sub _)).div_const 2).congr
    (fun u z => by simp only [clearedDensityProfile])

end
end RHTower.D4BMJointSource
