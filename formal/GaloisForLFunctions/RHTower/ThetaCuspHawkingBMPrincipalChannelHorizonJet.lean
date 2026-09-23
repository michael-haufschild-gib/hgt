import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSelfChannelHorizonJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalPrincipalRegularity

/-!
# Uniform horizon jets of the principal cutoff channels

Each principal cutoff channel `continuedPrincipalDifference` is a continued response at the
principal frequency minus a radial lift, and its connection coefficient is nonzero at the
fundamental QNM.  Dividing by `z^{u/2}` therefore gives a profile with a uniform second-order
horizon jet on a closed frequency ball around the QNM, with analytic coefficients, and no clearing
is required.  This is the companion of the self-channel jet; it evaluates no physical current.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric D4BMLaplaceRadial D4BMModularCore
  GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- A principal cutoff channel in the horizon coordinate, divided by `z^{u/2}`. -/
def principalProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (u : ℂ) (z : ℝ) : ℂ :=
  continuedPrincipalDifference q branch u a i (tortoiseOf z) / (z:ℂ) ^ (u / 2)

/-- Constant jet coefficient of a principal channel. -/
def principalJetZero (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (b : ℝ) (u : ℂ) : ℂ :=
  clearedEndpoint (physicalRate q branch) (principalFrequency q i) a (principalAmplitude q i)
      (principalGradient q branch i) b u /
      reducedGreenClearingFactor u (principalFrequency q i) (physicalRate q branch) -
    principalAmplitude q i *
      ((-physicalRate q branch * (physicalRate q branch - 1) / 4) *
        ((2:ℂ) ^ (2 * physicalRate q branch - u) *
          (a ^ (2 : ℕ) * continuedOnset (physicalRate q branch) u)))

/-- Linear jet coefficient of a principal channel. -/
def principalJetOne (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (b : ℝ) (u : ℂ) : ℂ :=
  (clearedEndpoint (physicalRate q branch) (principalFrequency q i) a (principalAmplitude q i)
      (principalGradient q branch i) b u * horizonGaussFirstCoefficient u (principalFrequency q i) +
    reducedGreenClearingFactor u (principalFrequency q i) (physicalRate q branch) *
      horizonSlope (physicalRate q branch) (principalFrequency q i) a (principalAmplitude q i)
        (principalGradient q branch i) u) /
      reducedGreenClearingFactor u (principalFrequency q i) (physicalRate q branch) -
    principalAmplitude q i *
      ((-physicalRate q branch * (physicalRate q branch - 1) / 4) *
        ((2:ℂ) ^ (2 * physicalRate q branch - u) *
            (a ^ (2 : ℕ) * continuedOnset (physicalRate q branch) u) * (-3 / 2) +
          -(2 * physicalRate q branch - u) * (2:ℂ) ^ (2 * physicalRate q branch - u) / 4 *
            (a ^ (2 : ℕ) * continuedOnset (physicalRate q branch) u)))

theorem continuedOnset_analyticAt (s w : ℂ) (hs : w - 2 * s ≠ 0) :
    AnalyticAt ℂ (continuedOnset s) w := by
  have honset : AnalyticAt ℂ (fun u => onsetCorrection (2 * s) u) w :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (onsetCorrection_entire (2 * s))) w
      (mem_univ _)
  unfold continuedOnset
  exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add honset

/-- Uniform horizon jet of a principal channel around the fundamental QNM. -/
theorem principalProfile_jet (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (i : Fin 3) :
    ∃ R b bE C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1 / 2 ∧
      AnalyticAt ℂ (principalJetZero q branch a i bE) (physicalFundamentalFrequency q side) ∧
      AnalyticAt ℂ (principalJetOne q branch a i bE) (physicalFundamentalFrequency q side) ∧
      (∀ u ∈ closedBall (physicalFundamentalFrequency q side) R, ∀ z ∈ Ioc (0:ℝ) b,
        AnalyticAt ℂ (fun v => principalProfile q branch a i v z) u) ∧
      HasUniformJet2 (closedBall (physicalFundamentalFrequency q side) R) b
        (principalProfile q branch a i) (principalJetZero q branch a i bE)
        (principalJetOne q branch a i bE) C := by
  set w0 := physicalFundamentalFrequency q side with hw0
  have hw : w0.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hwr : -2 < w0.re := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  have hs : w0 - 2 * physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨R₁, b₁, C₁, hR₁, hb₁, hb₁h, hfacts, hgauss, hE, hjet⟩ :=
    clearedResponseQuotient_jet (physicalRate q branch) (principalFrequency q i) a
      (principalAmplitude q i) (principalGradient q branch i) w0 hw hwr hs
  -- the connection coefficient is nonzero near the QNM
  have hcne0 : connection w0 (principalFrequency q i) ≠ 0 :=
    physicalFundamental_principal_connection_ne_zero q side i
  obtain ⟨R₄, hR₄, hconnne⟩ := Metric.eventually_nhds_iff.mp
    ((connection_frequency_analyticAt w0 (principalFrequency q i) hw).continuousAt.eventually_ne hcne0)
  set R : ℝ := min R₁ R₄ / 2 with hR
  have hR0 : 0 < R := by positivity
  have hRR₁ : R ≤ R₁ := by
    have := min_le_left R₁ R₄; rw [hR]; linarith
  have hRR₄ : R < R₄ := by
    have := min_le_right R₁ R₄; rw [hR]; linarith
  have hsub : closedBall w0 R ⊆ closedBall w0 R₁ := closedBall_subset_closedBall hRR₁
  have hcne : ∀ u ∈ closedBall w0 R, connection u (principalFrequency q i) ≠ 0 := by
    intro u hu
    apply hconnne
    have := mem_closedBall.mp hu
    linarith
  have hcF : ∀ u ∈ closedBall w0 R,
      reducedGreenClearingFactor u (principalFrequency q i) (physicalRate q branch) ≠ 0 := by
    intro u hu
    unfold reducedGreenClearingFactor
    exact mul_ne_zero (neg_ne_zero.mpr (hfacts u (hsub hu)).2.2.1) (hcne u hu)
  have hcomp : IsCompact (closedBall w0 R) := isCompact_closedBall w0 R
  have hcFan : ∀ u ∈ closedBall w0 R, AnalyticAt ℂ
      (fun v => reducedGreenClearingFactor v (principalFrequency q i) (physicalRate q branch)) u := by
    intro u hu
    unfold reducedGreenClearingFactor
    exact (analyticAt_id.sub analyticAt_const).neg.mul
      (connection_frequency_analyticAt u (principalFrequency q i) (hfacts u (hsub hu)).1)
  obtain ⟨Kinv, hKinv⟩ := hcomp.exists_bound_of_continuousOn (f := fun u =>
      1 / reducedGreenClearingFactor u (principalFrequency q i) (physicalRate q branch))
    (fun u hu => ((analyticAt_const.div (hcFan u hu) (hcF u hu)).continuousAt).continuousWithinAt)
  have hTan : ∀ u ∈ closedBall w0 R, AnalyticAt ℂ (continuedOnset (physicalRate q branch)) u :=
    fun u hu => continuedOnset_analyticAt _ u (hfacts u (hsub hu)).2.2.1
  obtain ⟨KT, hKT⟩ := hcomp.exists_bound_of_continuousOn
    (fun u hu => (hTan u hu).continuousAt.continuousWithinAt)
  obtain ⟨b₄, C₄, hb₄, hb₄h, hlift⟩ := liftProfile_jet (physicalRate q branch) a w0 R hR0.le
    (continuedOnset (physicalRate q branch)) (K := max KT 0) (le_max_right _ _)
    (fun u hu => (hKT u hu).trans (le_max_left _ _))
  set b : ℝ := min b₁ b₄ with hb
  have hb0 : 0 < b := lt_min hb₁ hb₄
  have hbh : b ≤ 1 / 2 := (min_le_left _ _).trans hb₁h
  have hbb₁ : b ≤ b₁ := min_le_left _ _
  have hbb₄ : b ≤ b₄ := min_le_right _ _
  -- the identity
  have hid : ∀ u ∈ closedBall w0 R, ∀ z ∈ Ioc (0:ℝ) b,
      principalProfile q branch a i u z =
        (1 / reducedGreenClearingFactor u (principalFrequency q i) (physicalRate q branch)) *
          clearedResponseQuotient (physicalRate q branch) (principalFrequency q i) a
            (principalAmplitude q i) (principalGradient q branch i) u z -
        principalAmplitude q i *
          liftProfile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) u z := by
    intro u hu z hz
    have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1, by linarith [hz.2, hbh]⟩
    have ht : tortoiseOf z < 0 := tortoiseOf_neg hzI
    have hzt : horizonCoordinate (tortoiseOf z) = z := horizonCoordinate_tortoiseOf hzI
    have hz0 : (z:ℂ) ^ (u / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
    have hc := hcF u hu
    unfold principalProfile clearedResponseQuotient
    rw [continuedPrincipalDifference, continuedTortoiseGreen, hzt,
      radialLift_eq_profile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) u
        (tortoiseOf z) ht, hzt]
    field_simp
  have hjet' := (hjet.mono (fun u (hu : u ∈ closedBall w0 R) => ⟨hsub hu, hcne u hu⟩)).mono_radius hbb₁
  have hscaled := hjet'.const_mul (k := fun u =>
    1 / reducedGreenClearingFactor u (principalFrequency q i) (physicalRate q branch))
    (K := max Kinv 0) (fun u hu => (hKinv u hu).trans (le_max_left _ _))
  have hlift' := (hlift.mono_radius hbb₄).const_mul (k := fun _ => principalAmplitude q i)
    (K := ‖principalAmplitude q i‖) (fun _ _ => le_rfl)
  have hsum := ((hscaled.sub hlift').congr hid).congr_coeff
    (d₀ := principalJetZero q branch a i b₁) (d₁ := principalJetOne q branch a i b₁)
    (fun u hu => by
      simp only [principalJetZero]
      field_simp [hcF u hu])
    (fun u hu => by
      simp only [principalJetOne]
      field_simp [hcF u hu])
  -- analyticity
  have hanal : ∀ u ∈ closedBall w0 R, ∀ z ∈ Ioc (0:ℝ) b,
      AnalyticAt ℂ (fun v => principalProfile q branch a i v z) u := by
    intro u hu z hz
    have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1, by linarith [hz.2, hbh]⟩
    have ht : tortoiseOf z < 0 := tortoiseOf_neg hzI
    have hu' := hfacts u (hsub hu)
    unfold principalProfile
    apply AnalyticAt.div (continuedPrincipalDifference_analyticAt q branch u a hu'.1 hu'.2.1 i
      hu'.2.2.1 (hcne u hu) _ ht)
    · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        ((differentiable_id.div_const 2).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))))
        u (mem_univ _)
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
  have hw0ball : w0 ∈ closedBall w0 R := mem_closedBall_self hR0.le
  have hcF0 := hcFan w0 hw0ball
  have hcF0ne := hcF w0 hw0ball
  have hγ : AnalyticAt ℂ (fun u => horizonGaussFirstCoefficient u (principalFrequency q i)) w0 :=
    horizonGaussFirstCoefficient_analyticAt w0 (principalFrequency q i) hw
  have hS0 := horizonSlope_analyticAt (physicalRate q branch) (principalFrequency q i) a
    (principalAmplitude q i) (principalGradient q branch i) w0 hw hs
  have hT0 := hTan w0 hw0ball
  have hpow : AnalyticAt ℂ (fun u => (2:ℂ) ^ (2 * physicalRate q branch - u)) w0 :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_const _ |>.sub differentiable_id).const_cpow (Or.inl two_ne_zero))) w0
      (mem_univ _)
  have hc₀an : AnalyticAt ℂ (principalJetZero q branch a i b₁) w0 := by
    unfold principalJetZero
    exact (hE.div hcF0 hcF0ne).sub
      (analyticAt_const.mul (analyticAt_const.mul (hpow.mul (analyticAt_const.mul hT0))))
  have hc₁an : AnalyticAt ℂ (principalJetOne q branch a i b₁) w0 := by
    unfold principalJetOne
    refine (((hE.mul hγ).add (hcF0.mul hS0)).div hcF0 hcF0ne).sub
      (analyticAt_const.mul (analyticAt_const.mul ?_))
    exact ((hpow.mul (analyticAt_const.mul hT0)).mul analyticAt_const).add
      ((((analyticAt_const.sub analyticAt_id).neg.mul hpow).div analyticAt_const (by norm_num)).mul
        (analyticAt_const.mul hT0))
  exact ⟨R, b, b₁, _, hR0, hb0, hbh, hc₀an, hc₁an, hanal, hsum⟩

end
end RHTower.D4BMJointSource
