import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonCoordinateJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingHorizonExpansion
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedGreenNumerator
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonTaylorBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonGaussBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalOppositePairingRegularity

/-!
# Uniform horizon jet of the cleared self channel

The continued self response `continuedReducedGreen` carries the fundamental QNM pole through the
clearing factor `-(u-2s)·connection u χ`; its cleared numerator `clearedReducedGreen` is analytic
in the frequency.  In the horizon coordinate `z`, the cleared numerator divided by `z^{u/2}` is
`gauss(u,z)·(Ê(u) + cF(u)·P(u,z)) + connection(u)·liftProfile(u,z)` away from the QNM, where
`P` is the source primitive with its uniform quadratic bound, `Ê` the cleared endpoint coefficient,
and `liftProfile` the elementary lift.  All coefficient functions are analytic at the QNM, so the
cleared self profile has a uniform second-order horizon jet on a closed frequency ball including
the QNM itself.  This transfers the corpus's punctured expansion through the pole; it evaluates no
physical current.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric D4BMLaplaceRadial D4BMModularCore
  GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-! ## The inverse horizon coordinate -/

/-- Inverse of the horizon coordinate on the exterior. -/
def tortoiseOf (z : ℝ) : ℝ := Real.log (Real.sqrt z / (1 + Real.sqrt (1 - z)))

theorem tortoiseOf_neg {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) : tortoiseOf z < 0 := by
  unfold tortoiseOf
  apply Real.log_neg
  · exact div_pos (Real.sqrt_pos.mpr hz.1) (by positivity)
  · rw [div_lt_one (by positivity)]
    have h1 : Real.sqrt z < 1 := by
      rw [Real.sqrt_lt' (by norm_num)]
      linarith [hz.2]
    linarith [Real.sqrt_nonneg (1 - z)]

theorem tortoiseOf_horizonCoordinate {t : ℝ} (ht : t < 0) :
    tortoiseOf (horizonCoordinate t) = t := by
  unfold tortoiseOf
  rw [← radialUnit_eq_sqrt t ht, ← exp_eq_sqrt_div t, Real.log_exp]

theorem horizonCoordinate_tortoiseOf {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    horizonCoordinate (tortoiseOf z) = z := by
  have hs1 : Real.sqrt z ^ (2 : ℕ) = z := Real.sq_sqrt hz.1.le
  have hs2 : Real.sqrt (1 - z) ^ (2 : ℕ) = 1 - z := Real.sq_sqrt (by linarith [hz.2])
  have hs1p : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz.1
  have hs2p : 0 ≤ Real.sqrt (1 - z) := Real.sqrt_nonneg _
  have hr : 0 < Real.sqrt z / (1 + Real.sqrt (1 - z)) := by positivity
  have hcosh : Real.cosh (tortoiseOf z) = 1 / Real.sqrt z := by
    unfold tortoiseOf
    rw [Real.cosh_log hr]
    field_simp
    linear_combination hs1 + hs2
  rw [horizonCoordinate_eq_inv_cosh_sq, hcosh]
  field_simp
  exact hs1

theorem horizon_eq_pow_mul (u chi : ℂ) (z : ℝ) :
    horizon u chi z = (z:ℂ) ^ (u / 2) * gaussFactor u chi false (z:ℂ) := rfl

theorem radialLift_smul (s u a T c : ℂ) (t : ℝ) :
    radialLift s u a (c * T) t = c * radialLift s u a T t := by
  simp only [radialLift, sourceAmplitude]; ring

theorem liftProfile_smul (s a : ℂ) (T : ℂ → ℂ) (c : ℂ → ℂ) (u : ℂ) (z : ℝ) :
    liftProfile s a (fun v => c v * T v) u z = c u * liftProfile s a T u z := by
  simp only [liftProfile, amplitudeProfile]; ring

theorem clearingFactor_mul_continuedOnset (s u chi : ℂ) (hs : u - 2 * s ≠ 0) :
    reducedGreenClearingFactor u chi s * continuedOnset s u =
      -connection u chi * clearedOnset s u := by
  simp only [reducedGreenClearingFactor, continuedOnset, clearedOnset]
  field_simp

/-! ## The generic cleared response quotient -/

/-- The clearing-factor multiple of the continued response, divided by `z^{u/2}`. -/
def clearedResponseQuotient (s chi a J K : ℂ) (u : ℂ) (z : ℝ) : ℂ :=
  reducedGreenClearingFactor u chi s * continuedResponse s chi a J K z u / (z:ℂ) ^ (u / 2)

/-- The explicit source slope of the horizon expansion. -/
def horizonSlope (s _chi a J K : ℂ) (u : ℂ) : ℂ :=
  sourceRemainder s u a J K 1 0 * (1 / (u - 2 * s) + onsetCorrection (2 * s) u) / (2 * (u + 1))

/-- The cleared endpoint coefficient, analytic through the QNM. -/
def clearedEndpoint (s chi a J K : ℂ) (b : ℝ) (u : ℂ) : ℂ :=
  (u - 2 * s) * (oppositeEndpointPoleNumerator s chi a J K b u +
    connection u chi * incomingSourcePrimitive s chi a J K u b)

theorem horizonSlope_analyticAt (s chi a J K w : ℂ) (hw : w.im ≠ 0) (hs : w - 2 * s ≠ 0) :
    AnalyticAt ℂ (horizonSlope s chi a J K) w := by
  have h1 : w + 1 ≠ 0 := by
    intro h; apply hw; have := congrArg Complex.im h; simpa using this
  have hrem : AnalyticAt ℂ (fun u => sourceRemainder s u a J K 1 0) w := by
    have hd : Differentiable ℂ (fun u => sourceRemainder s u a J K 1 0) := by
      simp only [sourceRemainder, power]
      fun_prop (disch := norm_num)
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) w (mem_univ _)
  have honset : AnalyticAt ℂ (fun u => onsetCorrection (2 * s) u) w :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (onsetCorrection_entire (2 * s))) w
      (mem_univ _)
  unfold horizonSlope
  apply AnalyticAt.div
  · apply hrem.mul
    apply AnalyticAt.add _ honset
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs
  · exact analyticAt_const.mul (analyticAt_id.add analyticAt_const)
  · exact mul_ne_zero (by norm_num) h1

/-- Uniform data for the cleared response quotient near a nonreal frequency:
a radius, a horizon radius, and analytic jet coefficients, with the jet valid wherever the
connection coefficient is nonzero. -/
theorem clearedResponseQuotient_jet (s chi a J K w : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hs : w - 2 * s ≠ 0) :
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1 / 2 ∧
      (∀ u ∈ closedBall w R, u.im ≠ 0 ∧ -2 < u.re ∧ u - 2 * s ≠ 0 ∧ u + 1 ≠ 0) ∧
      (∀ u ∈ closedBall w R, ∀ z ∈ Ioc (0:ℝ) b,
        1 / 2 ≤ ‖gaussFactor u chi false (z:ℂ)‖ ∧ horizon u chi z ≠ 0) ∧
      AnalyticAt ℂ (clearedEndpoint s chi a J K b) w ∧
      HasUniformJet2 (closedBall w R \ {u | connection u chi = 0}) b
        (clearedResponseQuotient s chi a J K)
        (clearedEndpoint s chi a J K b)
        (fun u => clearedEndpoint s chi a J K b u * horizonGaussFirstCoefficient u chi +
          reducedGreenClearingFactor u chi s * horizonSlope s chi a J K u) C := by
  obtain ⟨R₁, b₁, C₁, M₁, hR₁, hb₁, hb₁h, hC₁, hM₁, hpkg⟩ :=
    incomingSourcePrimitive_common_data s chi a J K w hw hwr hs
  obtain ⟨R₂, C₂, L₂, hR₂, hC₂, hL₂, hg⟩ :=
    horizonGauss_uniform_second_bound w chi hw hb₁ (by linarith)
  obtain ⟨R₃, b₃, C₃, hR₃, hb₃, hb₃h, hC₃, hgn⟩ := horizonGauss_uniform_nonzero w chi hw
  set R : ℝ := min R₁ (min R₂ R₃) / 2 with hR
  have hR0 : 0 < R := by positivity
  have hRsub : ∀ u ∈ closedBall w R, u ∈ ball w R₁ ∧ u ∈ ball w R₂ ∧ u ∈ ball w R₃ := by
    intro u hu
    have h := mem_closedBall.mp hu
    have h1 : R < R₁ := by
      have := min_le_left R₁ (min R₂ R₃); rw [hR]; linarith
    have h2 : R < R₂ := by
      have := (min_le_right R₁ (min R₂ R₃)).trans (min_le_left R₂ R₃); rw [hR]; linarith
    have h3 : R < R₃ := by
      have := (min_le_right R₁ (min R₂ R₃)).trans (min_le_right R₂ R₃); rw [hR]; linarith
    exact ⟨mem_ball.mpr (by linarith), mem_ball.mpr (by linarith), mem_ball.mpr (by linarith)⟩
  set b : ℝ := min b₁ b₃ with hb
  have hb0 : 0 < b := lt_min hb₁ hb₃
  have hbh : b ≤ 1 / 2 := (min_le_left _ _).trans hb₁h
  have hbb₁ : b ≤ b₁ := min_le_left _ _
  have hbb₃ : b ≤ b₃ := min_le_right _ _
  have hb1 : b < 1 := by linarith
  have hfacts : ∀ u ∈ closedBall w R, u.im ≠ 0 ∧ -2 < u.re ∧ u - 2 * s ≠ 0 ∧ u + 1 ≠ 0 := by
    intro u hu
    obtain ⟨hui, hur, hus, -⟩ := hpkg u (hRsub u hu).1
    refine ⟨hui, hur, hus, ?_⟩
    intro h; apply hui; have := congrArg Complex.im h; simpa using this
  have hgauss : ∀ u ∈ closedBall w R, ∀ z ∈ Ioc (0:ℝ) b,
      1 / 2 ≤ ‖gaussFactor u chi false (z:ℂ)‖ ∧ horizon u chi z ≠ 0 := by
    intro u hu z hz
    have h := (hgn u (hRsub u hu).2.2 z ⟨hz.1.le, hz.2.trans hbb₃⟩).2.1
    refine ⟨h, ?_⟩
    rw [horizon_eq_pow_mul]
    apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
    · intro h0; rw [h0, norm_zero] at h; linarith
  -- analytic pieces
  have hEan : ∀ u ∈ closedBall w R, AnalyticAt ℂ (clearedEndpoint s chi a J K b) u := by
    intro u hu
    have hu' := hfacts u hu
    have hhor' : horizon u chi b ≠ 0 := (hgauss u hu b ⟨hb0, le_rfl⟩).2
    have hOpp' := oppositeEndpointPoleNumerator_analyticAt s chi a J K u hu'.1 hu'.2.1 hu'.2.2.1
      ⟨hb0, hb1⟩ hhor'
    have hP' := ((hpkg u (hRsub u hu).1).2.2.2.2 b ⟨hb0, hbb₁⟩).1
    have hconn' := connection_frequency_analyticAt u chi hu'.1
    unfold clearedEndpoint
    exact (analyticAt_id.sub analyticAt_const).mul (hOpp'.add (hconn'.mul hP'))
  have hw0ball : w ∈ closedBall w R := mem_closedBall_self hR0.le
  have hE : AnalyticAt ℂ (clearedEndpoint s chi a J K b) w := hEan w hw0ball
  have hcFan : ∀ u ∈ closedBall w R, AnalyticAt ℂ (fun v => reducedGreenClearingFactor v chi s) u := by
    intro u hu
    unfold reducedGreenClearingFactor
    exact (analyticAt_id.sub analyticAt_const).neg.mul (connection_frequency_analyticAt u chi (hfacts u hu).1)
  have hSan : ∀ u ∈ closedBall w R, AnalyticAt ℂ
      (fun v => reducedGreenClearingFactor v chi s * horizonSlope s chi a J K v) u := fun u hu =>
    (hcFan u hu).mul (horizonSlope_analyticAt s chi a J K u (hfacts u hu).1 (hfacts u hu).2.2.1)
  -- compactness bounds
  have hcomp : IsCompact (closedBall w R) := isCompact_closedBall w R
  obtain ⟨KF, hKF⟩ := hcomp.exists_bound_of_continuousOn
    (fun u hu => (hcFan u hu).continuousAt.continuousWithinAt)
  obtain ⟨KE, hKE⟩ := hcomp.exists_bound_of_continuousOn
    (fun u hu => (hEan u hu).continuousAt.continuousWithinAt)
  obtain ⟨KS, hKS⟩ := hcomp.exists_bound_of_continuousOn
    (fun u hu => (hSan u hu).continuousAt.continuousWithinAt)
  set KF' := max KF 0 with hKF'
  have hKF'0 : 0 ≤ KF' := le_max_right _ _
  have hKFb : ∀ u ∈ closedBall w R, ‖reducedGreenClearingFactor u chi s‖ ≤ KF' :=
    fun u hu => (hKF u hu).trans (le_max_left _ _)
  set M : ℝ := max (max 1 L₂) (max (max KE 0) (max KS 0)) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (le_max_of_le_left zero_le_one)
  -- the two jets
  have hgjet : HasUniformJet2 (closedBall w R) b (fun u z => gaussFactor u chi false (z:ℂ))
      (fun _ => 1) (fun u => horizonGaussFirstCoefficient u chi) C₂ := by
    intro u hu z hz
    exact (hg u (hRsub u hu).2.1).2 z ⟨hz.1.le, hz.2.trans hbb₁⟩
  have hG2 : HasUniformJet2 (closedBall w R) b
      (fun u z => clearedEndpoint s chi a J K b u +
        reducedGreenClearingFactor u chi s * incomingSourcePrimitive s chi a J K u z)
      (clearedEndpoint s chi a J K b)
      (fun u => reducedGreenClearingFactor u chi s * horizonSlope s chi a J K u) (KF' * C₁) := by
    intro u hu z hz
    have hq := ((hpkg u (hRsub u hu).1).2.2.2.2 z ⟨hz.1, hz.2.trans hbb₁⟩).2.2.1
    have hkey : clearedEndpoint s chi a J K b u +
        reducedGreenClearingFactor u chi s * incomingSourcePrimitive s chi a J K u z -
        clearedEndpoint s chi a J K b u -
        reducedGreenClearingFactor u chi s * horizonSlope s chi a J K u * (z:ℂ) =
        reducedGreenClearingFactor u chi s *
          (incomingSourcePrimitive s chi a J K u z - horizonSlope s chi a J K u * (z:ℂ)) := by
      ring
    rw [hkey, norm_mul]
    unfold horizonSlope
    calc ‖reducedGreenClearingFactor u chi s‖ *
          ‖incomingSourcePrimitive s chi a J K u z -
            sourceRemainder s u a J K 1 0 * (1 / (u - 2 * s) + onsetCorrection (2 * s) u) /
              (2 * (u + 1)) * (z:ℂ)‖
        ≤ KF' * (C₁ * z ^ (2 : ℕ)) := mul_le_mul (hKFb u hu) hq (norm_nonneg _) hKF'0
      _ = KF' * C₁ * z ^ (2 : ℕ) := by ring
  have hprod := hgjet.mul (by linarith) hG2 hC₂ (mul_nonneg hKF'0 hC₁) hM0
    (fun _ _ => by simp; exact le_max_of_le_left (le_max_left _ _))
    (fun u hu => ((hg u (hRsub u hu).2.1).1).trans (le_max_of_le_left (le_max_right _ _)))
    (fun u hu => (hKE u hu).trans (le_max_of_le_right (le_max_of_le_left (le_max_left _ _))))
    (fun u hu => (hKS u hu).trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  -- the identity on the connection-nonzero part
  have hid : ∀ u ∈ closedBall w R \ {u | connection u chi = 0}, ∀ z ∈ Ioc (0:ℝ) b,
      clearedResponseQuotient s chi a J K u z =
        gaussFactor u chi false (z:ℂ) * (clearedEndpoint s chi a J K b u +
          reducedGreenClearingFactor u chi s * incomingSourcePrimitive s chi a J K u z) := by
    intro u hu z hz
    have hc : connection u chi ≠ 0 := fun h => hu.2 h
    have hpk := (hpkg u (hRsub u hu.1).1).2.2.2.2
    have hidz := (hpk z ⟨hz.1, hz.2.trans hbb₁⟩).2.2.2 hc
    have hidb := (hpk b ⟨hb0, hbb₁⟩).2.2.2 hc
    have hhz := (hgauss u hu.1 z hz).2
    have hhb := (hgauss u hu.1 b ⟨hb0, le_rfl⟩).2
    have hEb : incomingResponseEndpoint s chi a J K u b₁ = incomingResponseEndpoint s chi a J K u b := by
      have h1 : incomingResponseEndpoint s chi a J K u b =
          continuedResponse s chi a J K b u / horizon u chi b - incomingSourcePrimitive s chi a J K u b := rfl
      rw [h1, hidb]; ring
    have hcE : reducedGreenClearingFactor u chi s * incomingResponseEndpoint s chi a J K u b₁ =
        clearedEndpoint s chi a J K b u := by
      rw [hEb, reducedGreenClearingFactor, clearedEndpoint,
        show -(u - 2 * s) * connection u chi * incomingResponseEndpoint s chi a J K u b =
          -(u - 2 * s) * (connection u chi * incomingResponseEndpoint s chi a J K u b) by ring,
        connection_mul_incomingEndpoint_eq s chi a J K u b hc hhb]
      ring
    have hresp : continuedResponse s chi a J K z u = horizon u chi z *
        (incomingResponseEndpoint s chi a J K u b₁ + incomingSourcePrimitive s chi a J K u z) := by
      rw [← hidz]; field_simp
    have hz0 : (z:ℂ) ^ (u / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
    unfold clearedResponseQuotient
    rw [hresp, horizon_eq_pow_mul, ← hcE]
    field_simp
  refine ⟨R, b, M ^ (2 : ℕ) + C₂ * (2 * M + KF' * C₁) + 2 * M * (KF' * C₁), hR0, hb0, hbh, hfacts,
    hgauss, hE, ?_⟩
  exact ((hprod.mono sdiff_subset).congr hid).congr_coeff (fun u _ => by ring) (fun u _ => by ring)

/-! ## The self channel -/

/-- The cleared self response in the horizon coordinate, divided by `z^{u/2}`. -/
def selfClearedProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ) (z : ℝ) : ℂ :=
  clearedReducedGreen u (physicalRadialFrequency q) (physicalRate q branch) a (tortoiseOf z) /
    (z:ℂ) ^ (u / 2)

theorem liftProfile_congr_value (s a : ℂ) (T T' : ℂ → ℂ) (u : ℂ) (z : ℝ) (h : T u = T' u) :
    liftProfile s a T u z = liftProfile s a T' u z := by
  simp only [liftProfile, amplitudeProfile, h]

/-- Constant jet coefficient of the cleared self profile. -/
def selfJetZero (q : XiZeroCopy) (branch : Bool) (a : ℂ) (b : ℝ) (u : ℂ) : ℂ :=
  clearedEndpoint (physicalRate q branch) (physicalRadialFrequency q) a 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) b u +
    connection u (physicalRadialFrequency q) *
      ((-physicalRate q branch * (physicalRate q branch - 1) / 4) *
        ((2:ℂ) ^ (2 * physicalRate q branch - u) * (a ^ (2 : ℕ) * clearedOnset (physicalRate q branch) u)))

/-- Linear jet coefficient of the cleared self profile. -/
def selfJetOne (q : XiZeroCopy) (branch : Bool) (a : ℂ) (b : ℝ) (u : ℂ) : ℂ :=
  (clearedEndpoint (physicalRate q branch) (physicalRadialFrequency q) a 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) b u *
      horizonGaussFirstCoefficient u (physicalRadialFrequency q) +
    reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
      horizonSlope (physicalRate q branch) (physicalRadialFrequency q) a 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) u) +
  connection u (physicalRadialFrequency q) *
    ((-physicalRate q branch * (physicalRate q branch - 1) / 4) *
      ((2:ℂ) ^ (2 * physicalRate q branch - u) * (a ^ (2 : ℕ) * clearedOnset (physicalRate q branch) u) *
          (-3 / 2) +
        -(2 * physicalRate q branch - u) * (2:ℂ) ^ (2 * physicalRate q branch - u) / 4 *
          (a ^ (2 : ℕ) * clearedOnset (physicalRate q branch) u)))

/-- The cleared self profile has a uniform second-order horizon jet on a closed frequency ball
around the fundamental QNM, with coefficients analytic at the QNM, and is analytic in the
frequency at every point of that ball for every positive horizon coordinate. -/
theorem selfClearedProfile_jet (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    ∃ R b bE C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1 / 2 ∧
      AnalyticAt ℂ (selfJetZero q branch a bE) (physicalFundamentalFrequency q side) ∧
      AnalyticAt ℂ (selfJetOne q branch a bE) (physicalFundamentalFrequency q side) ∧
      (∀ u ∈ closedBall (physicalFundamentalFrequency q side) R, ∀ z ∈ Ioc (0:ℝ) b,
        AnalyticAt ℂ (fun v => selfClearedProfile q branch a v z) u) ∧
      HasUniformJet2 (closedBall (physicalFundamentalFrequency q side) R) b
        (selfClearedProfile q branch a) (selfJetZero q branch a bE) (selfJetOne q branch a bE) C := by
  set w0 := physicalFundamentalFrequency q side with hw0
  have hw : w0.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hwr : -2 < w0.re := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  have hs : w0 - 2 * physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨R₁, b₁, C₁, hR₁, hb₁, hb₁h, hfacts, hgauss, hE, hjet⟩ :=
    clearedResponseQuotient_jet (physicalRate q branch) (physicalRadialFrequency q) a 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) w0 hw hwr hs
  obtain ⟨R₄, hR₄, hconnne⟩ :=
    Metric.mem_nhdsWithin_iff.mp (connection_eventually_ne_zero w0 (physicalRadialFrequency q) hw)
  have hcomp₁ : IsCompact (closedBall w0 R₁) := isCompact_closedBall w0 R₁
  obtain ⟨KT, hKT⟩ := hcomp₁.exists_bound_of_continuousOn
    (clearedOnset_entire (physicalRate q branch)).continuous.continuousOn
  obtain ⟨b₄, C₄, hb₄, hb₄h, hlift⟩ := liftProfile_jet (physicalRate q branch) a w0 R₁ hR₁.le
    (clearedOnset (physicalRate q branch)) (K := max KT 0) (le_max_right _ _)
    (fun u hu => (hKT u hu).trans (le_max_left _ _))
  obtain ⟨Kc, hKc⟩ := hcomp₁.exists_bound_of_continuousOn
    (fun u hu => (connection_frequency_analyticAt u (physicalRadialFrequency q)
      (hfacts u hu).1).continuousAt.continuousWithinAt)
  set R : ℝ := min R₁ R₄ / 2 with hR
  have hR0 : 0 < R := by positivity
  have hRR₁ : R ≤ R₁ := by
    have := min_le_left R₁ R₄; rw [hR]; linarith
  have hRR₄ : R < R₄ := by
    have := min_le_right R₁ R₄; rw [hR]; linarith
  have hsub : closedBall w0 R ⊆ closedBall w0 R₁ := closedBall_subset_closedBall hRR₁
  set b : ℝ := min b₁ b₄ with hb
  have hb0 : 0 < b := lt_min hb₁ hb₄
  have hbh : b ≤ 1 / 2 := (min_le_left _ _).trans hb₁h
  have hbb₁ : b ≤ b₁ := min_le_left _ _
  have hbb₄ : b ≤ b₄ := min_le_right _ _
  have hcne : ∀ u ∈ closedBall w0 R \ {w0}, connection u (physicalRadialFrequency q) ≠ 0 := by
    intro u hu
    apply hconnne
    refine ⟨mem_ball.mpr ?_, hu.2⟩
    have := mem_closedBall.mp hu.1
    linarith
  -- the identity on the punctured ball
  have hid : ∀ u ∈ closedBall w0 R \ {w0}, ∀ z ∈ Ioc (0:ℝ) b,
      selfClearedProfile q branch a u z =
        clearedResponseQuotient (physicalRate q branch) (physicalRadialFrequency q) a 1
            (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) u z +
          connection u (physicalRadialFrequency q) *
            liftProfile (physicalRate q branch) a (clearedOnset (physicalRate q branch)) u z := by
    intro u hu z hz
    have hc := hcne u hu
    have hs' : u - 2 * physicalRate q branch ≠ 0 := (hfacts u (hsub hu.1)).2.2.1
    have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1, by linarith [hz.2, hbh]⟩
    have ht : tortoiseOf z < 0 := tortoiseOf_neg hzI
    have hzt : horizonCoordinate (tortoiseOf z) = z := horizonCoordinate_tortoiseOf hzI
    have hz0 : (z:ℂ) ^ (u / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
    have hlp : reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
        liftProfile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) u z =
        -connection u (physicalRadialFrequency q) *
          liftProfile (physicalRate q branch) a (clearedOnset (physicalRate q branch)) u z := by
      rw [← liftProfile_smul (physicalRate q branch) a (continuedOnset (physicalRate q branch))
        (fun v => reducedGreenClearingFactor v (physicalRadialFrequency q) (physicalRate q branch)),
        ← liftProfile_smul (physicalRate q branch) a (clearedOnset (physicalRate q branch))
        (fun v => -connection v (physicalRadialFrequency q))]
      exact liftProfile_congr_value _ a _ _ u z
        (clearingFactor_mul_continuedOnset (physicalRate q branch) u (physicalRadialFrequency q) hs')
    unfold selfClearedProfile clearedResponseQuotient
    rw [clearedReducedGreen_eq u (physicalRadialFrequency q) (physicalRate q branch) a hs' hc,
      continuedReducedGreen, continuedTortoiseGreen, hzt,
      radialLift_eq_profile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) u
        (tortoiseOf z) ht, hzt]
    rw [div_add' _ _ _ hz0]
    congr 1
    linear_combination (-(z:ℂ) ^ (u / 2)) * hlp
  -- jets on the punctured ball
  have hjet' := (hjet.mono (fun u (hu : u ∈ closedBall w0 R \ {w0}) =>
    ⟨hsub hu.1, fun h => hcne u hu h⟩)).mono_radius hbb₁
  have hlift' := ((hlift.mono (fun u (hu : u ∈ closedBall w0 R \ {w0}) => hsub hu.1)).mono_radius
    hbb₄).const_mul (k := fun u => connection u (physicalRadialFrequency q)) (K := max Kc 0)
    (fun u hu => (hKc u (hsub hu.1)).trans (le_max_left _ _))
  have hsum := ((hjet'.add hlift').congr hid).congr_coeff
    (d₀ := selfJetZero q branch a b₁) (d₁ := selfJetOne q branch a b₁)
    (fun u _ => by simp only [selfJetZero]; try ring) (fun u _ => by simp only [selfJetOne]; try ring)
  -- analyticity in the frequency
  have hanal : ∀ u ∈ closedBall w0 R, ∀ z ∈ Ioc (0:ℝ) b,
      AnalyticAt ℂ (fun v => selfClearedProfile q branch a v z) u := by
    intro u hu z hz
    have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1, by linarith [hz.2, hbh]⟩
    have ht : tortoiseOf z < 0 := tortoiseOf_neg hzI
    have hu' := hfacts u (hsub hu)
    unfold selfClearedProfile
    apply AnalyticAt.div (clearedReducedGreen_analyticAt u (physicalRadialFrequency q)
      (physicalRate q branch) a hu'.1 hu'.2.1 _ ht)
    · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        ((differentiable_id.div_const 2).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))))
        u (mem_univ _)
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
  have hconn0 : AnalyticAt ℂ (fun u => connection u (physicalRadialFrequency q)) w0 :=
    connection_frequency_analyticAt w0 (physicalRadialFrequency q) hw
  have hcF0 : AnalyticAt ℂ
      (fun u => reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)) w0 := by
    unfold reducedGreenClearingFactor
    exact (analyticAt_id.sub analyticAt_const).neg.mul hconn0
  have hγ : AnalyticAt ℂ (fun u => horizonGaussFirstCoefficient u (physicalRadialFrequency q)) w0 :=
    horizonGaussFirstCoefficient_analyticAt w0 (physicalRadialFrequency q) hw
  have hS0 := horizonSlope_analyticAt (physicalRate q branch) (physicalRadialFrequency q) a 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) w0 hw hs
  have hT0 : AnalyticAt ℂ (clearedOnset (physicalRate q branch)) w0 :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (clearedOnset_entire _)) w0 (mem_univ _)
  have hpow : AnalyticAt ℂ (fun u => (2:ℂ) ^ (2 * physicalRate q branch - u)) w0 :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_const _ |>.sub differentiable_id).const_cpow (Or.inl two_ne_zero))) w0
      (mem_univ _)
  have hc₀an : AnalyticAt ℂ (selfJetZero q branch a b₁) w0 := by
    unfold selfJetZero
    exact hE.add (hconn0.mul (analyticAt_const.mul (hpow.mul (analyticAt_const.mul hT0))))
  have hc₁an : AnalyticAt ℂ (selfJetOne q branch a b₁) w0 := by
    unfold selfJetOne
    refine ((hE.mul hγ).add (hcF0.mul hS0)).add (hconn0.mul (analyticAt_const.mul ?_))
    exact ((hpow.mul (analyticAt_const.mul hT0)).mul analyticAt_const).add
      ((((analyticAt_const.sub analyticAt_id).neg.mul hpow).div analyticAt_const (by norm_num)).mul
        (analyticAt_const.mul hT0))
  have hfinal := hsum.closedBall_of_punctured hR0
    (fun z hz => (hanal w0 (mem_closedBall_self hR0.le) z hz).continuousAt)
    hc₀an.continuousAt hc₁an.continuousAt
  exact ⟨R, b, b₁, _, hR0, hb0, hbh, hc₀an, hc₁an, hanal, hfinal⟩

end
end RHTower.D4BMJointSource
