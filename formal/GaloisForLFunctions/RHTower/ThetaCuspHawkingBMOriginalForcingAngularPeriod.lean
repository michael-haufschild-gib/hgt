import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalTemporalCorner
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCircleFlux

/-!
# Original forcing and its angular finite part

The literal forcing splits exactly into the full square source and its angular Green defect.
The three original principal counterterms obey the same decomposition. The existing square
period and original normal-flux identity therefore determine the forcing period at every radius.

Retaining the actual onset and normalizable radial reader gives every damped temporal moment
one joint ingoing-time, horizon and angular-cutoff limit. This is a source-contact identity;
the complete metric current, its static-time corner and QNM continuation remain separate.
-/
open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry ScalarTwoJet
namespace RHTower.D4BMOriginalForcingAngularPeriod
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalCornerForcing
open D4BMOriginalScalarRestoration D4BMOriginalCircleFlux D4BMOriginalCircleGreen
open D4BMAngularSeries D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev Point := Fin 2 → ℝ

def angularDefect (q : XiZeroCopy) (z : Point) : ℂ :=
  D4BMHorizon.scalarLaplacian (fullSquarePotential q) z-
    (physicalAngularParameter q^2-1/4)*fullSquarePotential q z

private theorem circle_zero (q : XiZeroCopy) (z : Point) (hz : 0<z 1) :
    circleField q 0 z=fullSquarePotential q z := by
  have he : (![z 0,z 1] : Point)=z := by ext i;fin_cases i <;> rfl
  simp only [circleField,D4BMNativeCircle.mean_zero,Real.exp_log hz,he]

private theorem jet_congr {f g : Point → ℂ} {z : Point} (h : f=ᶠ[𝓝 z] g) (i : Fin 2) :
    coordDeriv i f=ᶠ[𝓝 z] coordDeriv i g := by
  filter_upwards [h.fderiv (𝕜:=ℝ)] with v hv
  exact congrArg (fun A : Point →L[ℝ] ℂ => A (Pi.single i 1)) hv

private theorem circle_defect_zero (q : XiZeroCopy) (z : Point) (hz : 0<z 1) :
    scalarEquationDefect q 0 z=angularDefect q z := by
  have h : circleField q 0=ᶠ[𝓝 z] fullSquarePotential q := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
    exact circle_zero q v hv
  have h0 := (jet_congr (jet_congr h 0) 0).eq_of_nhds
  have h1 := (jet_congr (jet_congr h 1) 1).eq_of_nhds
  rw [scalarEquationDefect,angularDefect,circle_zero q z hz,
    D4BMHorizon.scalarLaplacian_eq _ z hz,D4BMHorizon.scalarLaplacian_eq _ z hz]
  simp only [h0,h1]

private theorem coordinates_continuous : Continuous (coordinates : UpperHalfPlane → Point) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

private theorem square_continuous (q : XiZeroCopy) :
    Continuous (fun z : UpperHalfPlane => fullSquarePotential q (coordinates z)) := by
  exact continuous_iff_continuousAt.mpr (fun z =>
    (fullSquarePotential_smooth q _ z.im_pos 0).continuousAt.comp coordinates_continuous.continuousAt)

private theorem defect_continuous (q : XiZeroCopy) :
    Continuous (fun z : UpperHalfPlane => angularDefect q (coordinates z)) := by
  have he (z : UpperHalfPlane) : angularDefect q (coordinates z)=
      (2*(physicalRate q false+1)*(physicalRate q false+2)-(physicalAngularParameter q^2-1/4))*
        fullSquarePotential q (coordinates z)+fullGradientEnergy q (coordinates z) := by
    rw [angularDefect,fullSquarePotential_laplacian q false _ z.im_pos]
    ring
  simp_rw [he]
  apply ((square_continuous q).const_mul _).add
  exact continuous_iff_continuousAt.mpr (fun z =>
    (fullGradientEnergy_smooth q _ z.im_pos).continuousAt.comp coordinates_continuous.continuousAt)

private theorem reader_continuous (q : XiZeroCopy) :
    Continuous (fun z : UpperHalfPlane => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)) := by
  exact continuous_iff_continuousAt.mpr (fun z =>
    (cuspLeg_contDiffAt .scalar (physicalAngularParameter q) 0 _ z.im_pos).continuousAt.comp
      coordinates_continuous.continuousAt)

private theorem reader_global (q : XiZeroCopy) :
    D4BMGlobalAngularResponse.scalar (physicalAngularParameter q)=
      D4BMLiteralCusp.scalar (physicalAngularParameter q) := rfl

/-- Actual scalar Green defect with its derived principal normal-flux counterterm. -/
def greenCut (q : XiZeroCopy) (Y : ℝ) : ℂ :=
  truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
    angularDefect q (coordinates z)) Y-
  principalCounterterm q (fun i => physicalAngularGap q q i*principalAmplitude q i) Y

/-- The whole angular Green defect, including the curved modular core, has zero finite part. -/
theorem original_green_finitePart (q : XiZeroCopy) :
    Tendsto (fun k : ℝ => greenCut q (Real.exp k)) atTop (𝓝 0) := by
  have h := original_angular_measure_green_finitePart q ⟨0,by norm_num⟩ 0
  have hc (i : Fin 3) : D4BMOriginalCirclePeriod.coefficient q 0 i=principalAmplitude q i := by
    simp only [D4BMOriginalCirclePeriod.coefficient,D4BMNativeCircle.powerCircle_eq_legendre,
      Real.cosh_zero,D4BMCausalKernel.legendreKernel_one,mul_one]
  have he (z : UpperHalfPlane) : scalarEquationDefect q 0 ![z.re,z.im]=
      angularDefect q (coordinates z) := circle_defect_zero q _ z.im_pos
  simpa only [zero_mul,Complex.exp_zero,one_mul,he,hc,greenCut,coordinates] using h

/-- Coefficient of the actual angular Green defect at every original compact radius. -/
def profileDefectCoefficient (s amp : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)^3*power (2*s) (1+u)*amp^2*s*(s-1)/4

private theorem profile (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u : ℝ)
    (z : Point) (hz : 0<z 1) :
    forcingProfile (physicalRate q br) amp (fullSquarePotential q z) (fullGradientEnergy q z/2) u =
      forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) u*fullSquarePotential q z+
      profileDefectCoefficient (physicalRate q br) amp u*angularDefect q z := by
  rw [angularDefect,fullSquarePotential_laplacian q br z hz]
  unfold reducedGreenGradient
  rw [physicalRadialFrequency_parameter]
  unfold forcingProfile profileDefectCoefficient
  ring

/-- All three principal coefficients of the actual unprojected forcing profile. -/
def profilePrincipal (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u : ℝ) (i : Fin 3) : ℂ :=
  forcingProfile (physicalRate q br) amp (principalAmplitude q i)
    ((principalExponent q i*(principalExponent q i-1)/2-
      (physicalRate q br+1)*(physicalRate q br+2))*principalAmplitude q i) u

private theorem profilePrincipal_decomposition (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u : ℝ) (i : Fin 3) :
    profilePrincipal q br amp u i =
      forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) u*principalAmplitude q i+
      profileDefectCoefficient (physicalRate q br) amp u*(physicalAngularGap q q i*principalAmplitude q i) := by
  unfold profilePrincipal reducedGreenGradient
  rw [physicalRadialFrequency_parameter,physicalAngularGap_self_indicial,physicalAngularParameter_eq]
  unfold forcingProfile profileDefectCoefficient
  ring

/-- The original forcing profile paired against the unchanged physical scalar reader,
with exactly its three angular principal powers subtracted. -/
def profileCut (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u Y : ℝ) : ℂ :=
  truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
    forcingProfile (physicalRate q br) amp (fullSquarePotential q (coordinates z))
      (fullGradientEnergy q (coordinates z)/2) u) Y-
  principalCounterterm q (profilePrincipal q br amp u) Y

/-- Exact finite-height decomposition; the full normal-flux defect is retained. -/
theorem original_profile_cut_decomposition (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u Y : ℝ) :
    profileCut q br amp u Y =
      forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) u*
          (truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
            fullSquarePotential q (coordinates z)) Y-principalCounterterm q (principalAmplitude q) Y)+
      profileDefectCoefficient (physicalRate q br) amp u*greenCut q Y := by
  have hS := truncated_integrable _ ((reader_continuous q).mul (square_continuous q)) Y
  have hD := truncated_integrable _ ((reader_continuous q).mul (defect_continuous q)) Y
  simp only [Pi.mul_def] at hS hD
  let a := forcingProfile (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) u
  let b := profileDefectCoefficient (physicalRate q br) amp u
  have hi : truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
      forcingProfile (physicalRate q br) amp (fullSquarePotential q (coordinates z))
        (fullGradientEnergy q (coordinates z)/2) u) Y =
      a*truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
        fullSquarePotential q (coordinates z)) Y+
      b*truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
        angularDefect q (coordinates z)) Y := by
    unfold truncatedIntegral
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hS.const_mul a) (hD.const_mul b)]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp only;rw [profile q br amp u _ z.im_pos];dsimp [a,b];ring)
  have hc : principalCounterterm q (profilePrincipal q br amp u) Y=
      a*principalCounterterm q (principalAmplitude q) Y+
      b*principalCounterterm q (fun i => physicalAngularGap q q i*principalAmplitude q i) Y := by
    unfold principalCounterterm
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [profilePrincipal_decomposition]
    dsimp [a,b]
    ring
  rw [profileCut,hi,hc,greenCut]
  dsimp [a,b]
  ring

/-- The full angular forcing profile has exactly the Green source coefficient at every radius. -/
theorem original_profile_finitePart (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u : ℝ) :
    Tendsto (fun k : ℝ => profileCut q br amp u (Real.exp k)) atTop
      (𝓝 (physicalSelfSourceCoefficient q*forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) u)) := by
  simp_rw [original_profile_cut_decomposition]
  have h := ((original_square_finitePart q).comp Real.tendsto_exp_atTop).const_mul
    (forcingProfile (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) u)
  have hD := (original_green_finitePart q).const_mul (profileDefectCoefficient (physicalRate q br) amp u)
  have ht := h.add hD
  simp only [Function.comp_def,mul_zero,add_zero,reader_global] at ht
  rwa [mul_comm (forcingProfile (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) u)
    (physicalSelfSourceCoefficient q)] at ht


/-- Literal angular cutoff of the original forcing divided by its geometric horizon factor. -/
def normalizedCut (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L p Y : ℝ) : ℂ :=
  truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
    (timeOriginalForcing q br amp (p+L/2) (-L/2) (coordinates z)/(horizonCoordinate (-L/2):ℂ))) Y-
  timeOnset (2*physicalRate q br) p*
    principalCounterterm q (profilePrincipal q br amp (radialUnit (-L/2))) Y

/-- The literal causal onset factors out of the original angular integral and its counterterm. -/
theorem original_normalized_cut (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    {L : ℝ} (hL : 0<L) (p Y : ℝ) :
    normalizedCut q br amp L p Y = timeOnset (2*physicalRate q br) p*
      profileCut q br amp (radialUnit (-L/2)) Y := by
  unfold normalizedCut profileCut truncatedIntegral
  rw [mul_sub,← integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by dsimp only;rw [original_full_forcing_normalized q br amp hL];ring)

private theorem onset_bound (s : ℂ) (p : ℝ) :
    ‖timeOnset (2*s) p‖ ≤ Real.exp ((2*s).re*p) := by
  have hc : ‖(Real.smoothTransition p:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg p)]
      using Real.smoothTransition.le_one p
  simp only [timeOnset,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) hc

private theorem onset_moment_integrable (s w : ℂ) (n : ℕ) (hw : (2*s).re<w.re) :
    IntegrableOn (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*timeOnset (2*s) p) (Ioi 0) := by
  have hn : (-1:ℝ)<(n:ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have hm := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) hn (by norm_num) (sub_pos.mpr hw)
  have hi : IntegrableOn (fun p : ℝ => p^n*Real.exp (-(w.re-(2*s).re)*p)) (Ioi 0) := by
    simpa only [Real.rpow_one,Real.rpow_natCast] using hm
  apply hi.mono' (by unfold timeOnset;fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  change ‖(p:ℂ)^n*Complex.exp (-w*(p:ℂ))*timeOnset (2*s) p‖ ≤ _
  have he : ‖Complex.exp (-w*(p:ℂ))‖=Real.exp (-w.re*p) := by rw [Complex.norm_exp];congr 1;simp
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp.le,he]
  calc
    _ ≤ (p^n*Real.exp (-w.re*p))*Real.exp ((2*s).re*p) :=
      mul_le_mul_of_nonneg_left (onset_bound s p)
        (mul_nonneg (pow_nonneg hp.le n) (Real.exp_nonneg _))
    _ = _ := by rw [mul_assoc,← Real.exp_add];congr 2;ring

/-- Every original regularized forcing time moment is admitted at finite radius and angular cutoff. -/
theorem original_normalized_moment_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (n : ℕ) (hw : (2*physicalRate q br).re<w.re) {L : ℝ} (hL : 0<L) (Y : ℝ) :
    IntegrableOn (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*normalizedCut q br amp L p Y) (Ioi 0) := by
  apply ((onset_moment_integrable (physicalRate q br) w n hw).mul_const
    (profileCut q br amp (radialUnit (-L/2)) Y)).congr
  exact ae_of_all _ (fun p => by dsimp only;rw [original_normalized_cut q br amp hL];ring)

private def onsetMoment (s w : ℂ) (n : ℕ) : ℂ :=
  ∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*timeOnset (2*s) p

private theorem normalized_moment_eq (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (n : ℕ) {L : ℝ} (hL : 0<L) (Y : ℝ) :
    (∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*normalizedCut q br amp L p Y)=
      profileCut q br amp (radialUnit (-L/2)) Y*onsetMoment (physicalRate q br) w n := by
  rw [onsetMoment,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by dsimp only;rw [original_normalized_cut q br amp hL];ring)

private theorem unit_collar_limit :
    Tendsto (fun L : ℝ => radialUnit (-L/2)) atTop (𝓝 (1:ℝ)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hform (L : ℝ) : radialUnit (-L/2)=(1-Real.exp (-L))/(1+Real.exp (-L)) := by
    apply (eq_div_iff (ne_of_gt (by positivity : 0<1+Real.exp (-L)))).mpr
    have h := radialUnit_one_sub (-L/2)
    rw [show 2*(-L/2) = -L by ring] at h
    nlinarith
  simp_rw [hform]
  simpa only [Pi.div_def,sub_zero,add_zero,div_one] using
    ((tendsto_const_nhds (x:=(1:ℝ))).sub he).div
      ((tendsto_const_nhds (x:=(1:ℝ))).add he) (by norm_num : (1:ℝ)+0≠0)

private theorem profile_continuous (s amp J K : ℂ) : ContinuousAt (forcingProfile s amp J K) 1 := by
  have hp := (power_derivatives (2*s) (by norm_num : 0<1+(1:ℝ))).1.continuousAt.comp
    (continuous_const.add continuous_id).continuousAt
  unfold forcingProfile
  fun_prop

private theorem defect_coefficient_continuous (s amp : ℂ) :
    ContinuousAt (profileDefectCoefficient s amp) 1 := by
  have hp := (power_derivatives (2*s) (by norm_num : 0<1+(1:ℝ))).1.continuousAt.comp
    (continuous_const.add continuous_id).continuousAt
  unfold profileDefectCoefficient
  fun_prop

private theorem reader_collar_limit (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (hwr : 0<w.re) :
    Tendsto (D4BMOriginalCornerCurrentAdmission.reader w (physicalRadialFrequency q)) atTop
      (𝓝 (D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q))) := by
  obtain ⟨B,_,hb⟩ := D4BMOriginalCollarCurrentBounds.normalizable_reader_collar_error w (physicalRadialFrequency q) hw
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_const_mul_atTop_of_pos hwr).mpr tendsto_id)
  have hmajor : Tendsto (fun L : ℝ => B*(Real.exp (-L)+Real.exp (-w.re*L))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul,add_zero,mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.add h2).const_mul B
  have hdiff : Tendsto (fun L : ℝ => D4BMOriginalCornerCurrentAdmission.reader w (physicalRadialFrequency q) L-
      D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q)) atTop (𝓝 0) :=
    squeeze_zero_norm' hb hmajor
  simpa only [sub_add_cancel,zero_add] using hdiff.add_const
    (D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q))

/-- The full original forcing time moment, including the unchanged normalizable radial reader. -/
def readerMomentCut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ) (L Y : ℝ) : ℂ :=
  D4BMOriginalCornerCurrentAdmission.reader w (physicalRadialFrequency q) L*
    ∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*normalizedCut q br amp L p Y

/-- Angular and horizon cutoffs can approach infinity jointly in every relative order
for the complete retained forcing moment. All original angular counterterms remain. -/
theorem original_forcing_joint_angular_horizon_moment (q : XiZeroCopy) (br : Bool)
    (amp w : ℂ) (n : ℕ) (hw : w.im≠0) (hwr : 0<w.re) :
    Tendsto (fun v : ℝ × ℝ => readerMomentCut q br amp w n v.1 (Real.exp v.2))
      ((atTop : Filter ℝ) ×ˢ atTop)
      (𝓝 (D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q)*
        physicalSelfSourceCoefficient q*
          ∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*
            forcingTrace (physicalRate q br) amp 1
              (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) p)) := by
  have hL : Tendsto (fun v : ℝ × ℝ => v.1) ((atTop : Filter ℝ) ×ˢ atTop) atTop := tendsto_fst
  have hk : Tendsto (fun v : ℝ × ℝ => v.2) ((atTop : Filter ℝ) ×ˢ atTop) atTop := tendsto_snd
  have ha := ((profile_continuous (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)).tendsto.comp unit_collar_limit).comp hL
  have hb := ((defect_coefficient_continuous (physicalRate q br) amp).tendsto.comp unit_collar_limit).comp hL
  have hS := ((original_square_finitePart q).comp Real.tendsto_exp_atTop).comp hk
  have hD := (original_green_finitePart q).comp hk
  have hN := (reader_collar_limit q w hw hwr).comp hL
  have h := (hN.mul ((ha.mul hS).add (hb.mul hD))).mul_const (onsetMoment (physicalRate q br) w n)
  simp only [reader_global] at h
  have he : (∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*
      forcingTrace (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) p)=
      forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) 1*
      onsetMoment (physicalRate q br) w n := by
    rw [onsetMoment,← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by unfold forcingTrace;ring)
  rw [he]
  have htarget : (D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q)*
      (forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) 1*
        physicalSelfSourceCoefficient q+profileDefectCoefficient (physicalRate q br) amp 1*0))*
        onsetMoment (physicalRate q br) w n =
      D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q)*
        physicalSelfSourceCoefficient q*(forcingProfile (physicalRate q br) amp 1
          (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) 1*
          onsetMoment (physicalRate q br) w n) := by ring
  rw [htarget] at h
  apply h.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ))] with v hv
  simp only [readerMomentCut,normalized_moment_eq q br amp w n hv,
    original_profile_cut_decomposition,Function.comp_def]
  ring


/-- The same original forcing moment with a finite ingoing-time cutoff. -/
def readerMomentSlab (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ) (P L Y : ℝ) : ℂ :=
  D4BMOriginalCornerCurrentAdmission.reader w (physicalRadialFrequency q) L*
    ∫ p in (0:ℝ)..P, (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*normalizedCut q br amp L p Y

private theorem original_slab_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (n : ℕ) (P Y : ℝ) {L : ℝ} (hL : 0<L) :
    readerMomentSlab q br amp w n P L Y =
      D4BMOriginalCornerCurrentAdmission.reader w (physicalRadialFrequency q) L*
        profileCut q br amp (radialUnit (-L/2)) Y*
        ∫ p in (0:ℝ)..P, (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p := by
  rw [readerMomentSlab,mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro p _
  dsimp only
  rw [original_normalized_cut q br amp hL]
  ring

/-- Every temporal moment of the full forcing has one joint ingoing-time, horizon and
angular-cutoff limit. The independent cutoffs may diverge at arbitrary relative rates.
The metric current and its evolved-response corner are separate from this source term. -/
theorem original_forcing_three_cutoff_moment (q : XiZeroCopy) (br : Bool)
    (amp w : ℂ) (n : ℕ) (hw : w.im≠0) (hwr : 0<w.re) :
    Tendsto (fun v : ℝ × ℝ × ℝ => readerMomentSlab q br amp w n v.1 v.2.1 (Real.exp v.2.2))
      ((atTop : Filter ℝ) ×ˢ (atTop ×ˢ atTop))
      (𝓝 (D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q)*
        physicalSelfSourceCoefficient q*
          ∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*
            forcingTrace (physicalRate q br) amp 1
              (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) p)) := by
  have hP : Tendsto (fun v : ℝ × ℝ × ℝ => v.1)
      ((atTop : Filter ℝ) ×ˢ (atTop ×ˢ atTop)) atTop := tendsto_fst
  have hPair : Tendsto (fun v : ℝ × ℝ × ℝ => v.2)
      ((atTop : Filter ℝ) ×ˢ (atTop ×ˢ atTop)) (atTop ×ˢ atTop) := tendsto_snd
  have hL := tendsto_fst.comp hPair
  have hk := tendsto_snd.comp hPair
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hOn := onset_moment_integrable (physicalRate q br) w n (by linarith)
  have hT := intervalIntegral_tendsto_integral_Ioi 0 hOn hP
  change Tendsto _ _ (𝓝 (onsetMoment (physicalRate q br) w n)) at hT
  have ha := ((profile_continuous (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)).tendsto.comp unit_collar_limit).comp hL
  have hb := ((defect_coefficient_continuous (physicalRate q br) amp).tendsto.comp unit_collar_limit).comp hL
  have hS := ((original_square_finitePart q).comp Real.tendsto_exp_atTop).comp hk
  have hD := (original_green_finitePart q).comp hk
  have hN := (reader_collar_limit q w hw hwr).comp hL
  have h := (hN.mul ((ha.mul hS).add (hb.mul hD))).mul hT
  simp only [reader_global,mul_zero,add_zero] at h
  have he : (∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*
      forcingTrace (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) p)=
      forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) 1*
      onsetMoment (physicalRate q br) w n := by
    rw [onsetMoment,← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by unfold forcingTrace;ring)
  rw [he]
  have hc : D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q)*
      (forcingProfile (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) 1*physicalSelfSourceCoefficient q)*
      onsetMoment (physicalRate q br) w n =
      D4BMOriginalCornerCurrentAdmission.readerTrace w (physicalRadialFrequency q)*physicalSelfSourceCoefficient q*
        (forcingProfile (physicalRate q br) amp 1
          (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) 1*onsetMoment (physicalRate q br) w n) := by ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ))] with v hv
  change 0<v.2.1 at hv
  dsimp only [Function.comp_def]
  rw [original_slab_decomposition q br amp w n v.1 (Real.exp v.2.2) hv,
    original_profile_cut_decomposition]

end
end RHTower.D4BMOriginalForcingAngularPeriod
