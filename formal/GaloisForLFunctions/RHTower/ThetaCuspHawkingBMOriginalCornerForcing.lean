import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonGreenMatch

/-! The normalized original horizon forcing, its time moments, and its QNM-regular contact. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalCornerForcing
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore D4BMOriginalHorizonGreenMatch
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The full source after removing its single geometric horizon factor. -/
def forcingProfile (s amp J K : ℂ) (u : ℝ) : ℂ :=
  -2*(u:ℂ)*power (2*s) (1+u)*amp^2*
    (((5*s^2+15*s+4)/4)*J+s*(s-1)*(u:ℂ)^2/4*((s+2)^2*J-K))

/-- Exact factorization of the original forcing; both angular channels remain. -/
theorem original_forcing_factor (s amp J K : ℂ) (x : ℝ) :
    D4BMJointSource.originalForcing s 0 amp 1 J K x =
      (horizonCoordinate x:ℂ)*forcingProfile s amp J K (radialUnit x) := by
  simp only [D4BMJointSource.originalForcing,sourceAmplitude,zero_mul,
    Complex.exp_zero,one_mul,mul_one,horizonCoordinate,forcingProfile]
  push_cast
  ring

private theorem profile_continuousAt (s amp J K : ℂ) :
    ContinuousAt (forcingProfile s amp J K) 1 := by
  have hp := (power_derivatives (2*s) (by norm_num : 0 < 1+(1:ℝ))).1.continuousAt.comp
    (continuous_const.add continuous_id).continuousAt
  unfold forcingProfile
  fun_prop

private theorem unit_collar_limit :
    Tendsto (fun L : ℝ => radialUnit (-L/2)) atTop (𝓝 (1:ℝ)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hform (L : ℝ) : radialUnit (-L/2)=(1-Real.exp (-L))/(1+Real.exp (-L)) := by
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (-L)))).mpr
    have h := radialUnit_one_sub (-L/2)
    rw [show 2*(-L/2) = -L by ring] at h
    nlinarith
  simp_rw [hform]
  convert! (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
    (by norm_num : (1:ℝ)+0 ≠ 0) using 1
  · norm_num

/-- The source trace retains the literal causal onset. -/
def forcingTrace (s amp J K : ℂ) (p : ℝ) : ℂ :=
  forcingProfile s amp J K 1*timeOnset (2*s) p

/-- Exact normalized original source at every positive collar length. -/
theorem original_full_forcing_normalized (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    {L : ℝ} (hL : 0 < L) (p : ℝ) (z : D4BMHorizon.Point) :
    timeOriginalForcing q br amp (p+L/2) (-L/2) z / (horizonCoordinate (-L/2):ℂ) =
      forcingProfile (physicalRate q br) amp (fullSquarePotential q z)
        (fullGradientEnergy q z/2) (radialUnit (-L/2))*timeOnset (2*physicalRate q br) p := by
  have hz : (horizonCoordinate (-L/2):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (horizonCoordinate_interior (-L/2) (by linarith)).1)
  simp only [timeOriginalForcing,original_forcing_factor,show p+L/2+-L/2=p by ring]
  apply (div_eq_iff hz).mpr
  ring

/-- The horizon trace comes from the full original time source before angular subtraction. -/
theorem original_full_forcing_horizon (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p : ℝ) (z : D4BMHorizon.Point) :
    Tendsto (fun L : ℝ => timeOriginalForcing q br amp (p+L/2) (-L/2) z /
      (horizonCoordinate (-L/2):ℂ)) atTop
      (𝓝 (forcingTrace (physicalRate q br) amp (fullSquarePotential q z)
        (fullGradientEnergy q z/2) p)) := by
  have ht := ((profile_continuousAt (physicalRate q br) amp (fullSquarePotential q z)
    (fullGradientEnergy q z/2)).tendsto.comp unit_collar_limit).mul_const
      (timeOnset (2*physicalRate q br) p)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact (original_full_forcing_normalized q br amp hL p z).symm

private theorem profile_collar_bound (s amp J K : ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop,
      ‖forcingProfile s amp J K (radialUnit (-L/2))-forcingProfile s amp J K 1‖ ≤ B*Real.exp (-L) := by
  have hp := ((power_derivatives (2*s) (by norm_num : 0 < 1+(1:ℝ))).1.scomp 1
    ((hasDerivAt_id (1:ℝ)).const_add 1)).differentiableAt
  have hd : DifferentiableAt ℝ (forcingProfile s amp J K) 1 := by
    unfold forcingProfile
    fun_prop
  obtain ⟨B,hB,hb⟩ := hd.isBigO_sub.exists_pos
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [unit_collar_limit.eventually hb.bound,eventually_gt_atTop (0:ℝ)] with L h hL
  have hu := (radialUnit_bounds (-L/2) (by linarith)).2
  have he := radialUnit_one_sub (-L/2)
  rw [show 2*(-L/2) = -L by ring] at he
  have hn : ‖radialUnit (-L/2)-(1:ℝ)‖ = 1-radialUnit (-L/2) := by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hu.le)]
    ring
  rw [hn,he] at h
  apply h.trans
  calc
    _ ≤ B*(Real.exp (-L)*2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith : 1+radialUnit (-L/2) ≤ 2)
        (Real.exp_nonneg _)) hB.le
    _ = _ := by ring

private theorem onset_bound (s : ℂ) (p : ℝ) :
    ‖timeOnset (2*s) p‖ ≤ Real.exp ((2*s).re*p) := by
  have hc : ‖(Real.smoothTransition p:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg p)]
      using Real.smoothTransition.le_one p
  simp only [timeOnset,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) hc

/-- A single horizon error bound holds for every original ingoing time, retaining the full source. -/
theorem original_full_forcing_collar_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (z : D4BMHorizon.Point) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop, ∀ p : ℝ,
      ‖timeOriginalForcing q br amp (p+L/2) (-L/2) z / (horizonCoordinate (-L/2):ℂ)-
        forcingTrace (physicalRate q br) amp (fullSquarePotential q z) (fullGradientEnergy q z/2) p‖ ≤
          B*Real.exp (-L)*Real.exp ((2*physicalRate q br).re*p) := by
  obtain ⟨B,hB,hb⟩ := profile_collar_bound (physicalRate q br) amp (fullSquarePotential q z)
    (fullGradientEnergy q z/2)
  refine ⟨B,hB,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with L h hL p
  rw [original_full_forcing_normalized q br amp hL p z,forcingTrace,← sub_mul,norm_mul]
  exact mul_le_mul h (onset_bound (physicalRate q br) p) (norm_nonneg _) (by positivity)

/-- The normalized transform of the original forcing trace. -/
def forcingTransform (s amp J K w : ℂ) : ℂ :=
  Complex.exp (-w*(Real.log 2:ℂ))*
    ∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p

/-- One explicit continuation of the same original source transform. -/
def continuedForcingTransform (s amp J K w : ℂ) : ℂ :=
  Complex.exp (-w*(Real.log 2:ℂ))*forcingProfile s amp J K 1*continuedOnset s w

theorem forcing_trace_integrable (s amp J K w : ℂ) (hw : (2*s).re < w.re) :
    IntegrableOn (fun p : ℝ => Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p) (Ioi 0) := by
  simpa only [IntegrableOn,forcingTrace,mul_left_comm] using!
    (timeOnset_integrable (2*s) w hw).const_mul (forcingProfile s amp J K 1)

/-- Equality is proved on the original convergence half-plane, before continuation. -/
theorem continued_forcing_eq_original (s amp J K w : ℂ) (hw : (2*s).re < w.re) :
    continuedForcingTransform s amp J K w=forcingTransform s amp J K w := by
  simp only [forcingTransform,forcingTrace,mul_left_comm (Complex.exp _) (forcingProfile _ _ _ _ _),
    integral_const_mul,timeOnset_laplace,onsetTransform_eq (2*s) w hw,
    continuedForcingTransform,continuedOnset,mul_assoc]

/-- The actual collar transforms are admitted and converge to the same continued source family. -/
theorem original_full_forcing_laplace_horizon (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : (2*physicalRate q br).re < w.re) (z : D4BMHorizon.Point) :
    (∀ L : ℝ, 0 < L → IntegrableOn (fun p : ℝ => Complex.exp (-w*(p:ℂ))*
      (timeOriginalForcing q br amp (p+L/2) (-L/2) z/(horizonCoordinate (-L/2):ℂ))) (Ioi 0)) ∧
    Tendsto (fun L : ℝ => Complex.exp (-w*(Real.log 2:ℂ))*∫ p in Ioi (0:ℝ),
      Complex.exp (-w*(p:ℂ))*(timeOriginalForcing q br amp (p+L/2) (-L/2) z/
        (horizonCoordinate (-L/2):ℂ))) atTop
      (𝓝 (continuedForcingTransform (physicalRate q br) amp (fullSquarePotential q z)
        (fullGradientEnergy q z/2) w)) := by
  constructor
  · intro L hL
    change Integrable (fun p : ℝ => Complex.exp (-w*(p:ℂ))*
      (timeOriginalForcing q br amp (p+L/2) (-L/2) z/(horizonCoordinate (-L/2):ℂ)))
        (volume.restrict (Ioi 0))
    convert! (timeOnset_integrable (2*physicalRate q br) w hw).const_mul
      (forcingProfile (physicalRate q br) amp (fullSquarePotential q z)
        (fullGradientEnergy q z/2) (radialUnit (-L/2))) using 1
    ext p
    rw [original_full_forcing_normalized q br amp hL p z]
    ring
  · have ht := (((profile_continuousAt (physicalRate q br) amp (fullSquarePotential q z)
        (fullGradientEnergy q z/2)).tendsto.comp unit_collar_limit).const_mul
          (Complex.exp (-w*(Real.log 2:ℂ)))).mul_const (onsetTransform (2*physicalRate q br) w)
    rw [continuedForcingTransform,continuedOnset,← onsetTransform_eq (2*physicalRate q br) w hw]
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    simp_rw [original_full_forcing_normalized q br amp hL]
    simp only [mul_left_comm (Complex.exp _) (forcingProfile _ _ _ _ _),
      integral_const_mul,timeOnset_laplace,Function.comp_apply,mul_assoc]

/-- Exact horizon coefficients in the full scalar and angular-Laplacian basis. -/
def forcingValueCoefficient (s amp : ℂ) : ℂ :=
  -2*power (2*s) 2*amp^2*((5*s^2+15*s+4)/4+s*(s-1)*(s+2)*(2*s+3)/4)

def forcingLaplacianCoefficient (s amp : ℂ) : ℂ :=
  power (2*s) 2*amp^2*s*(s-1)/4

/-- The horizon source retains the exact angular derivative, before any finite-part transposition. -/
theorem forcing_trace_angular_laplacian (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p : ℝ) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    forcingTrace (physicalRate q br) amp (fullSquarePotential q z) (fullGradientEnergy q z/2) p =
      (forcingValueCoefficient (physicalRate q br) amp*fullSquarePotential q z+
        forcingLaplacianCoefficient (physicalRate q br) amp*
          D4BMHorizon.scalarLaplacian (fullSquarePotential q) z)*timeOnset (2*physicalRate q br) p := by
  rw [fullSquarePotential_laplacian q br z hz]
  norm_num only [forcingTrace,forcingProfile,forcingValueCoefficient,forcingLaplacianCoefficient,
    Complex.ofReal_one,one_pow,mul_one]
  ring

/-- The original Green gradient slot has exactly the same scalar/Laplacian coefficients. -/
theorem physical_forcing_profile_coefficients (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    forcingProfile (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) 1 =
      forcingValueCoefficient (physicalRate q br) amp+
        (physicalAngularParameter q^2-1/4)*forcingLaplacianCoefficient (physicalRate q br) amp := by
  unfold reducedGreenGradient
  rw [physicalRadialFrequency_parameter]
  norm_num only [forcingProfile,forcingValueCoefficient,forcingLaplacianCoefficient,
    Complex.ofReal_one,one_pow,mul_one]
  ring

/-- No new poles are introduced by the full angular source or its horizon normalization. -/
theorem continued_forcing_analyticAt (s amp J K w : ℂ) (hw : w-2*s ≠ 0) :
    AnalyticAt ℂ (continuedForcingTransform s amp J K) w := by
  have he : AnalyticAt ℂ (fun u : ℂ => Complex.exp (-u*(Real.log 2:ℂ))) w := by
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (show Differentiable ℂ (fun u : ℂ => Complex.exp (-u*(Real.log 2:ℂ))) by fun_prop)) w (mem_univ _)
  exact (he.mul analyticAt_const).mul (continuedOnset_analyticAt s w hw)

/-- At either physical fundamental QNM the source contact and its first moment are regular. -/
theorem physical_forcing_analyticAt (q : XiZeroCopy) (br side : Bool) (amp J K : ℂ) :
    AnalyticAt ℂ (continuedForcingTransform (physicalRate q br) amp J K)
      (physicalFundamentalFrequency q side) :=
  continued_forcing_analyticAt _ _ _ _ _ (physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side)

private theorem trace_bound (s amp J K : ℂ) (p : ℝ) :
    ‖forcingTrace s amp J K p‖ ≤ ‖forcingProfile s amp J K 1‖*Real.exp ((2*s).re*p) := by
  have hc : ‖(Real.smoothTransition p:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg p)]
      using Real.smoothTransition.le_one p
  simp only [forcingTrace,timeOnset,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (Real.exp_nonneg _) hc) (norm_nonneg _)

private theorem moment_majorant_integrable (n : ℕ) {c : ℝ} (hc : 0 < c) (B : ℝ) :
    IntegrableOn (fun p : ℝ => B*(p^n*Real.exp (-c*p))) (Ioi 0) := by
  have hn : (-1:ℝ) < (n:ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) hn (by norm_num) hc
  simpa only [IntegrableOn,Real.rpow_one,Real.rpow_natCast] using h.const_mul B

private theorem moment_bound (s amp J K w : ℂ) (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ‖(p:ℂ)^n*Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p‖ ≤
      ‖forcingProfile s amp J K 1‖*(p^n*Real.exp (-(w.re-(2*s).re)*p)) := by
  have he : ‖Complex.exp (-w*(p:ℂ))‖ = Real.exp (-w.re*p) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,he]
  calc
    _ ≤ (p^n*Real.exp (-w.re*p))*(‖forcingProfile s amp J K 1‖*Real.exp ((2*s).re*p)) :=
      mul_le_mul_of_nonneg_left (trace_bound s amp J K p) (by positivity)
    _ = _ := by
      rw [show -(w.re-(2*s).re)*p = -w.re*p+(2*s).re*p by ring,Real.exp_add]
      ring

/-- Every temporal moment of the original source trace is admitted in its exact half-plane. -/
theorem forcing_moment_integrable (s amp J K w : ℂ) (n : ℕ) (hw : (2*s).re < w.re) :
    IntegrableOn (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p) (Ioi 0) := by
  apply (moment_majorant_integrable n (sub_pos.mpr hw) ‖forcingProfile s amp J K 1‖).mono'
    (by unfold forcingTrace timeOnset; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact moment_bound s amp J K w n hp.le

private theorem trace_laplace_hasDerivAt (s amp J K w : ℂ) (hw : (2*s).re < w.re) :
    HasDerivAt (fun u : ℂ => ∫ p in Ioi (0:ℝ),
      Complex.exp (-u*(p:ℂ))*forcingTrace s amp J K p)
      (-(∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p)) w := by
  let G := (2*s).re
  let c := (G+w.re)/2
  let B := ‖forcingProfile s amp J K 1‖
  have hGc : G < c := by dsimp [c,G]; linarith
  have hcw : c < w.re := by dsimp [c,G]; linarith
  let F := fun z : ℂ => fun p : ℝ => Complex.exp (-z*(p:ℂ))*forcingTrace s amp J K p
  let D := fun z : ℂ => fun p : ℝ => -(p:ℂ)*Complex.exp (-z*(p:ℂ))*forcingTrace s amp J K p
  have hF (z : ℂ) : AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    dsimp only [F,forcingTrace,timeOnset]; fun_prop
  have hD : AEStronglyMeasurable (D w) (volume.restrict (Ioi 0)) := by
    dsimp only [D,forcingTrace,timeOnset]; fun_prop
  have hi : Integrable (F w) (volume.restrict (Ioi 0)) := by
    simpa only [IntegrableOn,F] using! forcing_trace_integrable s amp J K w hw
  have hs : {z : ℂ | c < z.re} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hcw
  have hdiff (p : ℝ) (z : ℂ) : HasDerivAt (fun a => F a p) (D z p) z := by
    apply (((Complex.hasDerivAt_exp (-z*(p:ℂ))).comp z
      ((hasDerivAt_id z).neg.mul_const (p:ℂ))).mul_const (forcingTrace s amp J K p)).congr_deriv
    dsimp [D]
    ring
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=D) (μ:=volume.restrict (Ioi 0))
    (bound:=fun p : ℝ => B*(p*Real.exp (-(c-G)*p))) hs
    (Filter.Eventually.of_forall hF) hi hD
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      intro z hz
      have h1 := moment_bound s amp J K z 1 hp.le
      have hnorm : ‖D z p‖ = ‖(p:ℂ)^1*Complex.exp (-z*(p:ℂ))*forcingTrace s amp J K p‖ := by
        simp only [D,pow_one,neg_mul,norm_neg]
      rw [hnorm]
      apply h1.trans
      simp only [pow_one]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hp.le
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (sub_le_sub_right hz.le G)) hp.le)
    (by simpa only [IntegrableOn,pow_one] using moment_majorant_integrable 1 (sub_pos.mpr hGc) B)
    (Filter.Eventually.of_forall (fun p z _ => hdiff p z))
  simpa only [F,D,neg_mul,integral_neg] using hder.2

/-- The normalized forcing derivative is its original first temporal moment, including log 2. -/
theorem forcing_transform_hasDerivAt (s amp J K w : ℂ) (hw : (2*s).re < w.re) :
    HasDerivAt (forcingTransform s amp J K)
      (Complex.exp (-w*(Real.log 2:ℂ))*(-(Real.log 2:ℂ)*
        (∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p)-
        ∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p)) w := by
  apply (((Complex.hasDerivAt_exp (-w*(Real.log 2:ℂ))).comp w
    ((hasDerivAt_id w).neg.mul_const (Real.log 2:ℂ))).mul
      (trace_laplace_hasDerivAt s amp J K w hw)).congr_deriv
  dsimp only [forcingTransform,Function.comp_def,Pi.neg_apply,id_eq]
  ring

/-- The continued contact derivative agrees with that original first moment before continuation. -/
theorem continued_forcing_original_firstMoment (s amp J K w : ℂ) (hw : (2*s).re < w.re) :
    HasDerivAt (continuedForcingTransform s amp J K)
      (Complex.exp (-w*(Real.log 2:ℂ))*(-(Real.log 2:ℂ)*
        (∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p)-
        ∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*forcingTrace s amp J K p)) w := by
  have he : continuedForcingTransform s amp J K =ᶠ[𝓝 w] forcingTransform s amp J K := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt hw] with u hu
    exact continued_forcing_eq_original s amp J K u hu
  exact (forcing_transform_hasDerivAt s amp J K w hw).congr_of_eventuallyEq he

/-- The first-moment forcing contact vanishes at the physical QNM connection zero. -/
theorem physical_forcing_contact_tendsto_zero (q : XiZeroCopy) (br side : Bool) (amp J K : ℂ) :
    Tendsto (fun w : ℂ => connection w (physicalRadialFrequency q)/(2*w)*w*
      deriv (continuedForcingTransform (physicalRate q br) amp J K) w)
      (𝓝 (physicalFundamentalFrequency q side)) (𝓝 0) := by
  have hb := (D4BMOriginalCornerSpectralBalance.physical_oppositeCoefficient_hasDerivAt q side).continuousAt.tendsto
  have hd := (physical_forcing_analyticAt q br side amp J K).deriv.continuousAt.tendsto
  simpa only [physicalFundamentalFrequency_connection_zero,zero_div,zero_mul,id_eq] using!
    (hb.mul tendsto_id).mul hd

/-- Adding the source-derived forcing contact preserves the exact response-corner residue.
This evaluates the complete corner candidate; it does not identify the original spacetime finite part. -/
theorem complete_corner_candidate_residue (q : XiZeroCopy) (br side : Bool) (amp J K C μ : ℂ) :
    Tendsto (fun w : ℂ => (w-physicalFundamentalFrequency q side)*
      (μ*(connection w (physicalRadialFrequency q)/(2*w))*
        ((μ-2)*continuedCornerAmplitude q br amp w+
          2*w*(μ-2)*deriv (continuedCornerAmplitude q br amp) w+
          w*C*deriv (continuedForcingTransform (physicalRate q br) amp J K) w)))
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (μ*(μ-2)*(physicalSelfSourceCoefficient q*
        fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q br) amp*
        continuedOnset (physicalRate q br) (physicalFundamentalFrequency q side)))) := by
  have hr := (original_corner_response_residue q br side amp).const_mul (μ*(μ-2))
  have hzero : Tendsto (fun w : ℂ => μ*C*((w-physicalFundamentalFrequency q side)*
      (connection w (physicalRadialFrequency q)/(2*w)*w*
        deriv (continuedForcingTransform (physicalRate q br) amp J K) w)))
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) := by
    simpa only [sub_self,mul_zero,id_eq] using!
      (((tendsto_id.sub_const (physicalFundamentalFrequency q side)).mul
        (physical_forcing_contact_tendsto_zero q br side amp J K)).const_mul (μ*C)).mono_left
          (nhdsWithin_le_nhds (s:={physicalFundamentalFrequency q side}ᶜ))
  have ht := hr.add hzero
  simp only [add_zero] at ht
  convert ht using 1
  ext w
  ring

/-- The proposed full corner at the unchanged physical angular and source coefficients. -/
def physicalCornerCandidate (q : XiZeroCopy) (br : Bool) (amp w : ℂ) : ℂ :=
  let μ := physicalAngularParameter q^2-1/4
  μ*(connection w (physicalRadialFrequency q)/(2*w))*
    ((μ-2)*continuedCornerAmplitude q br amp w+
      2*w*(μ-2)*deriv (continuedCornerAmplitude q br amp) w+
      w*physicalSelfSourceCoefficient q*
        deriv (continuedForcingTransform (physicalRate q br) amp 1
          (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)) w)

/-- The forcing-regular full corner candidate has its original source residue in both branches. -/
theorem physical_corner_candidate_residue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (fun w : ℂ => (w-physicalFundamentalFrequency q side)*physicalCornerCandidate q br amp w)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 ((physicalAngularParameter q^2-1/4)*(physicalAngularParameter q^2-1/4-2)*
        (physicalSelfSourceCoefficient q*
          fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q br) amp*
          continuedOnset (physicalRate q br) (physicalFundamentalFrequency q side)))) :=
  complete_corner_candidate_residue q br side amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)
    (physicalSelfSourceCoefficient q) (physicalAngularParameter q^2-1/4)

end
end RHTower.D4BMOriginalCornerForcing
