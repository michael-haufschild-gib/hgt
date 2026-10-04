import GaloisForLFunctions.RHTower.SoninGammaClockSymbol
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.RHTower.CCMArchimedeanPhaseDerivative
import GaloisForLFunctions.RHTower.CCMArchimedeanPhaseOperatorProduct
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# The literal Gamma clock source recovers the Hardy phase

The compensated odd clock primitive has the exact real digamma derivative.
Its fixed linear term retains the Hardy conductor and normalization; derivative
uniqueness identifies the full source with the canonical continuous phase lift.
This recovers the original Gamma phase, zeta reflection multiplier and CCM
scattering phase with their original orientations and clock scales.

Every cofinal removal of the finite source endpoints gives the same phase.
The corresponding unitary multipliers converge strongly on the original
spectral Sonin carrier. This is not a trace-norm or cubic-trace limit and
does not prove arithmetic admission or the TG sub-unit law.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
namespace RHTower

/-- The original Gamma clock density is positive on its source half-line. -/
theorem gammaClock_density_pos {u : ℝ} (hu : 0 < u) :
    0 < ccmPublishedArchimedeanDensity u := by
  rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu]
  exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

/-- Exponential majorant for the first moment of the original Gamma source. -/
theorem gammaClock_firstMoment_bound {u : ℝ} (hu : 0 < u) :
    u*ccmPublishedArchimedeanDensity u ≤ 4*Real.exp (-u/4) := by
  have hd : 0 < 1-Real.exp (-2*u) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2*u))
    (Real.exp_pos (-2*u)).le
  have hexp : Real.exp (2*u)*Real.exp (-2*u)=1 := by
    rw [← Real.exp_add]
    simp
  rw [hexp] at he
  have hdiv : u/(1-Real.exp (-2*u)) ≤ u+1/2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hp : u+1/2 ≤ 4*Real.exp (u/4) := by
    linarith [Real.add_one_le_exp (u/4)]
  rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu]
  calc
    _ = (u/(1-Real.exp (-2*u)))*Real.exp (-u/2) := by ring
    _ ≤ (u+1/2)*Real.exp (-u/2) := mul_le_mul_of_nonneg_right hdiv (Real.exp_pos _).le
    _ ≤ (4*Real.exp (u/4))*Real.exp (-u/2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The literal Gamma density has an integrable first clock moment. -/
theorem gammaClock_firstMoment_integrable :
    IntegrableOn (fun u => u*ccmPublishedArchimedeanDensity u) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun u => u*ccmPublishedArchimedeanDensity u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  have hi := (integrableOn_exp_mul_Ioi (a := -(1/4:ℝ)) (by norm_num) 0).const_mul 4
  apply hi.mono' hm.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hu (gammaClock_density_pos hu))]
  convert gammaClock_firstMoment_bound hu using 1
  ring_nf

/-- Global compensated sine bound used by the clock source and its tails. -/
theorem gammaClock_sine_remainder_bound (x : ℝ) : |x-Real.sin x| ≤ 2*x^2 := by
  by_cases hx : |x| ≤ 1
  · have hc := mul_le_mul_of_nonneg_right hx (sq_nonneg |x|)
    have hsin := Real.abs_sub_sin_le x
    nlinarith [sq_abs x]
  · have ha : 1 ≤ |x| := le_of_not_ge hx
    have hsin := Real.abs_sin_le_abs (x := x)
    have htri := abs_sub x (Real.sin x)
    nlinarith [sq_abs x]

/-- The original odd clock kernel with its exact first-order subtraction. -/
def gammaClockOddRemainder (t : ℝ) : ℝ :=
  ∫ u in Ioi 0, (t*u-Real.sin (t*u))*ccmPublishedArchimedeanDensity u/u

/-- Absolute convergence holds for every frequency before phase reconstruction. -/
theorem gammaClockOddRemainder_integrable (t : ℝ) :
    IntegrableOn (fun u => (t*u-Real.sin (t*u))*ccmPublishedArchimedeanDensity u/u) (Ioi 0) := by
  have hm : AEStronglyMeasurable
      (fun u => (t*u-Real.sin (t*u))*ccmPublishedArchimedeanDensity u/u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  apply (gammaClock_firstMoment_integrable.const_mul (2*t^2)).mono' hm.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (gammaClock_density_pos hu), abs_of_pos (show 0 < u from hu)]
  calc
    _ ≤ (2*(t*u)^2)*ccmPublishedArchimedeanDensity u/u := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (gammaClock_sine_remainder_bound (t*u)) (gammaClock_density_pos hu).le)
        (show 0 ≤ u from le_of_lt hu)
    _ = _ := by field_simp [ne_of_gt (show 0 < u from hu)]

/-- A height-local majorant for the derivative of the compensated clock kernel. -/
theorem gammaClock_cosine_bound (C t u : ℝ) (ht : |t| ≤ C) (hu : 0 < u) :
    ‖(1-Real.cos (t*u))*ccmPublishedArchimedeanDensity u‖ ≤
      C*(u*ccmPublishedArchimedeanDensity u) := by
  have hc : |1-Real.cos (t*u)| ≤ |t*u| := by
    simpa only [mul_zero, Real.cos_zero, sub_zero, abs_sub_comm] using
      Real.abs_cos_sub_cos_le (t*u) 0
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gammaClock_density_pos hu)]
  calc
    _ ≤ |t*u| *ccmPublishedArchimedeanDensity u :=
      mul_le_mul_of_nonneg_right hc (gammaClock_density_pos hu).le
    _ = |t| *(u*ccmPublishedArchimedeanDensity u) := by
      rw [abs_mul, abs_of_pos hu]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ht (mul_nonneg hu.le (gammaClock_density_pos hu).le)

/-- Derivative of the full compensated odd source, with no cutoff premise. -/
theorem hasDerivAt_gammaClockOddRemainder (t : ℝ) :
    HasDerivAt gammaClockOddRemainder
      (∫ u in Ioi (0:ℝ), (1-Real.cos (t*u))*ccmPublishedArchimedeanDensity u) t := by
  let C := |t|+1
  have hs : Ioo (-C) C ∈ 𝓝 t := Ioo_mem_nhds
    (by dsimp [C]; linarith [neg_abs_le t]) (by dsimp [C]; linarith [le_abs_self t])
  have hm (x : ℝ) : AEStronglyMeasurable
      (fun u => (x*u-Real.sin (x*u))*ccmPublishedArchimedeanDensity u/u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  have hm' : AEStronglyMeasurable
      (fun u => (1-Real.cos (t*u))*ccmPublishedArchimedeanDensity u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun x u : ℝ => (x*u-Real.sin (x*u))*ccmPublishedArchimedeanDensity u/u)
    (F' := fun x u : ℝ => (1-Real.cos (x*u))*ccmPublishedArchimedeanDensity u)
    (bound := fun u => C*(u*ccmPublishedArchimedeanDensity u)) hs
    (Eventually.of_forall fun x => (hm x).restrict)
    (gammaClockOddRemainder_integrable t) hm'.restrict
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro x hx
      exact gammaClock_cosine_bound C x u (abs_le.mpr ⟨hx.1.le,hx.2.le⟩) hu)
    (gammaClock_firstMoment_integrable.const_mul C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro x _
      have hh := ((((hasDerivAt_id x).mul_const u).sub
        ((Real.hasDerivAt_sin (x*u)).comp x ((hasDerivAt_id x).mul_const u))).mul_const
          (ccmPublishedArchimedeanDensity u)).div_const u
      convert! hh using 1
      field_simp [ne_of_gt (show 0 < u from hu)])
  exact hd.2

private theorem gauss_real_difference (t u : ℝ) (hu : 0 < u) :
    (digammaGaussIntegrand (1/4+((t/2:ℝ):ℂ)*Complex.I) (2*u)).re-
      (digammaGaussIntegrand (1/4) (2*u)).re =
        (1-Real.cos (t*u))*ccmPublishedArchimedeanDensity u := by
  rw [digammaGaussIntegrand, digammaGaussIntegrand,
    Complex.sub_re, Complex.sub_re, Complex.ofReal_re,
    one_sub_exp_neg_ofReal_eq, div_ofReal_re_digammaIntegralRepresentation,
    div_ofReal_re_digammaIntegralRepresentation, Complex.exp_re, Complex.exp_re]
  have hre : (-(1/4+((t/2:ℝ):ℂ)*Complex.I)*((2*u:ℝ):ℂ)).re = -u/2 := by
    simp [Complex.mul_re,Complex.mul_im]; ring
  have him : (-(1/4+((t/2:ℝ):ℂ)*Complex.I)*((2*u:ℝ):ℂ)).im = -(t*u) := by
    simp [Complex.mul_re,Complex.mul_im]; ring
  have hre0 : (-(1/4:ℂ)*((2*u:ℝ):ℂ)).re = -u/2 := by simp; ring
  have him0 : (-(1/4:ℂ)*((2*u:ℝ):ℂ)).im = 0 := by simp
  rw [hre,him,hre0,him0,Real.cos_neg,Real.cos_zero,
    ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hu]
  ring_nf

/-- Exact real digamma difference of the literal cosine source. -/
theorem integral_gammaClockCosineDifference (t : ℝ) :
    (∫ u in Ioi (0:ℝ), (1-Real.cos (t*u))*ccmPublishedArchimedeanDensity u) =
      ((Complex.digamma (1/4+((t/2:ℝ):ℂ)*Complex.I)).re-
        (Complex.digamma (1/4)).re)/2 := by
  let z : ℂ := 1/4+((t/2:ℝ):ℂ)*Complex.I
  have hz : 0 < z.re := by simp [z]
  have h0 : 0 < (1/4:ℂ).re := by norm_num
  have hiz := Complex.reCLM.integrable_comp (integrableOn_digammaGaussIntegrand hz)
  have hi0 := Complex.reCLM.integrable_comp (integrableOn_digammaGaussIntegrand h0)
  have hcz := Complex.reCLM.integral_comp_comm (integrableOn_digammaGaussIntegrand hz)
  have hc0 := Complex.reCLM.integral_comp_comm (integrableOn_digammaGaussIntegrand h0)
  simp only [Complex.reCLM_apply] at hiz hi0 hcz hc0
  calc
    _ = ∫ u in Ioi (0:ℝ), ((digammaGaussIntegrand z (2*u)).re-
        (digammaGaussIntegrand (1/4) (2*u)).re) :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => (gauss_real_difference t u hu).symm)
    _ = (1/2)*(∫ u in Ioi (0:ℝ), ((digammaGaussIntegrand z u).re-
        (digammaGaussIntegrand (1/4) u).re)) := by
      simpa only [mul_zero, smul_eq_mul, one_div] using
        integral_comp_mul_left_Ioi (fun u => (digammaGaussIntegrand z u).re-
          (digammaGaussIntegrand (1/4) u).re) 0 (show (0:ℝ)<2 by norm_num)
    _ = _ := by
      rw [integral_sub hiz hi0,hcz,hc0,← digamma_eq_integral_gauss hz,
        ← digamma_eq_integral_gauss h0]
      ring

/-- Literal clock phase with the original Hardy conductor and linear normalization. -/
def gammaClockHardyPhaseLift (t : ℝ) : ℝ :=
  t*gammaHardyPhaseRate 0+gammaClockOddRemainder t

/-- The actual Gamma clock source has exactly the Hardy phase velocity. -/
theorem hasDerivAt_gammaClockHardyPhaseLift (t : ℝ) :
    HasDerivAt gammaClockHardyPhaseLift (gammaHardyPhaseRate t) t := by
  have h := ((hasDerivAt_id t).mul_const (gammaHardyPhaseRate 0)).add
    (hasDerivAt_gammaClockOddRemainder t)
  apply h.congr_deriv
  rw [integral_gammaClockCosineDifference]
  simp only [gammaHardyPhaseRate]
  have harg : linePt t/2=1/4+((t/2:ℝ):ℂ)*Complex.I := by
    unfold linePt
    push_cast
    ring
  rw [harg]
  norm_num [linePt]
  ring

/-- Source identification with the canonical, globally continuous Hardy phase lift. -/
theorem gammaClockHardyPhaseLift_eq_theta (t : ℝ) :
    gammaClockHardyPhaseLift t=gammaHardyTheta t := by
  have hd (x : ℝ) : HasDerivAt (fun y => gammaClockHardyPhaseLift y-gammaHardyTheta y) 0 x := by
    simpa only [sub_self] using!
      (hasDerivAt_gammaClockHardyPhaseLift x).sub (hasDerivAt_gammaHardyTheta x)
  have h := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t 0
  apply sub_eq_zero.mp
  simpa [gammaClockHardyPhaseLift,gammaClockOddRemainder,gammaHardyTheta] using h

/-- The complete compensated clock source reconstructs the original normalized Gamma phase. -/
theorem gammaHardyPhase_eq_exp_gammaClock (t : ℝ) :
    gammaHardyPhase t=Complex.exp (-Complex.I*(gammaClockHardyPhaseLift t:ℂ)) := by
  rw [gammaClockHardyPhaseLift_eq_theta, gammaHardyPhase_eq_exp_neg_theta]

/-- The literal finite compensated odd clock source, with the same fixed normalization. -/
def gammaClockHardyPhaseCutoff (t ε R : ℝ) : ℝ :=
  t*gammaHardyPhaseRate 0+
    ∫ u in Icc ε R, (t*u-Real.sin (t*u))*ccmPublishedArchimedeanDensity u/u

/-- Every cofinal removal of the original clock endpoints gives the same Hardy lift. -/
theorem gammaClockHardyPhaseCutoff_tendsto (t : ℝ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    Tendsto (fun i => gammaClockHardyPhaseCutoff t (ε i) (R i)) l (𝓝 (gammaHardyTheta t)) := by
  have hc : AECover (volume.restrict (Ioi (0:ℝ))) l (fun i => Icc (ε i) (R i)) :=
    (aecover_Ioi_of_Ici (hε.mono_right nhdsWithin_le_nhds)).inter (aecover_Iic hR)
  have ht := hc.integral_tendsto_of_countably_generated (gammaClockOddRemainder_integrable t)
  have hfull := (tendsto_const_nhds (x := t*gammaHardyPhaseRate 0)).add ht
  rw [← gammaClockHardyPhaseLift_eq_theta t]
  apply hfull.congr'
  filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
  rw [Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (show Icc (ε i) (R i) ⊆ Ioi 0 from fun u hu => lt_of_lt_of_le hi hu.1)]
  rfl

/-- The exact zeta reflection multiplier is the exponential of the literal clock phase. -/
theorem zetaChi_line_eq_exp_gammaClock (t : ℝ) :
    zetaChi (linePt t)=Complex.exp (-2*Complex.I*(gammaClockHardyPhaseLift t:ℂ)) := by
  rw [← gammaHardyPhase_sq, gammaHardyPhase_eq_exp_gammaClock, ← Complex.exp_add]
  congr 1
  ring

/-- Actual Hardy decomposition with the source-derived archimedean phase. -/
theorem riemannZeta_line_eq_gammaClock_mul_hardyZ (t : ℝ) :
    riemannZeta (linePt t)=
      Complex.exp (-Complex.I*(gammaClockHardyPhaseLift t:ℂ))*(hardyZ t:ℂ) := by
  rw [riemannZeta_line_eq_gammaHardyPhase_mul_hardyZ, gammaHardyPhase_eq_exp_gammaClock]

/-- The actual scattering phase, with the original orientation and factor two. -/
theorem ccmArchimedeanScatteringPhase_eq_exp_gammaClock (t : ℝ) :
    ccmArchimedeanScatteringPhase t=
      Complex.exp (2*Complex.I*(gammaClockHardyPhaseLift t:ℂ)) := by
  have hc : (starRingEnd ℂ) (Complex.exp (-Complex.I*(gammaClockHardyPhaseLift t:ℂ)))=
      Complex.exp (Complex.I*(gammaClockHardyPhaseLift t:ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [ccmArchimedeanScatteringPhase_eq_conj_gamma_sq, gammaHardyPhase_eq_exp_gammaClock,
    hc, ← Complex.exp_add]
  congr 1
  ring

private theorem cutoffLift_measurable (ε R : ℝ) :
    Measurable (fun t => gammaClockHardyPhaseCutoff t ε R) := by
  have h : Measurable (fun p : ℝ × ℝ =>
      (p.1*p.2-Real.sin (p.1*p.2))*ccmPublishedArchimedeanDensity p.2/p.2) := by
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  exact (measurable_id.mul_const (gammaHardyPhaseRate 0)).add
    h.stronglyMeasurable.integral_prod_right'.measurable

/-- The exponentiated literal finite clock phase on the spectral carrier. -/
def gammaClockScatteringCutoffSymbol (ε R t : ℝ) : ℂ :=
  Complex.exp (2*Complex.I*(gammaClockHardyPhaseCutoff t ε R:ℂ))

private theorem cutoffSymbol_measurable (ε R : ℝ) :
    Measurable (gammaClockScatteringCutoffSymbol ε R) :=
  Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp (cutoffLift_measurable ε R)))

private theorem cutoffSymbol_norm (ε R t : ℝ) :
    ‖gammaClockScatteringCutoffSymbol ε R t‖=1 := by
  simp [gammaClockScatteringCutoffSymbol,Complex.norm_exp]

/-- Every finite compensated source gives a unitary on the original spectral L2 carrier. -/
def gammaClockScatteringCutoffUnitary (ε R : ℝ) : SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  (⟨gammaClockScatteringCutoffSymbol ε R,
    (cutoffSymbol_measurable ε R).aestronglyMeasurable,
    Eventually.of_forall (cutoffSymbol_norm ε R)⟩ :
      GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ volume).mulUnitary

private theorem cutoffUnitary_eq_multiplier (ε R : ℝ) (f : SoninL2) :
    gammaClockScatteringCutoffUnitary ε R f=
      lpBoundedMulCLM (p := 2) (μ := volume) (cutoffSymbol_measurable ε R)
        zero_le_one (fun t => (cutoffSymbol_norm ε R t).le) f := by
  apply Lp.ext
  have hleft := (⟨gammaClockScatteringCutoffSymbol ε R,
    (cutoffSymbol_measurable ε R).aestronglyMeasurable,
    Eventually.of_forall (cutoffSymbol_norm ε R)⟩ :
      GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ volume).mulUnitary_ae f
  have hright := lpBoundedMulCLM_coeFn (p := 2) (μ := volume) (cutoffSymbol_measurable ε R)
    zero_le_one (fun t => (cutoffSymbol_norm ε R t).le) f
  exact hleft.trans hright.symm

/-- Cofinal source exponentials converge strongly to the original CCM scattering unitary. -/
theorem gammaClockScatteringCutoffUnitary_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (f : SoninL2) :
    Tendsto (fun i => gammaClockScatteringCutoffUnitary (ε i) (R i) f) l
      (𝓝 (ccmArchimedeanScatteringL2Unitary f)) := by
  have hpt (t : ℝ) : Tendsto (fun i => gammaClockScatteringCutoffSymbol (ε i) (R i) t) l
      (𝓝 (ccmArchimedeanScatteringPhase t)) := by
    rw [ccmArchimedeanScatteringPhase_eq_exp_gammaClock, gammaClockHardyPhaseLift_eq_theta]
    have hc : Continuous (fun x : ℝ => Complex.exp (2*Complex.I*(x:ℂ))) := by fun_prop
    exact hc.continuousAt.tendsto.comp (gammaClockHardyPhaseCutoff_tendsto t hε hR)
  have hm := ccmArchimedeanScatteringPhase_hasTemperateGrowth.1.continuous.measurable
  have h := tendsto_lpBoundedMulCLM_apply
    (fun i => cutoffSymbol_measurable (ε i) (R i)) hm zero_le_one
    (fun i t => (cutoffSymbol_norm (ε i) (R i) t).le)
    (fun t => (norm_ccmArchimedeanScatteringPhase t).le) hpt f
  have he : lpBoundedMulCLM (p := 2) (μ := volume) hm zero_le_one
      (fun t => (norm_ccmArchimedeanScatteringPhase t).le) f=
        ccmArchimedeanScatteringL2Unitary f := by
    apply Lp.ext
    exact (lpBoundedMulCLM_coeFn (p := 2) (μ := volume) hm zero_le_one
      (fun t => (norm_ccmArchimedeanScatteringPhase t).le) f).trans
        (ccmArchimedeanScatteringUnitPhase.mulUnitary_ae f).symm
  simpa only [← cutoffUnitary_eq_multiplier,he] using! h

end RHTower
