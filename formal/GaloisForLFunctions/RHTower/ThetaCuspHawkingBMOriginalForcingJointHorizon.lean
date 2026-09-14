import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricHorizon
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalForcingAngularPeriod

/-! The original forcing's mixed cusp/horizon corner, before angular restoration. -/
open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalForcingJointHorizon
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalCornerForcing D4BMOriginalMetricHorizon
open D4BMOriginalForcingAngularPeriod D4BMOriginalScalarRestoration
open D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

def squareCut (q : XiZeroCopy) (Y : ℝ) : ℂ :=
  truncatedIntegral (fun z => D4BMLiteralCusp.scalar (physicalAngularParameter q) (coordinates z)*
    fullSquarePotential q (coordinates z)) Y-principalCounterterm q (principalAmplitude q) Y

def firstWeight (q : XiZeroCopy) (Y : ℝ) : ℂ := squareCut q Y-greenCut q Y/2
def secondWeight (q : XiZeroCopy) (Y : ℝ) : ℂ := greenCut q Y/2
def gradient (q : XiZeroCopy) (br : Bool) : ℂ :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1

/-- The actual finite-height forcing is a combination of two fixed radial profiles. -/
theorem profile_two_kernels (q : XiZeroCopy) (br : Bool) (amp : ℂ) (u Y : ℝ) :
    profileCut q br amp u Y =
      firstWeight q Y*forcingProfile (physicalRate q br) amp 1 (gradient q br) u+
      secondWeight q Y*forcingProfile (physicalRate q br) amp 1 (gradient q br+1) u := by
  rw [original_profile_cut_decomposition]
  unfold firstWeight secondWeight squareCut gradient forcingProfile profileDefectCoefficient
  ring

theorem weights_limit (q : XiZeroCopy) :
    Tendsto (fun k : ℝ => firstWeight q (Real.exp k)) atTop (𝓝 (physicalSelfSourceCoefficient q)) ∧
    Tendsto (fun k : ℝ => secondWeight q (Real.exp k)) atTop (𝓝 0) := by
  have hS : Tendsto (fun k : ℝ => squareCut q (Real.exp k)) atTop
      (𝓝 (physicalSelfSourceCoefficient q)) := by
    exact (original_square_finitePart q).comp Real.tendsto_exp_atTop
  have hD := (original_green_finitePart q).div_const (2:ℂ)
  simpa only [firstWeight,secondWeight,zero_div,sub_zero] using And.intro (hS.sub hD) hD

/-- The literal angular-cut forcing paired with the unchanged radial reader. -/
def kernelCut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (Y x : ℝ) : ℂ :=
  Complex.exp (w*(x:ℂ))*profileCut q br amp (radialUnit x) Y*
    normalizable w (physicalRadialFrequency q) (horizonCoordinate x)

theorem kernel_two_kernels (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (Y x : ℝ) :
    kernelCut q br amp w Y x =
      firstWeight q Y*forcingKernel q br amp (gradient q br) w x+
      secondWeight q Y*forcingKernel q br amp (gradient q br+1) w x := by
  rw [kernelCut,profile_two_kernels]
  unfold forcingKernel
  ring

private theorem kernel_continuous (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    ContinuousOn (forcingKernel q br amp K w) (Iio (0:ℝ)) := by
  have hu : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hp : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (continuousAt_ofReal_cpow_const (1+radialUnit x) (2*physicalRate q br)
      (Or.inr (radialUnit_add_one_pos x).ne')).comp_of_eq
        (continuous_const.add hu).continuousAt rfl
  have hF : Continuous (fun x : ℝ => forcingProfile (physicalRate q br) amp 1 K (radialUnit x)) := by
    unfold forcingProfile
    fun_prop
  intro x hx
  have hn := ((normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior x hx)).1.continuousAt).comp_of_eq
      (horizonCoordinate_hasDerivAt x).continuousAt rfl
  exact (((show Continuous (fun x : ℝ => Complex.exp (w*(x:ℂ))) by fun_prop).continuousAt.mul
    hF.continuousAt).mul hn).continuousWithinAt

private theorem kernel_integrable (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {a b : ℝ} (ha : a<0) (hb : b<0) :
    IntervalIntegrable (forcingKernel q br amp K w) volume a b :=
  ((kernel_continuous q br amp K w).mono (fun _ hx =>
    lt_of_le_of_lt hx.2 (max_lt ha hb))).intervalIntegrable

theorem integral_two_kernels (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (Y a b : ℝ)
    (ha : a<0) (hb : b<0) :
    (∫ x in a..b,kernelCut q br amp w Y x) =
      firstWeight q Y*(∫ x in a..b,forcingKernel q br amp (gradient q br) w x)+
      secondWeight q Y*(∫ x in a..b,forcingKernel q br amp (gradient q br+1) w x) := by
  simp_rw [kernel_two_kernels]
  rw [intervalIntegral.integral_add
    ((kernel_integrable q br amp (gradient q br) w ha hb).const_mul _)
    ((kernel_integrable q br amp (gradient q br+1) w ha hb).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

/-- Both powers and the logarithm use the angular coefficients at the same finite height. -/
def counterterm (c₀ c₁ d₀ : ℂ→ℂ) (w : ℂ) (e : ℝ) : ℂ :=
  c₀ w*(e:ℂ)^w/w+c₁ w*(e:ℂ)^(w+1)/(w+1)+d₀ w*(Real.log e:ℂ)

def radialCut (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c₀ c₁ d₀ e₀ e₁ f₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) (v : ℝ×ℝ) : ℂ :=
  (∫ x in tortoiseOf v.1..tortoiseOf b,kernelCut q br amp w (Real.exp v.2) x)-
    (firstWeight q (Real.exp v.2)*counterterm c₀ c₁ d₀ w v.1+
      secondWeight q (Real.exp v.2)*counterterm e₀ e₁ f₀ w v.1)

theorem radialCut_decomposition (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c₀ c₁ d₀ e₀ e₁ f₀ : ℂ→ℂ) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1)
    (w : ℂ) (v : ℝ×ℝ) (hv : v.1 ∈ Ioo (0:ℝ) 1) :
    radialCut q br amp c₀ c₁ d₀ e₀ e₁ f₀ b w v =
      firstWeight q (Real.exp v.2)*
        ((∫ x in tortoiseOf v.1..tortoiseOf b,forcingKernel q br amp (gradient q br) w x)-
          counterterm c₀ c₁ d₀ w v.1)+
      secondWeight q (Real.exp v.2)*
        ((∫ x in tortoiseOf v.1..tortoiseOf b,forcingKernel q br amp (gradient q br+1) w x)-
          counterterm e₀ e₁ f₀ w v.1) := by
  rw [radialCut,integral_two_kernels q br amp w _ _ _ (tortoiseOf_neg hv) (tortoiseOf_neg hb)]
  ring

/-- Independent original cusp and horizon removal, including both physical QNM centers.
The finite-height Green defect is subtracted before the radial limit; its restored
contribution then tends to zero at arbitrary relative cutoff rates. -/
theorem original_forcing_joint_horizon_QNM (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ R B : ℝ, ∃ c₀ c₁ d₀ e₀ e₁ f₀ : ℂ→ℂ, 0<R ∧ 0<B ∧ B≤1/2 ∧
      ∀ b : ℝ, 0<b → b≤B →
        AnalyticAt ℂ (fun w => physicalSelfSourceCoefficient q*
          horizonFinitePart q br amp (gradient q br) c₀ c₁ d₀ b w)
            (physicalFundamentalFrequency q side) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          Tendsto (radialCut q br amp c₀ c₁ d₀ e₀ e₁ f₀ b w)
            ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ))
            (𝓝 (physicalSelfSourceCoefficient q*
              horizonFinitePart q br amp (gradient q br) c₀ c₁ d₀ b w)) := by
  obtain ⟨R₁,B₁,c₀,c₁,d₀,hR₁,hB₁,hBh₁,h₁⟩ :=
    forcing_horizon_restoration q br side amp (gradient q br)
  obtain ⟨R₂,B₂,e₀,e₁,f₀,hR₂,hB₂,hBh₂,h₂⟩ :=
    forcing_horizon_restoration q br side amp (gradient q br+1)
  refine ⟨min R₁ R₂,min B₁ B₂,c₀,c₁,d₀,e₀,e₁,f₀,lt_min hR₁ hR₂,
    lt_min hB₁ hB₂,(min_le_left _ _).trans hBh₁,?_⟩
  intro b hb hbB
  have hb₁ := hbB.trans (min_le_left B₁ B₂)
  have hb₂ := hbB.trans (min_le_right B₁ B₂)
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨hb,lt_of_le_of_lt (hb₁.trans hBh₁) (by norm_num)⟩
  refine ⟨analyticAt_const.mul (h₁ b hb hb₁).1,?_⟩
  intro w hw
  have hw₁ : w ∈ ball (physicalFundamentalFrequency q side) R₁ :=
    ball_subset_ball (min_le_left _ _) hw
  have hw₂ : w ∈ ball (physicalFundamentalFrequency q side) R₂ :=
    ball_subset_ball (min_le_right _ _) hw
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioo (0:ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e<b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds]
      with e he heb
    exact ⟨he,heb⟩
  have ht₁ : Tendsto (fun e : ℝ =>
      (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp (gradient q br) w x)-
        counterterm c₀ c₁ d₀ w e) (𝓝[>] (0:ℝ))
      (𝓝 (horizonFinitePart q br amp (gradient q br) c₀ c₁ d₀ b w)) := by
    apply ((h₁ b hb hb₁).2 w hw₁).congr'
    filter_upwards [he] with e he
    rw [forcing_radial_integral_pullback q br amp (gradient q br) w he.1 he.2.le hbI.2]
    unfold counterterm
    ring
  have ht₂ : Tendsto (fun e : ℝ =>
      (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp (gradient q br+1) w x)-
        counterterm e₀ e₁ f₀ w e) (𝓝[>] (0:ℝ))
      (𝓝 (horizonFinitePart q br amp (gradient q br+1) e₀ e₁ f₀ b w)) := by
    apply ((h₂ b hb hb₂).2 w hw₂).congr'
    filter_upwards [he] with e he
    rw [forcing_radial_integral_pullback q br amp (gradient q br+1) w he.1 he.2.le hbI.2]
    unfold counterterm
    ring
  have hf : Tendsto (fun v : ℝ×ℝ => v.1)
      ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝[>] (0:ℝ)) := tendsto_fst
  have hk : Tendsto (fun v : ℝ×ℝ => v.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) atTop := tendsto_snd
  have ht := (((weights_limit q).1.comp hk).mul (ht₁.comp hf)).add
    (((weights_limit q).2.comp hk).mul (ht₂.comp hf))
  simp only [zero_mul,add_zero] at ht
  apply ht.congr'
  filter_upwards [hf.eventually he] with v hv
  exact (radialCut_decomposition q br amp c₀ c₁ d₀ e₀ e₁ f₀ hbI w v
    ⟨hv.1,hv.2.trans hbI.2⟩).symm

end
end RHTower.D4BMOriginalForcingJointHorizon
