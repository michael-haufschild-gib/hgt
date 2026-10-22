import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalMetricForcingMatch
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalForcingJointHorizon

/-! The original fourth metric-boundary transfer reduces exactly to two fixed
forcing kernels. Its physical source-time integral converges at both fundamental
QNMs. Source-derived radial power/logarithmic counterterms retain their actual
finite-height and finite-time coefficients, giving independent restoration of
time, cusp and horizon cutoffs. The evolved-source transfers and complete metric
action are not identified by this forcing-sector theorem. -/

open Set Filter Topology Metric MeasureTheory
namespace RHTower.D4BMOriginalForcingBoundaryQNM
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalForcingProductBounds D4BMOriginalForcingAngularPeriod D4BMOriginalCornerForcing
open D4BMOriginalAngularReaderBounds D4BMOriginalMetricHorizon
noncomputable section
set_option autoImplicit false

def firstWeight (q : XiZeroCopy) (br : Bool) (x k : ℝ) : ℂ :=
  fixedProduct q br false true x k-fixedProduct q br true true x k
def secondWeight (q : XiZeroCopy) (br : Bool) (x k : ℝ) : ℂ := fixedProduct q br true true x k

/-- The actual normal-reader forcing product, before radial integration. -/
def boundaryKernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x k t : ℝ) : ℂ :=
  Complex.exp (w*(t:ℂ))*normalizable w (physicalRadialFrequency q) (horizonCoordinate t)*
    (forcingProfile (physicalRate q br) amp (fullSquarePotential q ![x,Real.exp k])
      (fullGradientEnergy q ![x,Real.exp k]/2) (radialUnit t)*angularJet q true x k-
      (∑ i : Fin 3,profilePrincipal q br amp (radialUnit t) i*
        (Real.exp k:ℂ)^principalExponent q i)*angularPrincipal q true k)

/-- The exact physical boundary uses two already-restored radial kernels. -/
theorem boundary_two_kernels (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x k t : ℝ) :
    boundaryKernel q br amp w x k t=
      firstWeight q br x k*forcingKernel q br amp 0 w t+
      secondWeight q br x k*forcingKernel q br amp 1 w t := by
  simp only [boundaryKernel,firstWeight,secondWeight,fixedProduct,sourcePrincipal,forcingKernel,
    sourceField,sourceCoefficient,Bool.false_eq_true,↓reduceIte,Fin.sum_univ_three,
    profilePrincipal,principalGradient,forcingProfile,Matrix.cons_val]
  ring

/-- The actual finite-time product has exactly this radial kernel and its original onset. -/
theorem original_product_kernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (p L x k : ℝ) (hL : 0<L) :
    normalizedProduct q br amp w true p L x k=
      timeOnset (2*physicalRate q br) p*boundaryKernel q br amp w x k (-L/2) := by
  rw [normalizedProduct,original_full_forcing_normalized q br amp hL]
  simp only [boundaryKernel,D4BMOriginalReaderCuspBounds.reader,tortoiseMode,radialMode,↓reduceIte]
  ring

/-- The original radius Jacobian and the full metric coefficient leave exactly
this forcing kernel, with the unchanged damped onset. -/
theorem physical_metric_kernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwi : w.im≠0)
    (p L x k : ℝ) (hL : 0<L) :
    let R := D4BMJointWave.tortoiseRadius (-L/2)
    let f := (R:ℂ)^(2 : ℕ)-1
    f*((-w*(R:ℂ))/f^(2 : ℕ)*D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k)=
      -w*Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p*
        boundaryKernel q br amp w x k (-L/2) := by
  dsimp only
  let R := D4BMJointWave.tortoiseRadius (-L/2)
  have hR : 1<R := D4BMJointWave.tortoiseRadius_exterior (-L/2) (by linarith)
  have hR0 : (R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hf : (R:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (ne_of_gt (show 0<R^(2 : ℕ)-1 by nlinarith))
  have hZ : (R:ℂ)^(2 : ℕ)*(horizonCoordinate (-L/2):ℂ)=(R:ℂ)^(2 : ℕ)-1 := by
    rw [horizonCoordinate,radialUnit_inverse_radius]
    push_cast
    change (R:ℂ)^(2 : ℕ)*(1-(R:ℂ)⁻¹^(2 : ℕ))=(R:ℂ)^(2 : ℕ)-1
    field_simp
  rw [D4BMOriginalMetricForcingMatch.forcing_transfer_cut q br amp w hwi p L x k hL,
    raw_product_factor q br amp w true p L x k hL,original_product_kernel q br amp w p L x k hL]
  have halg (r z c : ℂ) (hf : r^(2 : ℕ)-1≠0) (hz : r^(2 : ℕ)*z=r^(2 : ℕ)-1) :
      (r^(2 : ℕ)-1)*((-w*r)/(r^(2 : ℕ)-1)^(2 : ℕ)*(r*z*c))=-w*c := by
    calc
      _ = -w*c*(r^(2 : ℕ)*z/(r^(2 : ℕ)-1)) := by field_simp
      _ = _ := by rw [hz,div_self hf,mul_one]
  convert halg (R:ℂ) (horizonCoordinate (-L/2))
    (Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p*
      boundaryKernel q br amp w x k (-L/2)) hf hZ using 1 <;> ring

/-- The physical fourth-transfer density has its actual time integral throughout
the forcing convergence domain, with the unchanged onset transform. -/
theorem physical_metric_laplace (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwi : w.im≠0)
    (hw : (2*physicalRate q br).re<w.re) (L x k : ℝ) (hL : 0<L) :
    let R := D4BMJointWave.tortoiseRadius (-L/2)
    let f := (R:ℂ)^(2 : ℕ)-1
    IntegrableOn (fun p : ℝ => f*((-w*(R:ℂ))/f^(2 : ℕ)*
      D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k)) (Ioi (0:ℝ)) ∧
    (∫ p in Ioi (0:ℝ),f*((-w*(R:ℂ))/f^(2 : ℕ)*
      D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k))=
        -w*continuedOnset (physicalRate q br) w*boundaryKernel q br amp w x k (-L/2) := by
  dsimp only
  have he (p : ℝ) : ((D4BMJointWave.tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
      ((-w*(D4BMJointWave.tortoiseRadius (-L/2):ℂ))/
        ((D4BMJointWave.tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)^(2 : ℕ)*
          D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k)=
      (-w*boundaryKernel q br amp w x k (-L/2))*
        (Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p) := by
    rw [physical_metric_kernel q br amp w hwi p L x k hL]
    ring
  simp_rw [he]
  constructor
  · exact (timeOnset_integrable (2*physicalRate q br) w hw).const_mul _
  · rw [integral_const_mul,timeOnset_laplace,onsetTransform_eq (2*physicalRate q br) w hw]
    unfold continuedOnset
    ring

/-- The forcing time integral converges at both actual QNM frequencies. -/
theorem physical_metric_QNM_laplace (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    (L x k : ℝ) (hL : 0<L) :
    let w := physicalFundamentalFrequency q side
    let R := D4BMJointWave.tortoiseRadius (-L/2)
    let f := (R:ℂ)^(2 : ℕ)-1
    IntegrableOn (fun p : ℝ => f*((-w*(R:ℂ))/f^(2 : ℕ)*
      D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k)) (Ioi (0:ℝ)) ∧
    (∫ p in Ioi (0:ℝ),f*((-w*(R:ℂ))/f^(2 : ℕ)*
      D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k))=
        -w*continuedOnset (physicalRate q br) w*boundaryKernel q br amp w x k (-L/2) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  exact physical_metric_laplace q br amp (physicalFundamentalFrequency q side) hw.1
    (hs.trans (abs_lt.mp hw.2).1) L x k hL

/-- Finite source-time integration preserves the very same radial kernel. -/
theorem physical_metric_time_cut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwi : w.im≠0)
    (T L x k : ℝ) (hL : 0<L) :
    let R := D4BMJointWave.tortoiseRadius (-L/2)
    let f := (R:ℂ)^(2 : ℕ)-1
    (∫ p in (0:ℝ)..T,f*((-w*(R:ℂ))/f^(2 : ℕ)*
      D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k))=
        -w*(∫ p in (0:ℝ)..T,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
          boundaryKernel q br amp w x k (-L/2) := by
  dsimp only
  have he (p : ℝ) : ((D4BMJointWave.tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
      ((-w*(D4BMJointWave.tortoiseRadius (-L/2):ℂ))/
        ((D4BMJointWave.tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)^(2 : ℕ)*
          D4BMOriginalMetricForcingMatch.forcingTransferCut q br amp w p L x k)=
      (-w*boundaryKernel q br amp w x k (-L/2))*
        (Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p) := by
    rw [physical_metric_kernel q br amp w hwi p L x k hL]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem kernel_continuous (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    ContinuousOn (forcingKernel q br amp K w) (Iio (0:ℝ)) := by
  have hu : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hp : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Complex.continuousAt_ofReal_cpow_const (1+radialUnit x) (2*physicalRate q br)
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

theorem integral_two_kernels (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x k a b : ℝ)
    (ha : a<0) (hb : b<0) :
    (∫ t in a..b,boundaryKernel q br amp w x k t)=
      firstWeight q br x k*(∫ t in a..b,forcingKernel q br amp 0 w t)+
      secondWeight q br x k*(∫ t in a..b,forcingKernel q br amp 1 w t) := by
  simp_rw [boundary_two_kernels]
  rw [intervalIntegral.integral_add
    ((kernel_integrable q br amp 0 w ha hb).const_mul _)
    ((kernel_integrable q br amp 1 w ha hb).const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

private theorem fixed_product_joint_limit (q : XiZeroCopy) (br b : Bool) (X : ℝ×ℝ → ℝ) :
    Tendsto (fun z : ℝ×ℝ => fixedProduct q br b true (X z) z.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨B,hB,h⟩ := fixed_product_decay q br b true 1
  have he : Tendsto (fun z : ℝ×ℝ => B*Real.exp (-z.2))
      ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  have hk : ∀ᶠ z : ℝ×ℝ in ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)),0≤z.2 :=
    tendsto_snd.eventually (eventually_ge_atTop (0:ℝ))
  filter_upwards [hk] with z hz
  simpa only [Nat.cast_one,neg_one_mul] using h (X z) z.2 hz

/-- Both power counterterms and the logarithm retain the same finite-height
angular weights as the literal physical forcing boundary. -/
def radialCut (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c₀ c₁ d₀ e₀ e₁ f₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) (x : ℝ) (v : ℝ×ℝ) : ℂ :=
  (∫ t in tortoiseOf v.1..tortoiseOf b,boundaryKernel q br amp w x v.2 t)-
    (firstWeight q br x v.2*D4BMOriginalForcingJointHorizon.counterterm c₀ c₁ d₀ w v.1+
      secondWeight q br x v.2*D4BMOriginalForcingJointHorizon.counterterm e₀ e₁ f₀ w v.1)

/-- The original forcing boundary admits independent cusp/horizon restoration
through a neighborhood of either physical QNM. The restored boundary is zero. -/
theorem forcing_boundary_joint_QNM (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ R B : ℝ, ∃ c₀ c₁ d₀ e₀ e₁ f₀ : ℂ→ℂ,0<R ∧ 0<B ∧ B≤1/2 ∧
      ∀ b : ℝ,0<b → b≤B → ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
        ∀ X : ℝ×ℝ → ℝ,
          Tendsto (fun v : ℝ×ℝ => radialCut q br amp c₀ c₁ d₀ e₀ e₁ f₀ b w (X v) v)
            ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨R₀,B₀,c₀,c₁,d₀,hR₀,hB₀,hBh₀,h₀⟩ := forcing_horizon_restoration q br side amp 0
  obtain ⟨R₁,B₁,e₀,e₁,f₀,hR₁,hB₁,hBh₁,h₁⟩ := forcing_horizon_restoration q br side amp 1
  refine ⟨min R₀ R₁,min B₀ B₁,c₀,c₁,d₀,e₀,e₁,f₀,lt_min hR₀ hR₁,
    lt_min hB₀ hB₁,(min_le_left _ _).trans hBh₀,?_⟩
  intro b hb hbB w hw X
  have hb₀ := hbB.trans (min_le_left B₀ B₁)
  have hb₁ := hbB.trans (min_le_right B₀ B₁)
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨hb,lt_of_le_of_lt (hb₀.trans hBh₀) (by norm_num)⟩
  have hw₀ : w ∈ ball (physicalFundamentalFrequency q side) R₀ := ball_subset_ball (min_le_left _ _) hw
  have hw₁ : w ∈ ball (physicalFundamentalFrequency q side) R₁ := ball_subset_ball (min_le_right _ _) hw
  have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ),e ∈ Ioo (0:ℝ) b := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ),e<b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds]
      with e he heb
    exact ⟨he,heb⟩
  have ht (K : ℂ) (a₀ a₁ b₀ : ℂ→ℂ)
      (h : Tendsto (fun e : ℝ => (∫ z in e..b,pullback q br amp K w z)-
        a₀ w*(e:ℂ)^w/w-a₁ w*(e:ℂ)^(w+1)/(w+1)-b₀ w*(Real.log e:ℂ))
        (𝓝[>] (0:ℝ)) (𝓝 (horizonFinitePart q br amp K a₀ a₁ b₀ b w))) :
      Tendsto (fun e : ℝ => (∫ t in tortoiseOf e..tortoiseOf b,forcingKernel q br amp K w t)-
        D4BMOriginalForcingJointHorizon.counterterm a₀ a₁ b₀ w e)
        (𝓝[>] (0:ℝ)) (𝓝 (horizonFinitePart q br amp K a₀ a₁ b₀ b w)) := by
    apply h.congr'
    filter_upwards [he] with e he
    rw [forcing_radial_integral_pullback q br amp K w he.1 he.2.le hbI.2]
    unfold D4BMOriginalForcingJointHorizon.counterterm
    ring
  have ht₀ := ht 0 c₀ c₁ d₀ ((h₀ b hb hb₀).2 w hw₀)
  have ht₁ := ht 1 e₀ e₁ f₀ ((h₁ b hb hb₁).2 w hw₁)
  have hA : Tendsto (fun v : ℝ×ℝ => firstWeight q br (X v) v.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [firstWeight,sub_zero] using
      (fixed_product_joint_limit q br false X).sub (fixed_product_joint_limit q br true X)
  have hD := fixed_product_joint_limit q br true X
  change Tendsto (fun v : ℝ×ℝ => secondWeight q br (X v) v.2) _ (𝓝 0) at hD
  have h := (hA.mul (ht₀.comp tendsto_fst)).add (hD.mul (ht₁.comp tendsto_fst))
  simp only [zero_mul,add_zero] at h
  apply h.congr'
  have hv : ∀ᶠ v : ℝ×ℝ in ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)),v.1 ∈ Ioo (0:ℝ) b :=
    tendsto_fst.eventually he
  filter_upwards [hv] with v hv
  rw [radialCut,integral_two_kernels q br amp w (X v) v.2 _ _
    (tortoiseOf_neg ⟨hv.1,hv.2.trans hbI.2⟩) (tortoiseOf_neg hbI)]
  dsimp only [Function.comp_def]
  ring

/-- All three original cutoffs may be restored independently at the physical QNM.
The temporal factor multiplies the radial counterterms at the same finite time. -/
theorem physical_forcing_three_cutoff_QNM (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ B : ℝ, ∃ c₀ c₁ d₀ e₀ e₁ f₀ : ℂ→ℂ,0<B ∧ B≤1/2 ∧
      ∀ b : ℝ,0<b → b≤B → ∀ X : ℝ×ℝ → ℝ,
        let w := physicalFundamentalFrequency q side
        Tendsto (fun z : (ℝ×ℝ)×ℝ =>
          -w*(∫ p in (0:ℝ)..z.2,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
            radialCut q br amp c₀ c₁ d₀ e₀ e₁ f₀ b w (X z.1) z.1)
          (((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨R,B,c₀,c₁,d₀,e₀,e₁,f₀,hR,hB,hBh,h⟩ := forcing_boundary_joint_QNM q br side amp
  refine ⟨B,c₀,c₁,d₀,e₀,e₁,f₀,hB,hBh,?_⟩
  intro b hb hbB X
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hi := timeOnset_integrable (2*physicalRate q br) w (hs.trans (abs_lt.mp hw.2).1)
  have hT := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hi
    (tendsto_snd : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.2)
      (((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) ×ˢ (atTop : Filter ℝ)) atTop)
  have hS := (h b hb hbB w (mem_ball_self hR) X).comp
    (tendsto_fst : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.1)
      (((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) ×ˢ (atTop : Filter ℝ))
      ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)))
  simpa only [Function.comp_def,mul_zero] using (hT.const_mul (-w)).mul hS

end
end RHTower.D4BMOriginalForcingBoundaryQNM
