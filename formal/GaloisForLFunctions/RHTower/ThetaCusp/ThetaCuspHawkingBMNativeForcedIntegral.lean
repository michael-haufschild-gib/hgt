import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalGoursat
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalTimeForcing
import GaloisForLFunctions.HTGeometry.L2DominatedContinuity

/-! The native retarded integral of the original radial source. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMNativeResponse
open D4BMJointSource D4BMCausalKernel D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The actual reduced source vanishes at the original AdS endpoint at every time. -/
theorem source_boundary (s a : ℂ) (τ : ℝ) : timeReducedCoefficient s a τ 0 = 0 := by
  simp [timeReducedCoefficient,reducedCoefficient,reducedPolynomial,radialLiftFirst,
    liftFirstPolynomial,liftSecondPolynomial,radialUnit]

/-- Continuous odd representative of the original negative-ray source. -/
def oddSource (s a : ℂ) (τ x : ℝ) : ℂ :=
  timeReducedCoefficient s a τ (min x 0)-timeReducedCoefficient s a τ (min (-x) 0)

private theorem oddSource_negative (s a : ℂ) (τ x : ℝ) (hx : x ≤ 0) :
    oddSource s a τ x = timeReducedCoefficient s a τ x := by
  simp only [oddSource,min_eq_left hx,min_eq_right (neg_nonneg.mpr hx),source_boundary,sub_zero]

private theorem oddSource_odd (s a : ℂ) (τ x : ℝ) :
    oddSource s a τ (-x) = -oddSource s a τ x := by simp [oddSource]

private theorem oddSource_continuous (s a : ℂ) :
    Continuous (fun p : ℝ × ℝ => oddSource s a p.1 p.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s a).comp
    (show Continuous (fun p : ℝ × ℝ => (p.1,min p.2 0)) from
      continuous_fst.prodMk (continuous_snd.min continuous_const))
  have h₂ := (timeReducedCoefficient_joint_continuous s a).comp
    (show Continuous (fun p : ℝ × ℝ => (p.1,min (-p.2) 0)) from
      continuous_fst.prodMk (continuous_snd.neg.min continuous_const))
  convert! h₁.sub h₂ using 1

private theorem oddSource_zero_outside (s a : ℂ) (τ x : ℝ) (hx : max τ 0 < |x|) :
    oddSource s a τ x = 0 := by
  by_cases hn : x ≤ 0
  · rw [oddSource_negative s a τ x hn]
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonpos hn] at hx
    have := le_max_left τ 0
    linarith
  · have hp : 0 ≤ x := le_of_not_ge hn
    have hneg : oddSource s a τ (-x) = 0 := by
      rw [oddSource_negative s a τ (-x) (neg_nonpos.mpr hp)]
      apply timeReducedCoefficient_zero_before_onset
      rw [abs_of_nonneg hp] at hx
      have := le_max_left τ 0
      linarith
    rw [oddSource_odd] at hneg
    exact neg_eq_zero.mp hneg

private def extendedKernel (nu : ℂ) (h x y : ℝ) : ℂ :=
  legendreKernel nu (max 1 (invariant h x y))

private theorem extendedKernel_continuous (nu : ℂ) :
    Continuous (fun p : ℝ × ℝ × ℝ => extendedKernel nu p.1 p.2.1 p.2.2) := by
  have hz : Continuous (fun p : ℝ × ℝ × ℝ => invariant p.1 p.2.1 p.2.2) := by
    unfold invariant
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro p
      exact (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).ne'
  have hp : ContinuousOn (legendreKernel nu) (Ioi 0) := fun z hz =>
    (legendreKernel_derivatives nu hz).1.continuousAt.continuousWithinAt
  apply hp.comp_continuous (continuous_const.max hz)
  intro p
  change 0 < max 1 (invariant p.1 p.2.1 p.2.2)
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)

private theorem extendedKernel_eq (nu : ℂ) (h x y : ℝ) (hi : |x-y| ≤ h) :
    extendedKernel nu h x y = riemannKernel nu h x y := by
  simp only [extendedKernel,riemannKernel,max_eq_right (invariant_causal ⟨h,x,y,hi⟩)]

private theorem normalized_cone (τ x r z : ℝ) (hr : r ∈ Icc 0 1) (hz : z ∈ Icc (-1) 1) :
    |x-(x+max τ 0*(1-r)*z)| ≤ max τ 0*(1-r) := by
  have hh : 0 ≤ max τ 0*(1-r) := mul_nonneg (le_max_right _ _) (sub_nonneg.mpr hr.2)
  have hza : |z| ≤ 1 := abs_le.mpr hz
  rw [show x-(x+max τ 0*(1-r)*z) = -(max τ 0*(1-r)*z) by ring,abs_neg,abs_mul,
    abs_of_nonneg hh]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hza hh

/-- Original retarded integral in fixed rectangle coordinates; the factor includes both Jacobians. -/
def radialResponse (nu s a : ℂ) (τ x : ℝ) : ℂ :=
  ((max τ 0:ℝ):ℂ)^(2 : ℕ)/2*∫ r in (0:ℝ)..1, (1-r:ℂ)*
    ∫ z in (-1:ℝ)..1,
      riemannKernel nu (max τ 0*(1-r)) x (x+max τ 0*(1-r)*z)*
        oddSource s a (max τ 0*r) (x+max τ 0*(1-r)*z)

private theorem radialResponse_extended (nu s a : ℂ) (τ x : ℝ) :
    radialResponse nu s a τ x =
      ((max τ 0:ℝ):ℂ)^(2 : ℕ)/2*∫ r in (0:ℝ)..1, (1-r:ℂ)*
        ∫ z in (-1:ℝ)..1,
          extendedKernel nu (max τ 0*(1-r)) x (x+max τ 0*(1-r)*z)*
            oddSource s a (max τ 0*r) (x+max τ 0*(1-r)*z) := by
  unfold radialResponse
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  rw [extendedKernel_eq nu _ _ _ (normalized_cone τ x r z
    (by simpa using hr) (by simpa using hz))]

private def normalizedIntegrand (nu s a : ℂ) (τ x r z : ℝ) : ℂ :=
  extendedKernel nu (max τ 0*(1-r)) x (x+max τ 0*(1-r)*z)*
    oddSource s a (max τ 0*r) (x+max τ 0*(1-r)*z)

private theorem normalizedIntegrand_continuous (nu s a : ℂ) :
    Continuous (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      normalizedIntegrand nu s a p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hk := (extendedKernel_continuous nu).comp
    (show Continuous (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      (max p.1.1.1 0*(1-p.1.2),p.1.1.2,p.1.1.2+max p.1.1.1 0*(1-p.1.2)*p.2)) by fun_prop)
  have hf := (oddSource_continuous s a).comp
    (show Continuous (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      (max p.1.1.1 0*p.1.2,p.1.1.2+max p.1.1.1 0*(1-p.1.2)*p.2)) by fun_prop)
  convert! hk.mul hf using 1

/-- The integrated native response is jointly continuous, including zero time and the AdS endpoint. -/
theorem radialResponse_continuous (nu s a : ℂ) :
    Continuous (fun p : ℝ × ℝ => radialResponse nu s a p.1 p.2) := by
  have hi : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      ∫ z in (-1:ℝ)..1, normalizedIntegrand nu s a p.1.1 p.1.2 p.2 z) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (normalizedIntegrand_continuous nu s a) (-1) 1
  have hw : Continuous (fun p : (ℝ × ℝ) × ℝ => (1-p.2:ℂ)*
      ∫ z in (-1:ℝ)..1, normalizedIntegrand nu s a p.1.1 p.1.2 p.2 z) :=
    (continuous_const.sub (Complex.continuous_ofReal.comp continuous_snd)).mul hi
  have ho := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (p : ℝ × ℝ) r => (1-r:ℂ)*∫ z in (-1:ℝ)..1, normalizedIntegrand nu s a p.1 p.2 r z)
    hw 0 1
  simp_rw [radialResponse_extended]
  exact (show Continuous (fun p : ℝ × ℝ => ((max p.1 0:ℝ):ℂ)^(2 : ℕ)/2) by fun_prop).mul ho

/-- No native response precedes the original onset. -/
theorem radialResponse_zero_of_nonpos (nu s a : ℂ) (τ x : ℝ) (hτ : τ ≤ 0) :
    radialResponse nu s a τ x = 0 := by
  simp only [radialResponse,max_eq_right hτ,Complex.ofReal_zero,zero_pow (by decide : 2 ≠ 0),
    zero_div,zero_mul]

/-- The actual native response has finite propagation from the fixed source onset. -/
theorem radialResponse_zero_outside (nu s a : ℂ) (τ x : ℝ) (hx : max τ 0 < |x|) :
    radialResponse nu s a τ x = 0 := by
  unfold radialResponse
  suffices he : (∫ r in (0:ℝ)..1, (1-r:ℂ)*∫ z in (-1:ℝ)..1,
      riemannKernel nu (max τ 0*(1-r)) x (x+max τ 0*(1-r)*z)*
        oddSource s a (max τ 0*r) (x+max τ 0*(1-r)*z)) = 0 by rw [he,mul_zero]
  refine (intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_).trans (by simp)
  intro r hr
  dsimp only
  suffices he : (∫ z in (-1:ℝ)..1,
      riemannKernel nu (max τ 0*(1-r)) x (x+max τ 0*(1-r)*z)*
        oddSource s a (max τ 0*r) (x+max τ 0*(1-r)*z)) = 0 by rw [he,mul_zero]
  refine (intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_).trans (by simp)
  intro z hz
  dsimp only
  have hr' : r ∈ Icc 0 1 := by simpa using hr
  have hz' : z ∈ Icc (-1) 1 := by simpa using hz
  have hc := normalized_cone τ x r z hr' hz'
  have htri := abs_sub_le x (x+max τ 0*(1-r)*z) 0
  simp only [sub_zero] at htri
  have hs : 0 ≤ max τ 0*r := mul_nonneg (le_max_right _ _) hr'.1
  have ho : max (max τ 0*r) 0 < |x+max τ 0*(1-r)*z| := by
    rw [max_eq_left hs]
    nlinarith
  rw [oddSource_zero_outside s a _ _ ho,mul_zero]

private theorem radialResponse_compactSupport (nu s a : ℂ) (τ : ℝ) :
    HasCompactSupport (radialResponse nu s a τ) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  apply radialResponse_zero_outside
  by_contra h
  apply hx
  exact abs_le.mp (le_of_not_gt h)

/-- The original causal integral belongs to the whole-line L² space at every time. -/
theorem radialResponse_memLp (nu s a : ℂ) (τ : ℝ) : MemLp (radialResponse nu s a τ) 2 volume :=
  ((radialResponse_continuous nu s a).comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    (radialResponse_compactSupport nu s a τ)

/-- Actual L² class of the native retarded source integral. -/
def radialResponseVector (nu s a : ℂ) (τ : ℝ) : FourierRealL2 :=
  (radialResponse_memLp nu s a τ).toLp (radialResponse nu s a τ)

/-- The fixed rectangle formula is exactly the original retarded source integral. -/
theorem radialResponse_retarded (nu s a : ℂ) (τ x : ℝ) :
    radialResponse nu s a τ x = (1/2:ℂ)*∫ σ in (0:ℝ)..max τ 0,
      ∫ y in x-(max τ 0-σ)..x+(max τ 0-σ),
        riemannKernel nu (max τ 0-σ) x y*oddSource s a σ y := by
  let T := max τ 0
  let J (r : ℝ) := ∫ z in (-1:ℝ)..1,
    riemannKernel nu (T*(1-r)) x (x+T*(1-r)*z)*oddSource s a (T*r) (x+T*(1-r)*z)
  let F (σ : ℝ) := ∫ y in x-(T-σ)..x+(T-σ),
    riemannKernel nu (T-σ) x y*oddSource s a σ y
  have hi (r : ℝ) : F (T*r) = ((T:ℂ)*(1-r:ℂ))*J r := by
    have h := intervalIntegral.smul_integral_comp_add_mul
      (f := fun y => riemannKernel nu (T-T*r) x y*oddSource s a (T*r) y)
      (a := (-1:ℝ)) (b := 1) (T*(1-r)) x
    have he : T-T*r = T*(1-r) := by ring
    have hl : x+T*(1-r)*(-1) = x-(T-T*r) := by ring
    have hr : x+T*(1-r)*1 = x+(T-T*r) := by ring
    rw [hl,hr] at h
    change (T*(1-r)) • (∫ z in (-1:ℝ)..1,
      riemannKernel nu (T-T*r) x (x+T*(1-r)*z)*
        oddSource s a (T*r) (x+T*(1-r)*z)) = F (T*r) at h
    rw [he] at h
    simpa only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,J]
      using h.symm
  have ho := intervalIntegral.smul_integral_comp_mul_left (f := F) (a := (0:ℝ)) (b := 1) T
  simp only [mul_zero,mul_one,Complex.real_smul] at ho
  rw [show (fun r : ℝ => F (T*r)) = fun r : ℝ => (T:ℂ)*((1-r:ℂ)*J r) by
    funext r
    rw [hi]
    ring,intervalIntegral.integral_const_mul] at ho
  change (T:ℂ)^(2 : ℕ)/2*(∫ r in (0:ℝ)..1, (1-r:ℂ)*J r) = (1/2:ℂ)*∫ σ in (0:ℝ)..T, F σ
  rw [← ho]
  ring

private theorem kernel_reflection (nu : ℂ) (h x y : ℝ) :
    riemannKernel nu h (-x) (-y) = riemannKernel nu h x y := by
  simp [riemannKernel,invariant]

/-- The original native source integral preserves odd reflection exactly. -/
theorem radialResponse_odd (nu s a : ℂ) (τ x : ℝ) :
    radialResponse nu s a τ (-x) = -radialResponse nu s a τ x := by
  let T := max τ 0
  have hi (r : ℝ) :
      (∫ z in (-1:ℝ)..1,
        riemannKernel nu (T*(1-r)) (-x) (-x+T*(1-r)*z)*
          oddSource s a (T*r) (-x+T*(1-r)*z)) =
      -(∫ z in (-1:ℝ)..1,
        riemannKernel nu (T*(1-r)) x (x+T*(1-r)*z)*
          oddSource s a (T*r) (x+T*(1-r)*z)) := by
    have he (z : ℝ) : -x+T*(1-r)*z = -(x+T*(1-r)*(-z)) := by ring
    have hF : (fun z : ℝ =>
        riemannKernel nu (T*(1-r)) (-x) (-x+T*(1-r)*z)*
          oddSource s a (T*r) (-x+T*(1-r)*z)) =
        fun z => -(riemannKernel nu (T*(1-r)) x (x+T*(1-r)*(-z))*
          oddSource s a (T*r) (x+T*(1-r)*(-z))) := by
      funext z
      rw [he z,kernel_reflection,oddSource_odd,mul_neg]
    rw [hF,intervalIntegral.integral_neg]
    have hn := intervalIntegral.integral_comp_neg
      (f := fun z : ℝ => riemannKernel nu (T*(1-r)) x (x+T*(1-r)*z)*
        oddSource s a (T*r) (x+T*(1-r)*z)) (a := (-1:ℝ)) (b := 1)
    simpa only [neg_neg] using congrArg Neg.neg hn
  dsimp only [T] at hi
  unfold radialResponse
  simp_rw [hi,mul_neg]
  rw [intervalIntegral.integral_neg,mul_neg]

/-- The actual integral has zero Dirichlet trace at the original AdS endpoint. -/
theorem radialResponse_boundary (nu s a : ℂ) (τ : ℝ) : radialResponse nu s a τ 0 = 0 := by
  have h := radialResponse_odd nu s a τ 0
  simp only [neg_zero] at h
  linear_combination (1/2:ℂ)*h

private theorem continuous_Lp_of_coneSupport (f : ℝ → ℝ → ℂ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hz : ∀ τ x, max τ 0 < |x| → f τ x = 0)
    (hL : ∀ τ, MemLp (f τ) 2 volume) :
    Continuous (fun τ => (hL τ).toLp (f τ)) := by
  apply continuous_iff_continuousAt.mpr
  intro τ₀
  let L := τ₀-1
  let H := τ₀+1
  let R := max H 0
  let c (τ : ℝ) := min (max τ L) H
  have hLH : L ≤ H := by dsimp [L,H]; linarith
  have hcm (τ : ℝ) : c τ ∈ Icc L H :=
    ⟨le_min (le_max_right _ _) hLH,min_le_right _ _⟩
  have hcc : Continuous c := (continuous_id.max continuous_const).min continuous_const
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc L H ×ˢ Icc (-R) R) hf.continuousOn
  let b : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => max C 0)
  have hb : MemLp b 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr (memLp_const _)
  have hbound (τ : ℝ) : ∀ᵐ x : ℝ ∂volume, ‖f (c τ) x‖ ≤ b x := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ Icc (-R) R
    · rw [show b x = max C 0 from indicator_of_mem hx _]
      exact (hC (c τ,x) ⟨hcm τ,hx⟩).trans (le_max_left _ _)
    · have hxa : R < |x| := by
        apply lt_of_not_ge
        intro h
        exact hx (abs_le.mp h)
      have ht : max (c τ) 0 ≤ R := max_le_max (hcm τ).2 le_rfl
      rw [hz _ _ (ht.trans_lt hxa),norm_zero,
        show b x = 0 from indicator_of_notMem hx _]
  have hc := continuous_toLp_two_of_dominated volume
    (fun τ x => f (c τ) x) (fun τ => hL (c τ))
    b hb hbound (Eventually.of_forall fun x =>
      hf.comp (hcc.prodMk continuous_const))
  change Continuous (fun τ => (hL (c τ)).toLp (f (c τ))) at hc
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (show L < τ₀ by dsimp [L]; linarith)
    (show τ₀ < H by dsimp [H]; linarith)] with τ hτ
  have he : c τ = τ := by
    dsimp only [c]
    rw [max_eq_left hτ.1.le,min_eq_left hτ.2.le]
  rw [he]

/-- The actual L² integral is strongly continuous in static time. -/
theorem radialResponseVector_continuous (nu s a : ℂ) : Continuous (radialResponseVector nu s a) := by
  exact continuous_Lp_of_coneSupport (radialResponse nu s a)
    (radialResponse_continuous nu s a) (radialResponse_zero_outside nu s a)
    (radialResponse_memLp nu s a)

private theorem oddSource_ae_extension (s a : ℂ) (τ : ℝ) :
    negativeOddExtension (timeRadialSourceVector s a τ) =ᵐ[volume] oddSource s a τ := by
  let f := timeRadialSourceVector s a τ
  have he := (ae_restrict_iff' measurableSet_Iio).mp (timeRadialSourceVector_ae s a τ)
  have hz : negativeZeroExtension f =ᵐ[volume]
      (fun x => timeReducedCoefficient s a τ (min x 0)) := by
    filter_upwards [negativeZeroExtension_ae f,he] with x hx he
    rw [hx]
    by_cases hn : x < 0
    · change (Iio (0:ℝ)).indicator (⇑f) x = _
      rw [indicator_of_mem (show x ∈ Iio (0:ℝ) from hn),min_eq_left hn.le]
      exact he hn
    · change (Iio (0:ℝ)).indicator (⇑f) x = _
      rw [indicator_of_notMem (show x ∉ Iio (0:ℝ) from hn),
        min_eq_right (le_of_not_gt hn),source_boundary]
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hz
  have hr : l2Reflection (negativeZeroExtension f) =ᵐ[volume]
      (fun x : ℝ => negativeZeroExtension f (-x)) :=
    Lp.coeFn_compMeasurePreserving (negativeZeroExtension f)
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hs := Lp.coeFn_sub (negativeZeroExtension f) (l2Reflection (negativeZeroExtension f))
  filter_upwards [hz,hn,hr,hs] with x hz hn hr hs
  change (negativeZeroExtension f-l2Reflection (negativeZeroExtension f)) x = _
  rw [hs]
  change negativeZeroExtension f x-l2Reflection (negativeZeroExtension f) x = _
  rw [hz,hr,hn]
  rfl

/-- The integrand's source is the original constructed principal forcing in the actual L² quotient. -/
theorem principalForcing_ae_oddSource (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    principalTimeForcing q branch a i τ =ᵐ[volume]
      (fun x => principalAmplitude q i*oddSource (physicalRate q branch) a τ x) := by
  filter_upwards [oddSource_ae_extension (physicalRate q branch) a τ,
    Lp.coeFn_smul (principalAmplitude q i)
      (negativeOddExtension (timeRadialSourceVector (physicalRate q branch) a τ))] with x hx hs
  change (principalAmplitude q i •
    negativeOddExtension (timeRadialSourceVector (physicalRate q branch) a τ)) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hx]

/-- Native causal integral in each of the three original principal channels. -/
def nativePrincipalResponse (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) (τ : ℝ) :
    FourierRealL2 :=
  principalAmplitude q i • radialResponseVector (-principalExponent q i) (physicalRate q branch) a τ

/-- All three original channel integrals form strongly continuous L² families. -/
theorem nativePrincipalResponse_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3) :
    Continuous (nativePrincipalResponse q branch a i) := by
  change Continuous (fun τ => principalAmplitude q i •
    radialResponseVector (-principalExponent q i) (physicalRate q branch) a τ)
  exact (continuous_const : Continuous (fun _ : ℝ => principalAmplitude q i)).smul
    (radialResponseVector_continuous (-principalExponent q i) (physicalRate q branch) a)

end
end RHTower.D4BMNativeResponse
