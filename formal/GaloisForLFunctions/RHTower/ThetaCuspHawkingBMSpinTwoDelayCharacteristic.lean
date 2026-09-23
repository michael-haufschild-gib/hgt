import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeSpinTwoPrimitive
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedOpticalTail

/-! Original spin-two characteristic transfer in the physical delay coordinate. -/
namespace RHTower.D4BMSpinTwoDelay
open D4BMNativeSpinTwoPrimitive D4BMNativeCircle D4BMNativeResponse D4BMModularCore D4BMGlobalAngularResponse
open D4BMCommonSourceGreen D4BMCausalKernel D4BMJointSource D4BMHorizon
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private abbrev Point := Fin 3 → ℝ
private def D (i : Fin 3) (f : Point → ℂ) (p : Point) : ℂ :=
  fderiv ℝ f p (Pi.single i 1)
private theorem D_smooth {f : Point → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (D i f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem laplace_smooth (q : XiZeroCopy) (n : ℕ) : ContDiff ℝ ∞ (laplaceMean q n) := by
  induction n with
  | zero =>
    change ContDiff ℝ ∞ (fun p : Point => mean q (p 0) (p 1) (p 2))
    simpa only [Function.comp_def] using! (nativeMean_joint_smooth q).comp
      (show ContDiff ℝ ∞ (fun p : Point => (p 0,p 1,p 2)) by fun_prop)
  | succ n ih =>
    change ContDiff ℝ ∞ (fun p : Point => Complex.exp (2*(p 2:ℂ))*D 1 (D 1 (laplaceMean q n)) p+
      D 2 (D 2 (laplaceMean q n)) p-D 2 (laplaceMean q n) p)
    have he : ContDiff ℝ ∞ (fun p : Point => Complex.exp (2*(p 2:ℂ))) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (2:Fin 3)))).cexp
    exact ((he.mul (D_smooth (D_smooth ih 1) 1)).add (D_smooth (D_smooth ih 2) 2)).sub (D_smooth ih 2)

private theorem spin_continuous (q : XiZeroCopy) (X k : ℝ) :
    ContinuousOn (fun z => spinTwo q z X k) (Ici 1) := by
  have hc (n : ℕ) : ContinuousOn (fun z => argument q n z X k) (Ici 1) := by
    apply (laplace_smooth q n).continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · simpa using Real.continuousOn_arcosh
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => X) (Ici 1))
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => k) (Ici 1))
  exact (hc 2).neg.add (continuousOn_const.mul (hc 1))

private def closedSpin (q : XiZeroCopy) (X k z : ℝ) : ℂ := spinTwo q (max 1 z) X k
private theorem closedSpin_continuous (q : XiZeroCopy) (X k : ℝ) : Continuous (closedSpin q X k) :=
  (spin_continuous q X k).comp_continuous (continuous_const.max continuous_id)
    (fun z => by change (1:ℝ) ≤ max 1 z; exact le_max_left _ _)

/-- Original spin-two rescaled zeroth moment. -/
def firstMoment (q : XiZeroCopy) (X k z : ℝ) : ℂ :=
  -∫ t in (0:ℝ)..1, closedSpin q X k (1+t*(z-1))
/-- Original spin-two rescaled first moment. -/
def secondMoment (q : XiZeroCopy) (X k z : ℝ) : ℂ :=
  -∫ t in (0:ℝ)..1, (1-(t:ℂ))*closedSpin q X k (1+t*(z-1))

private theorem moments_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (firstMoment q X k) ∧ Continuous (secondMoment q X k) := by
  have hc : Continuous (fun p : ℝ × ℝ => closedSpin q X k (1+p.2*(p.1-1))) :=
    (closedSpin_continuous q X k).comp (by fun_prop)
  constructor
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun z t => closedSpin q X k (1+t*(z-1))) hc continuous_const).neg
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun z t => (1-(t:ℂ))*closedSpin q X k (1+t*(z-1)))
        ((by fun_prop : Continuous (fun p : ℝ × ℝ => (1:ℂ)-(p.2:ℂ))).mul hc) continuous_const).neg

private theorem closedSpin_segment (q : XiZeroCopy) (X k : ℝ) {z t : ℝ}
    (hz : 1 ≤ z) (ht : t ∈ Icc (0:ℝ) 1) :
    closedSpin q X k (1+t*(z-1))=spinTwo q (1+t*(z-1)) X k := by
  have h : 1 ≤ 1+t*(z-1) := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hz)]
  simp only [closedSpin,max_eq_right h]

/-- Both primitives factor by their exact original-source moment and characteristic power. -/
theorem primitive_factor (q : XiZeroCopy) (X k : ℝ) (z : Ici (1:ℝ)) :
    primitive q X k z=(z.val-1:ℂ)^(2 : ℕ)*secondMoment q X k z ∧
    primitiveFirst q X k z=(z.val-1:ℂ)*firstMoment q X k z := by
  have hs (f : ℝ → ℂ) :
      ((z.val-1:ℝ):ℂ)*(∫ t in (0:ℝ)..1, f (1+t*(z.val-1)))=∫ r in (1:ℝ)..z.val, f r := by
    have h := intervalIntegral.smul_integral_comp_add_mul f (a := 0) (b := 1) (z.val-1) 1
    simpa [Complex.real_smul,mul_comm] using h
  have he0 : (∫ t in (0:ℝ)..1, closedSpin q X k (1+t*(z.val-1)))=
      ∫ t in (0:ℝ)..1, spinTwo q (1+t*(z.val-1)) X k := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact closedSpin_segment q X k z.property (by simpa using ht)
  have he1 : (∫ t in (0:ℝ)..1, ((z.val:ℂ)-(1+t*(z.val-1):ℝ))*spinTwo q (1+t*(z.val-1)) X k)=
      (z.val-1:ℂ)*(∫ t in (0:ℝ)..1, (1-(t:ℂ))*closedSpin q X k (1+t*(z.val-1))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [closedSpin_segment q X k z.property (by simpa using ht)]
    push_cast
    ring
  constructor
  · rw [primitive_volterra,← hs (fun r => ((z.val:ℂ)-(r:ℂ))*spinTwo q r X k),he1]
    dsimp [secondMoment]
    push_cast
    ring
  · rw [primitiveFirst_integral,← hs (fun r => spinTwo q r X k)]
    dsimp [firstMoment]
    rw [he0]
    push_cast
    ring

/-- The two normalized moments have their literal full-source characteristic values. -/
theorem moments_at_one (q : XiZeroCopy) (X k : ℝ) :
    firstMoment q X k 1=-spinTwo q 1 X k ∧
    secondMoment q X k 1=-spinTwo q 1 X k/2 := by
  constructor
  · simp [firstMoment,closedSpin]
  · simp only [secondMoment,sub_self,mul_zero,add_zero,closedSpin,max_self]
    rw [intervalIntegral.integral_mul_const]
    have hi : (∫ t in (0:ℝ)..1, (1-(t:ℂ)))=(1:ℂ)/2 := by
      have hd (t : ℝ) : HasDerivAt (fun r : ℝ => (r:ℂ)-(r:ℂ)^(2 : ℕ)/2) (1-(t:ℂ)) t := by
        apply (((hasDerivAt_id t).ofReal_comp).sub (((hasDerivAt_id t).ofReal_comp.pow 2).div_const 2)).congr_deriv
        simp only [id_eq,Complex.ofReal_one]
        ring
      have hi : IntervalIntegrable (fun t : ℝ => (1:ℂ)-(t:ℂ)) volume 0 1 :=
        (by fun_prop : Continuous (fun t : ℝ => (1:ℂ)-(t:ℂ))).intervalIntegrable 0 1
      convert intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi using 1; norm_num
    rw [hi]
    ring

section
variable {E P K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [T2Space K] {μ : Measure K} [IsLocallyFiniteMeasure μ]
  {S : Set K} (hS : IsCompact S) (gamma : K → P) (hgamma : Continuous gamma)

private def partialMap {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E × P → G) (p : E × P) : E →L[ℝ] G :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E P)

omit [FiniteDimensional ℝ E] in
private theorem partialMap_smooth {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × P → G} {n : ℕ} (hf : ContDiff ℝ (n+1) f) :
    ContDiff ℝ n (partialMap f) := by
  have hh : ContDiff ℝ ((n : WithTop ℕ∞)+1) f := by exact_mod_cast hf
  exact (hh.fderiv_right le_rfl).clm_comp contDiff_const

omit [FiniteDimensional ℝ E] in
private theorem partialMap_derivative {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × P → G} (hf : ContDiff ℝ 1 f) (x : E) (p : P) :
    HasFDerivAt (fun y => f (y,p)) (partialMap f (x,p)) x := by
  exact ((hf.differentiable (by norm_num) (x,p)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const p x))

include hS hgamma in
private theorem compact_integral_first {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ 1 f) (x : E) :
    HasFDerivAt (fun y => ∫ k in S, f (y,gamma k) ∂μ)
      (∫ k in S, partialMap f (x,gamma k) ∂μ) x := by
  have hc : Continuous (fun q : E × K => f (q.1,gamma q.2)) :=
    hf.continuous.comp (continuous_fst.prodMk (hgamma.comp continuous_snd))
  have hd : Continuous (fun q : E × K => partialMap f (q.1,gamma q.2)) :=
    (partialMap_smooth (n := 0) hf).continuous.comp
      (continuous_fst.prodMk (hgamma.comp continuous_snd))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod hS).exists_bound_of_continuousOn hd.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y =>
      ((hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict)
  · exact ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn).integrableOn_compact hS
  · exact ((hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with k hk
    intro y hy
    exact hC (y,k) ⟨hy,hk⟩
  · exact integrableOn_const hS.measure_ne_top
  · exact Eventually.of_forall (fun k y _ => partialMap_derivative hf y (gamma k))

include hS hgamma in
private theorem compact_integral_smooth (n : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {f : E × P → G}, ContDiff ℝ n f →
      ContDiff ℝ n (fun y => ∫ k in S, f (y,gamma k) ∂μ) := by
  induction n with
  | zero =>
    intro G _ _ _ f hf
    apply contDiff_zero.mpr
    apply continuous_parametric_integral_of_continuous _ hS
    exact hf.continuous.comp (continuous_fst.prodMk (hgamma.comp continuous_snd))
  | succ n ih =>
    intro G _ _ _ f hf
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨(fun x => ∫ k in S, partialMap f (x,gamma k) ∂μ),?_,?_⟩
    · exact ih (partialMap_smooth hf)
    · intro x
      exact compact_integral_first hS gamma hgamma hf1 x

include hS hgamma in
private theorem compact_integral_infty {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => ∫ k in S, f (y,gamma k) ∂μ) :=
  contDiff_infty.mpr (fun n => compact_integral_smooth hS gamma hgamma n (contDiff_infty.mp hf n))

private theorem interval_integral_infty {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : E × P → G} (hf : ContDiff ℝ ∞ f)
    (γ : ℝ → P) (hγ : Continuous γ) (a b : ℝ) :
    ContDiff ℝ ∞ (fun y => ∫ k in a..b, f (y,γ k)) := by
  have h := compact_integral_infty (μ := volume) (S := uIcc a b) isCompact_uIcc γ hγ hf
  have he (y : E) : (∫ k in a..b, f (y,γ k)) =
      (if a ≤ b then (1 : ℝ) else -1) • ∫ k in uIcc a b, f (y,γ k) := by
    by_cases hab : a ≤ b
    · simp [hab, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    · have hba : b ≤ a := le_of_not_ge hab
      simp [hab, uIcc_of_ge hba, intervalIntegral.integral_of_ge hba, integral_Icc_eq_integral_Ioc]
  simpa only [he] using h.const_smul (if a ≤ b then (1 : ℝ) else -1)


end
/-- Fixed-onset reduced source profile, retaining the onset derivative. -/
def clockProfile (s : ℂ) (u v : ℝ) : ℂ :=
  Complex.exp (2*s*(v:ℂ))*((2*s+1)*(2*s+2)*(Real.smoothTransition v:ℂ)-
    (s*(s-1)/2*(u:ℂ)*(3+(2*s+3)*(u:ℂ))/(1+(u:ℂ)))*((deriv Real.smoothTransition v:ℝ):ℂ))

private theorem profile_smooth (s : ℂ) (u : ℝ) : ContDiff ℝ ∞ (clockProfile s u) := by
  have hc : ContDiff ℝ ∞ (fun v : ℝ => (Real.smoothTransition v:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff
  have hd : ContDiff ℝ ∞ (fun v : ℝ => ((deriv Real.smoothTransition v:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2)
  have he : ContDiff ℝ ∞ (fun v : ℝ => Complex.exp (2*s*(v:ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  exact he.mul ((contDiff_const.mul hc).sub (contDiff_const.mul hd))

private theorem profile_zero (s : ℂ) (u : ℝ) : clockProfile s u 0=0 := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    GaloisForLFunctions.HTGeometry.continuous_deriv_smoothTransition
  have he : (deriv Real.smoothTransition)=ᶠ[𝓝[<] (0:ℝ)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem
      (show v ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hv h.1)
  have hz : deriv Real.smoothTransition 0=0 :=
    tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' he.symm)
  simp [clockProfile,hz,Real.smoothTransition.zero]

/-- This profile is exactly the original reduced wave-image source coefficient. -/
theorem clockProfile_original (s a : ℂ) (tau x : ℝ) :
    timeReducedCoefficient s a tau x=
      -(radialUnit x:ℂ)*(1-(radialUnit x:ℂ)^(2 : ℕ))*sourceAmplitude s 0 a 1 x*
        clockProfile s (radialUnit x) (tau+x) := by
  rw [D4BMReducedOpticalTail.timeReducedCoefficient_closed]
  have hu : 1+(radialUnit x:ℂ) ≠ 0 := by
    exact_mod_cast (radialUnit_add_one_pos x).ne'
  dsimp [clockProfile]
  field_simp [hu]
  ring

private def clockMoment (q : XiZeroCopy) (branch : Bool) (u w V h : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, clockProfile (physicalRate q branch) u (h+(V-h)*t)*
    clockProfile (-physicalRate q branch-3) w ((V-h)*t)

/-- Original finite two-source clock density in rescaled interval form. -/
def clockDensity (q : XiZeroCopy) (branch : Bool) (u w V h : ℝ) : ℂ :=
  (V-h:ℂ)*clockMoment q branch u w V h

private theorem clockMoment_smooth (q : XiZeroCopy) (branch : Bool) (u w V : ℝ) :
    ContDiff ℝ ∞ (clockMoment q branch u w V) := by
  have h1 := (profile_smooth (physicalRate q branch) u).comp
    (show ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1+(V-p.1)*p.2) by fun_prop)
  have h2 := (profile_smooth (-physicalRate q branch-3) w).comp
    (show ContDiff ℝ ∞ (fun p : ℝ × ℝ => (V-p.1)*p.2) by fun_prop)
  exact interval_integral_infty (h1.mul h2) id continuous_id 0 1

private theorem clock_smooth (q : XiZeroCopy) (branch : Bool) (u w V : ℝ) :
    ContDiff ℝ ∞ (clockDensity q branch u w V) :=
  (contDiff_const.sub Complex.ofRealCLM.contDiff).mul (clockMoment_smooth q branch u w V)

/-- The density retains the original moving terminal endpoint and both fixed-onset sources. -/
theorem clockDensity_original (q : XiZeroCopy) (branch : Bool) (u w V h : ℝ) :
    clockDensity q branch u w V h=
      ∫ v in (0:ℝ)..(V-h), clockProfile (physicalRate q branch) u (v+h)*
        clockProfile (-physicalRate q branch-3) w v := by
  have hs := intervalIntegral.smul_integral_comp_add_mul
    (fun v => clockProfile (physicalRate q branch) u (v+h)*clockProfile (-physicalRate q branch-3) w v)
    (a := 0) (b := 1) (V-h) 0
  simpa [clockDensity,clockMoment,Complex.real_smul,add_comm] using hs

private theorem clock_derivatives (q : XiZeroCopy) (branch : Bool) (u w V h : ℝ) :
    HasDerivAt (clockDensity q branch u w V) (deriv (clockDensity q branch u w V) h) h ∧
    HasDerivAt (deriv (clockDensity q branch u w V)) (deriv (deriv (clockDensity q branch u w V)) h) h := by
  have hf := clock_smooth q branch u w V
  exact ⟨(hf.differentiable (by simp) h).hasDerivAt,
    (((contDiff_infty_iff_deriv.mp hf).2).differentiable (by simp) h).hasDerivAt⟩

/-- Both terminal clock jets vanish by the original earlier source's flat onset. -/
theorem clockDensity_terminal (q : XiZeroCopy) (branch : Bool) (u w V : ℝ) :
    clockDensity q branch u w V V=0 ∧ deriv (clockDensity q branch u w V) V=0 := by
  have hm : clockMoment q branch u w V V=0 := by
    simp [clockMoment,profile_zero]
  have hd := (((hasDerivAt_id V).ofReal_comp).const_sub (V:ℂ)).mul
    ((clockMoment_smooth q branch u w V).differentiable (by simp) V).hasDerivAt
  constructor
  · simp [clockDensity]
  · change deriv (fun h : ℝ => (V-h:ℂ)*clockMoment q branch u w V h) V=0
    simpa only [Pi.mul_apply,id_eq,hm,mul_zero,sub_self,zero_mul,add_zero] using! hd.deriv

private def Z (x h : ℝ) : ℝ := invariant h x x
private def A (x h : ℝ) : ℝ := Real.sinh h/Real.cosh x^(2 : ℕ)
private def B (x h : ℝ) : ℝ := Real.cosh h/Real.cosh x^(2 : ℕ)
private def ratioOne (h : ℝ) : ℝ := Real.sinh h/(Real.cosh h+1)
private def ratioTwo (x h : ℝ) : ℝ := Real.cosh x^(2 : ℕ)/(Real.cosh h+1)

private theorem Z_eq (x h : ℝ) : Z x h=1+(Real.cosh h-1)/Real.cosh x^(2 : ℕ) := by
  have hc := (Real.cosh_pos x).ne'
  unfold Z invariant
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]
private theorem Z_closed (x h : ℝ) : 1 ≤ Z x h := by
  rw [Z_eq]
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (Real.one_le_cosh h)) (sq_nonneg _))
private theorem Z_interior (x : ℝ) {h : ℝ} (hh : 0 < h) : 1 < Z x h := by
  rw [Z_eq]
  exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr (Real.one_lt_cosh.mpr hh.ne')) (sq_pos_of_pos (Real.cosh_pos x)))
private theorem A_pos (x : ℝ) {h : ℝ} (hh : 0 < h) : 0 < A x h :=
  div_pos (Real.sinh_pos_iff.mpr hh) (sq_pos_of_pos (Real.cosh_pos x))
private theorem geometry_continuous (x : ℝ) : Continuous (Z x) ∧ Continuous (A x) ∧
    Continuous (B x) ∧ Continuous ratioOne ∧ Continuous (ratioTwo x) := by
  have hden (h : ℝ) : Real.cosh h+1 ≠ 0 := by linarith [Real.cosh_pos h]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact continuous_iff_continuousAt.mpr (fun h => (invariant_time_derivatives h x x).1.continuousAt)
  · exact Real.continuous_sinh.div_const _
  · exact Real.continuous_cosh.div_const _
  · exact Real.continuous_sinh.div (Real.continuous_cosh.add continuous_const) hden
  · exact continuous_const.div (Real.continuous_cosh.add continuous_const) hden

private theorem geometry_derivatives (x h : ℝ) :
    HasDerivAt (Z x) (A x h) h ∧ HasDerivAt (A x) (B x h) h ∧ HasDerivAt (B x) (A x h) h := by
  refine ⟨?_,(Real.hasDerivAt_sinh h).div_const _,(Real.hasDerivAt_cosh h).div_const _⟩
  simpa only [Z,A,invariantTimeFirst,pow_two] using! (invariant_time_derivatives h x x).1

/-- Original direct physical spin-two trace in the coincident-radius delay chart. -/
theorem diagonal_original_trace (q : XiZeroCopy) (x h X k : ℝ) :
    nativeSpinTwoTrace false q h x ![x,X,k]=spinTwo q (invariant h x x) X k := by
  rw [nativeSpinTwoTrace_eq]
  simp

private theorem diagonal_ratios (x : ℝ) {h : ℝ} (hh : 0 < h) :
    (Z x h-1)/A x h=ratioOne h ∧ (Z x h-1)/(A x h)^(2 : ℕ)=ratioTwo x h := by
  have hc := (Real.cosh_pos x).ne'
  have hs := (Real.sinh_pos_iff.mpr hh).ne'
  have hp : Real.cosh h+1 ≠ 0 := by linarith [Real.cosh_pos h]
  have he : Real.sinh h^(2 : ℕ)=(Real.cosh h-1)*(Real.cosh h+1) := by
    nlinarith [Real.cosh_sq_sub_sinh_sq h]
  rw [Z_eq]
  dsimp [A,ratioOne,ratioTwo]
  constructor <;> field_simp [hc,hs,hp] <;> nlinarith [he]

private abbrev W (q : XiZeroCopy) (branch : Bool) (x V : ℝ) :=
  clockDensity q branch (radialUnit x) (radialUnit x) V

/-- The actual twice-transposed source-delay boundary expression on the direct diagonal. -/
def diagonalCurrent (q : XiZeroCopy) (branch : Bool) (x V X k h : ℝ) : ℂ :=
  -W q branch x V h*primitiveFirst q X k (Z x h)/(A x h:ℂ)+
    (deriv (W q branch x V) h/(A x h:ℂ)^(2 : ℕ)-
      W q branch x V h*(B x h:ℂ)/(A x h:ℂ)^(3 : ℕ))*primitive q X k (Z x h)

/-- The complete twice-transposed finite source bulk, including both onset derivatives. -/
def diagonalBulk (q : XiZeroCopy) (branch : Bool) (x V X k h : ℝ) : ℂ :=
  primitive q X k (Z x h)*(deriv (deriv (W q branch x V)) h/(A x h:ℂ)^(2 : ℕ)-
    3*(B x h:ℂ)*deriv (W q branch x V) h/(A x h:ℂ)^(3 : ℕ)+
    (3*(B x h:ℂ)^(2 : ℕ)-(A x h:ℂ)^(2 : ℕ))*W q branch x V h/(A x h:ℂ)^(4 : ℕ))

private def regularCurrent (q : XiZeroCopy) (branch : Bool) (x V X k h : ℝ) : ℂ :=
  -W q branch x V h*(ratioOne h:ℂ)*firstMoment q X k (Z x h)+
    (deriv (W q branch x V) h*(ratioOne h:ℂ)^(2 : ℕ)-
      W q branch x V h*(B x h:ℂ)*(ratioOne h:ℂ)*(ratioTwo x h:ℂ))*secondMoment q X k (Z x h)
private def regularBulk (q : XiZeroCopy) (branch : Bool) (x V X k h : ℝ) : ℂ :=
  (ratioOne h:ℂ)^(2 : ℕ)*secondMoment q X k (Z x h)*deriv (deriv (W q branch x V)) h-
    3*(B x h:ℂ)*(ratioOne h:ℂ)*(ratioTwo x h:ℂ)*secondMoment q X k (Z x h)*deriv (W q branch x V) h+
    (3*(B x h:ℂ)^(2 : ℕ)-(A x h:ℂ)^(2 : ℕ))*(ratioTwo x h:ℂ)^(2 : ℕ)*secondMoment q X k (Z x h)*W q branch x V h

private theorem regular_eq (q : XiZeroCopy) (branch : Bool) (x V X k : ℝ) {h : ℝ} (hh : 0 < h) :
    diagonalCurrent q branch x V X k h=regularCurrent q branch x V X k h ∧
    diagonalBulk q branch x V X k h=regularBulk q branch x V X k h := by
  obtain ⟨hJ,hJ1⟩ := primitive_factor q X k ⟨Z x h,(Z_closed x h)⟩
  change primitive q X k (Z x h)=_ at hJ
  change primitiveFirst q X k (Z x h)=_ at hJ1
  obtain ⟨hr,ht⟩ := diagonal_ratios x hh
  have hr' : ((Z x h:ℂ)-1)/(A x h:ℂ)=(ratioOne h:ℂ) := by exact_mod_cast hr
  have ht' : ((Z x h:ℂ)-1)/(A x h:ℂ)^(2 : ℕ)=(ratioTwo x h:ℂ) := by exact_mod_cast ht
  have ha : (A x h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (A_pos x hh).ne'
  constructor
  · dsimp [diagonalCurrent,regularCurrent]
    rw [hJ,hJ1,← hr',← ht']
    field_simp [ha]
  · dsimp [diagonalBulk,regularBulk]
    rw [hJ,← hr',← ht']
    field_simp [ha]

private theorem regular_continuous (q : XiZeroCopy) (branch : Bool) (x V X k : ℝ) :
    Continuous (regularCurrent q branch x V X k) ∧ Continuous (regularBulk q branch x V X k) := by
  obtain ⟨hZ,hA,hB,hr,ht⟩ := geometry_continuous x
  have hU := (moments_continuous q X k).2.comp hZ
  have hF := (moments_continuous q X k).1.comp hZ
  have hw := clock_smooth q branch (radialUnit x) (radialUnit x) V
  have hw1 := (contDiff_infty_iff_deriv.mp hw).2
  have hw2 := (contDiff_infty_iff_deriv.mp hw1).2
  have h0 : Continuous (W q branch x V) := hw.continuous
  have h1 : Continuous (deriv (W q branch x V)) := hw1.continuous
  have h2 : Continuous (deriv (deriv (W q branch x V))) := hw2.continuous
  have hrC := Complex.continuous_ofReal.comp hr
  have htC := Complex.continuous_ofReal.comp ht
  have hAC := Complex.continuous_ofReal.comp hA
  have hBC := Complex.continuous_ofReal.comp hB
  constructor
  · exact ((h0.neg.mul hrC).mul hF).add
      (((h1.mul (hrC.pow 2)).sub (((h0.mul hBC).mul hrC).mul htC)).mul hU)
  · exact ((((hrC.pow 2).mul hU).mul h2).sub
      (((((hBC.const_mul (3:ℂ)).mul hrC).mul htC).mul hU).mul h1)).add
        (((((hBC.pow 2).const_mul (3:ℂ)).sub (hAC.pow 2)).mul (htC.pow 2)).mul hU |>.mul h0)

private theorem regular_zero (q : XiZeroCopy) (branch : Bool) (x V X k : ℝ) :
    regularCurrent q branch x V X k 0=0 ∧
    regularBulk q branch x V X k 0=-(3:ℂ)/8*spinTwo q 1 X k*W q branch x V 0 := by
  have hc : (Real.cosh x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos x).ne'
  have hz0 : Z x 0=1 := by simp [Z_eq]
  constructor
  · simp [regularCurrent,ratioOne]
  · simp only [regularBulk,hz0,ratioOne,ratioTwo,A,B,Real.cosh_zero,Real.sinh_zero,
      zero_div,zero_pow (by decide : 2 ≠ 0),Complex.ofReal_zero,zero_mul,mul_zero,
      sub_zero,zero_add,
      (moments_at_one q X k).2]
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_one,Complex.ofReal_add]
    field_simp [hc]; ring

/-- The original boundary vanishes, while the transformed bulk retains its exact diagonal contact. -/
theorem diagonal_characteristic (q : XiZeroCopy) (branch : Bool) (x V X k : ℝ) :
    Tendsto (diagonalCurrent q branch x V X k) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (diagonalBulk q branch x V X k) (𝓝[>] 0)
      (𝓝 (-(3:ℂ)/8*spinTwo q 1 X k*clockDensity q branch (radialUnit x) (radialUnit x) V 0)) := by
  obtain ⟨hc,hb⟩ := regular_continuous q branch x V X k
  obtain ⟨hc0,hb0⟩ := regular_zero q branch x V X k
  constructor
  · have h := (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    rw [hc0] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (regular_eq q branch x V X k hh).1.symm
  · have h := (hb.continuousAt (x := (0:ℝ))).tendsto.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    rw [hb0] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (regular_eq q branch x V X k hh).2.symm

private theorem diagonal_current_derivative (q : XiZeroCopy) (branch : Bool) (x V X k : ℝ)
    {h : ℝ} (hh : 0 < h) :
    HasDerivAt (diagonalCurrent q branch x V X k)
      (W q branch x V h*spinTwo q (Z x h) X k+diagonalBulk q branch x V X k h) h := by
  obtain ⟨hZ,hA,hB⟩ := geometry_derivatives x h
  obtain ⟨hW,hW1⟩ := clock_derivatives q branch (radialUnit x) (radialUnit x) V h
  obtain ⟨hJ,hJ1⟩ := primitive_derivatives q X k (Z_interior x hh)
  have hf : HasDerivAt (fun r => primitive q X k (Z x r))
      ((A x h:ℂ)*primitiveFirst q X k (Z x h)) h := by
    simpa only [Complex.real_smul] using! hJ.scomp h hZ
  have hf1 : HasDerivAt (fun r => primitiveFirst q X k (Z x r))
      ((A x h:ℂ)*(-spinTwo q (Z x h) X k)) h := by
    simpa only [Complex.real_smul] using! hJ1.scomp h hZ
  have ha : (A x h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (A_pos x hh).ne'
  have hAc := hA.ofReal_comp
  have hBc := hB.ofReal_comp
  apply (((hW.neg.mul hf1).div hAc ha).add
    (((hW1.div (hAc.pow 2) (pow_ne_zero _ ha)).sub
      ((hW.mul hBc).div (hAc.pow 3) (pow_ne_zero _ ha))).mul hf)).congr_deriv
  dsimp [diagonalBulk]
  field_simp [ha]
  ring

private theorem bulk_integrable (q : XiZeroCopy) (branch : Bool) (x V X k : ℝ) (hV : 0 ≤ V) :
    IntervalIntegrable (diagonalBulk q branch x V X k) volume 0 V := by
  apply ((regular_continuous q branch x V X k).2.intervalIntegrable 0 V).congr_uIoo
  intro h hh
  rw [uIoo_of_le hV] at hh
  exact (regular_eq q branch x V X k hh.1).2.symm

/-- Exact finite original-clock transfer through the degenerate direct characteristic.
The retained diagonal bulk contact is integrable and both boundary currents are derived zero. -/
theorem diagonal_finite_transfer (q : XiZeroCopy) (branch : Bool) (x X k : ℝ) (V : Ioi (0:ℝ)) :
    (∫ h in (0:ℝ)..V.val, clockDensity q branch (radialUnit x) (radialUnit x) V h*
      nativeSpinTwoTrace false q h x ![x,X,k])=
      -∫ h in (0:ℝ)..V.val, diagonalBulk q branch x V X k h := by
  have hS : Continuous (fun h => spinTwo q (Z x h) X k) :=
    (spin_continuous q X k).comp_continuous (geometry_continuous x).1 (fun h => Z_closed x h)
  have hi1 : IntervalIntegrable (fun h => W q branch x V h*spinTwo q (Z x h) X k) volume 0 V.val :=
    ((clock_smooth q branch (radialUnit x) (radialUnit x) V).continuous.mul hS).intervalIntegrable 0 V.val
  have hi2 := bulk_integrable q branch x V X k V.property.le
  have hl := (diagonal_characteristic q branch x V X k).1
  have hr : Tendsto (diagonalCurrent q branch x V X k) (𝓝[<] V.val) (𝓝 0) := by
    have h := (diagonal_current_derivative q branch x V X k V.property).continuousAt.tendsto.mono_left
      (show 𝓝[<] V.val ≤ 𝓝 V.val from nhdsWithin_le_nhds)
    obtain ⟨h0,h1⟩ := clockDensity_terminal q branch (radialUnit x) (radialUnit x) V.val
    have he : diagonalCurrent q branch x V X k V=0 := by
      dsimp [diagonalCurrent,W]
      rw [h0,h1]
      simp
    rwa [he] at h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto V.property
    (fun h hh => diagonal_current_derivative q branch x V X k hh.1) (hi1.add hi2) hl hr
  rw [intervalIntegral.integral_add hi1 hi2,sub_zero] at h
  have he : (∫ h in (0:ℝ)..V.val, clockDensity q branch (radialUnit x) (radialUnit x) V h*
      nativeSpinTwoTrace false q h x ![x,X,k])=
      ∫ h in (0:ℝ)..V.val, W q branch x V h*spinTwo q (Z x h) X k := by
    apply intervalIntegral.integral_congr
    intro h _
    dsimp only
    rw [diagonal_original_trace]
    rfl
  rw [he]
  exact eq_neg_of_add_eq_zero_left h

/-- Every geometric coefficient of the regular diagonal transfer is independent of source radius. -/
theorem diagonal_regular_formula (q : XiZeroCopy) (branch : Bool) (x V X k : ℝ) (h : Ioi (0:ℝ)) :
    diagonalCurrent q branch x V X k h=
      -W q branch x V h*(Real.sinh h:ℂ)/(Real.cosh h+1:ℂ)*firstMoment q X k (Z x h)+
      ((Real.sinh h:ℂ)^(2 : ℕ)*deriv (W q branch x V) h-
        (Real.cosh h:ℂ)*(Real.sinh h:ℂ)*W q branch x V h)/(Real.cosh h+1:ℂ)^(2 : ℕ)*
          secondMoment q X k (Z x h) ∧
    diagonalBulk q branch x V X k h=
      secondMoment q X k (Z x h)/(Real.cosh h+1:ℂ)^(2 : ℕ)*
        ((Real.sinh h:ℂ)^(2 : ℕ)*deriv (deriv (W q branch x V)) h-
          3*(Real.cosh h:ℂ)*(Real.sinh h:ℂ)*deriv (W q branch x V) h+
          (2*(Real.cosh h:ℂ)^(2 : ℕ)+1)*W q branch x V h) := by
  obtain ⟨hcur,hbulk⟩ := regular_eq q branch x V X k h.property
  have hc : (Real.cosh x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos x).ne'
  have hp : (Real.cosh h+1:ℂ) ≠ 0 := by
    exact_mod_cast (show Real.cosh h+1 ≠ 0 by linarith [Real.cosh_pos h])
  have hh : (Real.cosh h:ℂ)^(2 : ℕ)-(Real.sinh h:ℂ)^(2 : ℕ)=1 := by exact_mod_cast Real.cosh_sq_sub_sinh_sq h.val
  constructor
  · rw [hcur]
    dsimp [regularCurrent,A,B,ratioOne,ratioTwo]
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one]
    field_simp [hc,hp]
  · rw [hbulk]
    dsimp [regularBulk,A,B,ratioOne,ratioTwo]
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one]
    linear_combination (norm := (field_simp [hc,hp]; ring))
      (secondMoment q X k (Z x h)*W q branch x V h/(Real.cosh h+1:ℂ)^(2 : ℕ))*hh

private def reflectedSource (image : Bool) (y : ℝ) : ℝ := if image then -y else y

/-- Original lower delay on the direct or image causal branch. -/
def causalDelayStart (image : Bool) (x y : ℝ) : ℝ :=
  if image then -2*y else 2*max (x-y) 0
/-- Literal physical invariant with ingoing source delay fixed. -/
def delayArgument (image : Bool) (x y h : ℝ) : ℝ :=
  invariant (h-x+y) x (reflectedSource image y)
/-- Actual first delay derivative of the original physical invariant. -/
def delaySlope (image : Bool) (x y h : ℝ) : ℝ :=
  invariantTimeFirst (h-x+y) x (reflectedSource image y)
private def delayAcceleration (image : Bool) (x y h : ℝ) : ℝ :=
  invariantTimeSecond (h-x+y) x (reflectedSource image y)

private theorem start_separation (image : Bool) (x y : Iic (0:ℝ)) :
    causalDelayStart image x y-x+y=|x.val-reflectedSource image y| := by
  have hx : x.val ≤ 0 := x.property
  have hy : y.val ≤ 0 := y.property
  cases image
  · simp only [causalDelayStart,reflectedSource,Bool.false_eq_true,if_false]
    by_cases h : 0 ≤ x.val-y.val
    · rw [max_eq_left h,abs_of_nonneg h]
      ring
    · rw [max_eq_right (le_of_not_ge h),abs_of_nonpos (le_of_not_ge h)]
      ring
  · simp only [causalDelayStart,reflectedSource,if_true,sub_neg_eq_add]
    rw [abs_of_nonpos (show x.val+y.val ≤ 0 by linarith)]
    ring

/-- Both actual branch starts are causal, including the closed AdS radial endpoints. -/
theorem causalDelayStart_nonneg (image : Bool) (x y : Iic (0:ℝ)) :
    0 ≤ causalDelayStart image x y := by
  cases image
  · exact mul_nonneg (by norm_num) (le_max_right _ _)
  · change 0 ≤ -2*y.val
    have hy : y.val ≤ 0 := y.property
    linarith

private theorem separation_bound (image : Bool) (x y : Iic (0:ℝ)) {h : ℝ}
    (hh : causalDelayStart image x y ≤ h) : |x.val-reflectedSource image y| ≤ h-x+y := by
  have hs := start_separation image x y
  linarith

private theorem delayArgument_closed (image : Bool) (x y : Iic (0:ℝ)) {h : ℝ}
    (hh : causalDelayStart image x y ≤ h) : 1 ≤ delayArgument image x y h :=
  invariant_causal ⟨h-x+y,x,reflectedSource image y,separation_bound image x y hh⟩

/-- Each original direct/image lower endpoint has invariant one. -/
theorem delayArgument_characteristic (image : Bool) (x y : Iic (0:ℝ)) :
    delayArgument image x y (causalDelayStart image x y)=1 := by
  unfold delayArgument
  rw [start_separation]
  simpa only [invariant,Real.cosh_abs] using invariant_characteristic x.val (reflectedSource image y)

private theorem delayArgument_interior (image : Bool) (x y : Iic (0:ℝ)) {h : ℝ}
    (hh : causalDelayStart image x y < h) : 1 < delayArgument image x y h := by
  have hs := start_separation image x y
  have ht : |x.val-reflectedSource image y| < h-x+y := by linarith
  have ht0 : 0 < h-x+y := lt_of_le_of_lt (abs_nonneg _) ht
  have hc : Real.cosh (x.val-reflectedSource image y)<Real.cosh (h-x+y) :=
    Real.cosh_lt_cosh.mpr (by simpa only [abs_of_pos ht0] using ht)
  unfold delayArgument invariant
  apply (lt_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).mpr
  rw [Real.cosh_sub] at hc
  linarith

private theorem slope_positive (image : Bool) (x y : Iic (0:ℝ)) {h : ℝ}
    (hh : causalDelayStart image x y < h) : 0 < delaySlope image x y h := by
  have hs := start_separation image x y
  have ht : 0 < h-x+y := by have := abs_nonneg (x.val-reflectedSource image y); linarith
  exact div_pos (Real.sinh_pos_iff.mpr ht) (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))

private theorem slope_positive_closed (image : Bool) (x y : Iic (0:ℝ))
    (hne : x.val ≠ reflectedSource image y) {h : ℝ}
    (hh : causalDelayStart image x y ≤ h) : 0 < delaySlope image x y h := by
  have ht := lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hne)) (separation_bound image x y hh)
  exact div_pos (Real.sinh_pos_iff.mpr ht) (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))

private theorem delay_geometry_derivatives (image : Bool) (x y h : ℝ) :
    HasDerivAt (delayArgument image x y) (delaySlope image x y h) h ∧
    HasDerivAt (delaySlope image x y) (delayAcceleration image x y h) h ∧
    HasDerivAt (delayAcceleration image x y) (delaySlope image x y h) h := by
  have ht : HasDerivAt (fun r : ℝ => r-x+y) 1 h :=
    ((hasDerivAt_id h).sub_const x).add_const y
  obtain ⟨hZ,hA⟩ := invariant_time_derivatives (h-x+y) x (reflectedSource image y)
  refine ⟨?_,?_,?_⟩
  · simpa only [delayArgument,delaySlope,mul_one] using! hZ.comp h ht
  · simpa only [delaySlope,delayAcceleration,mul_one] using! hA.comp h ht
  · simpa only [delayAcceleration,delaySlope,invariantTimeFirst,invariantTimeSecond,mul_one] using!
      ((Real.hasDerivAt_cosh (h-x+y)).comp h ht).div_const
        (Real.cosh x*Real.cosh (reflectedSource image y))

private theorem delay_geometry_continuous (image : Bool) (x y : ℝ) :
    Continuous (delayArgument image x y) ∧ Continuous (delaySlope image x y) ∧
    Continuous (delayAcceleration image x y) := by
  exact ⟨continuous_iff_continuousAt.mpr (fun h => (delay_geometry_derivatives image x y h).1.continuousAt),
    continuous_iff_continuousAt.mpr (fun h => (delay_geometry_derivatives image x y h).2.1.continuousAt),
    continuous_iff_continuousAt.mpr (fun h => (delay_geometry_derivatives image x y h).2.2.continuousAt)⟩

private abbrev fullClock (q : XiZeroCopy) (branch : Bool) (x y V : ℝ) :=
  clockDensity q branch (radialUnit x) (radialUnit y) V

/-- Original twice-transposed boundary current on either complete causal branch. -/
def delayCurrent (image : Bool) (q : XiZeroCopy) (branch : Bool) (x y V X k h : ℝ) : ℂ :=
  -fullClock q branch x y V h*primitiveFirst q X k (delayArgument image x y h)/(delaySlope image x y h:ℂ)+
    (deriv (fullClock q branch x y V) h/(delaySlope image x y h:ℂ)^(2 : ℕ)-
      fullClock q branch x y V h*(delayAcceleration image x y h:ℂ)/(delaySlope image x y h:ℂ)^(3 : ℕ))*
        primitive q X k (delayArgument image x y h)

/-- Complete source bulk after the actual delay transpose, retaining the original finite clock. -/
def delayBulk (image : Bool) (q : XiZeroCopy) (branch : Bool) (x y V X k h : ℝ) : ℂ :=
  primitive q X k (delayArgument image x y h)*
    (deriv (deriv (fullClock q branch x y V)) h/(delaySlope image x y h:ℂ)^(2 : ℕ)-
      3*(delayAcceleration image x y h:ℂ)*deriv (fullClock q branch x y V) h/(delaySlope image x y h:ℂ)^(3 : ℕ)+
      (3*(delayAcceleration image x y h:ℂ)^(2 : ℕ)-(delaySlope image x y h:ℂ)^(2 : ℕ))*
        fullClock q branch x y V h/(delaySlope image x y h:ℂ)^(4 : ℕ))

/-- The general delay chart is the literal radius-frozen physical spin-two trace. -/
theorem delay_original_trace (image : Bool) (q : XiZeroCopy) (x y h X k : ℝ) :
    nativeSpinTwoTrace image q h x ![y,X,k]=spinTwo q (delayArgument image x y h) X k := by
  rw [nativeSpinTwoTrace_eq]
  rfl

private theorem delay_current_derivative (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (V X k : ℝ) {h : ℝ} (hh : causalDelayStart image x y < h) :
    HasDerivAt (delayCurrent image q branch x y V X k)
      (fullClock q branch x y V h*spinTwo q (delayArgument image x y h) X k+
        delayBulk image q branch x y V X k h) h := by
  obtain ⟨hZ,hA,hB⟩ := delay_geometry_derivatives image x y h
  obtain ⟨hW,hW1⟩ := clock_derivatives q branch (radialUnit x) (radialUnit y) V h
  obtain ⟨hJ,hJ1⟩ := primitive_derivatives q X k (delayArgument_interior image x y hh)
  have hf : HasDerivAt (fun r => primitive q X k (delayArgument image x y r))
      ((delaySlope image x y h:ℂ)*primitiveFirst q X k (delayArgument image x y h)) h := by
    simpa only [Complex.real_smul] using! hJ.scomp h hZ
  have hf1 : HasDerivAt (fun r => primitiveFirst q X k (delayArgument image x y r))
      ((delaySlope image x y h:ℂ)*(-spinTwo q (delayArgument image x y h) X k)) h := by
    simpa only [Complex.real_smul] using! hJ1.scomp h hZ
  have ha : (delaySlope image x y h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (slope_positive image x y hh).ne'
  have hAc := hA.ofReal_comp
  have hBc := hB.ofReal_comp
  apply (((hW.neg.mul hf1).div hAc ha).add
    (((hW1.div (hAc.pow 2) (pow_ne_zero _ ha)).sub
      ((hW.mul hBc).div (hAc.pow 3) (pow_ne_zero _ ha))).mul hf)).congr_deriv
  dsimp [delayBulk]
  field_simp [ha]
  ring

private theorem primitives_continuousOn (q : XiZeroCopy) (X k : ℝ) :
    ContinuousOn (primitive q X k) (Ici 1) ∧ ContinuousOn (primitiveFirst q X k) (Ici 1) := by
  have hU := (moments_continuous q X k).2
  have hF := (moments_continuous q X k).1
  have hz : Continuous (fun z : ℝ => (z:ℂ)-1) := by fun_prop
  constructor
  · apply ((hz.pow 2).mul hU).continuousOn.congr
    intro z hz
    exact (primitive_factor q X k ⟨z,hz⟩).1
  · apply (hz.mul hF).continuousOn.congr
    intro z hz
    exact (primitive_factor q X k ⟨z,hz⟩).2

private theorem delay_continuousOn (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (V X k : ℝ) (hne : x.val ≠ reflectedSource image y) :
    ContinuousOn (delayCurrent image q branch x y V X k) (Ici (causalDelayStart image x y)) ∧
    ContinuousOn (delayBulk image q branch x y V X k) (Ici (causalDelayStart image x y)) := by
  obtain ⟨hZ,hA,hB⟩ := delay_geometry_continuous image x y
  have hJ := (primitives_continuousOn q X k).1.comp hZ.continuousOn
    (fun h hh => delayArgument_closed image x y hh)
  have hJ1 := (primitives_continuousOn q X k).2.comp hZ.continuousOn
    (fun h hh => delayArgument_closed image x y hh)
  have hw := clock_smooth q branch (radialUnit x) (radialUnit y) V
  have hw1 := (contDiff_infty_iff_deriv.mp hw).2
  have hw2 := (contDiff_infty_iff_deriv.mp hw1).2
  have h0 := hw.continuous.continuousOn (s := Ici (causalDelayStart image x y))
  have h1 := hw1.continuous.continuousOn (s := Ici (causalDelayStart image x y))
  have h2 := hw2.continuous.continuousOn (s := Ici (causalDelayStart image x y))
  have ha := (Complex.continuous_ofReal.comp hA).continuousOn (s := Ici (causalDelayStart image x y))
  have hb := (Complex.continuous_ofReal.comp hB).continuousOn (s := Ici (causalDelayStart image x y))
  have hn (h : ℝ) (hh : h ∈ Ici (causalDelayStart image x y)) : (delaySlope image x y h:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (slope_positive_closed image x y hne hh).ne'
  have hn2 := fun h hh => pow_ne_zero 2 (hn h hh)
  have hn3 := fun h hh => pow_ne_zero 3 (hn h hh)
  have hn4 := fun h hh => pow_ne_zero 4 (hn h hh)
  constructor
  · exact ((h0.neg.mul hJ1).div ha hn).add
      (((h1.div (ha.pow 2) hn2).sub ((h0.mul hb).div (ha.pow 3) hn3)).mul hJ)
  · exact hJ.mul (((h2.div (ha.pow 2) hn2).sub
      (((continuousOn_const.mul hb).mul h1).div (ha.pow 3) hn3)).add
        ((((continuousOn_const.mul (hb.pow 2)).sub (ha.pow 2)).mul h0).div (ha.pow 4) hn4))

/-- Original characteristic and terminal current values vanish on every physical branch. -/
theorem delayCurrent_endpoints (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (V X k : ℝ) :
    delayCurrent image q branch x y V X k (causalDelayStart image x y)=0 ∧
    delayCurrent image q branch x y V X k V=0 := by
  obtain ⟨hJ,hJ1⟩ := primitive_characteristic q X k
  obtain ⟨h0,h1⟩ := clockDensity_terminal q branch (radialUnit x) (radialUnit y) V
  constructor
  · dsimp [delayCurrent]
    rw [delayArgument_characteristic,hJ,hJ1]
    simp
  · dsimp [delayCurrent,fullClock]
    rw [h0,h1]
    simp

private theorem nondegenerate_transfer (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (X k : ℝ) (V : Ici (causalDelayStart image x y))
    (hne : x.val ≠ reflectedSource image y) :
    (∫ h in causalDelayStart image x y..V.val, fullClock q branch x y V h*
      spinTwo q (delayArgument image x y h) X k)=
      -∫ h in causalDelayStart image x y..V.val, delayBulk image q branch x y V X k h := by
  have hS := (spin_continuous q X k).comp (delay_geometry_continuous image x y).1.continuousOn
    (s := Ici (causalDelayStart image x y)) (fun h hh => delayArgument_closed image x y hh)
  have hsub : Icc (causalDelayStart image x y) V.val ⊆ Ici (causalDelayStart image x y) :=
    fun _ hh => hh.1
  have hi1 : IntervalIntegrable (fun h => fullClock q branch x y V h*
      spinTwo q (delayArgument image x y h) X k) volume (causalDelayStart image x y) V.val := by
    apply ContinuousOn.intervalIntegrable_of_Icc V.property
    exact (((clock_smooth q branch (radialUnit x) (radialUnit y) V).continuous.continuousOn).mul hS).mono hsub
  obtain ⟨hC,hB⟩ := delay_continuousOn image q branch x y V X k hne
  have hi2 : IntervalIntegrable (delayBulk image q branch x y V X k) volume
      (causalDelayStart image x y) V.val :=
    (hB.mono hsub).intervalIntegrable_of_Icc V.property
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le V.property (hC.mono hsub)
    (fun h hh => delay_current_derivative image q branch x y V X k hh.1) (hi1.add hi2)
  obtain ⟨hl,hr⟩ := delayCurrent_endpoints image q branch x y V X k
  rw [intervalIntegral.integral_add hi1 hi2,hl,hr,sub_zero] at ht
  exact eq_neg_of_add_eq_zero_left ht

private theorem degenerate_geometry (image : Bool) (x y : Iic (0:ℝ))
    (he : x.val = reflectedSource image y) :
    x.val=y.val ∧ reflectedSource image y=y.val ∧ causalDelayStart image x y=0 := by
  have hx : x.val ≤ 0 := x.property
  have hy : y.val ≤ 0 := y.property
  have hxy : x.val=y.val := by
    cases image
    · exact he
    · change x.val = -y.val at he
      linarith
  have href : reflectedSource image y=y.val := he.symm.trans hxy
  refine ⟨hxy,href,?_⟩
  have hs := start_separation image x y
  rw [href,hxy,sub_self,abs_zero] at hs
  rw [hxy]
  linarith

/-- Exact original-clock transfer for both complete causal branches, including all degenerate
characteristics and the closed radial endpoint. No source or terminal current is assumed zero. -/
theorem full_delay_finite_transfer (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (X k : ℝ) (V : Ici (causalDelayStart image x y)) :
    (∫ h in causalDelayStart image x y..V.val,
      clockDensity q branch (radialUnit x) (radialUnit y) V h*
        nativeSpinTwoTrace image q h x ![y,X,k])=
      -∫ h in causalDelayStart image x y..V.val, delayBulk image q branch x y V X k h := by
  have he : (fun h => clockDensity q branch (radialUnit x) (radialUnit y) V h*
      nativeSpinTwoTrace image q h x ![y,X,k])=
      fun h => fullClock q branch x y V h*spinTwo q (delayArgument image x y h) X k := by
    funext h
    rw [delay_original_trace]
  rw [he]
  by_cases hne : x.val ≠ reflectedSource image y
  · exact nondegenerate_transfer image q branch x y X k V hne
  · obtain ⟨hxy,href,hs⟩ := degenerate_geometry image x y (not_ne_iff.mp hne)
    have hV : 0 ≤ V.val := by simpa only [hs,mem_Ici] using V.property
    rcases eq_or_lt_of_le hV with hV0 | hVpos
    · rw [← hV0,hs]
      simp
    have hZ (h : ℝ) : delayArgument image x y h=Z y h := by
      simp only [delayArgument,href,hxy,sub_add_cancel,Z]
    have hA (h : ℝ) : delaySlope image x y h=A y h := by
      simp only [delaySlope,invariantTimeFirst,href,hxy,sub_add_cancel,A,pow_two]
    have hB (h : ℝ) : delayAcceleration image x y h=B y h := by
      simp only [delayAcceleration,invariantTimeSecond,href,hxy,sub_add_cancel,B,pow_two]
    have hb : delayBulk image q branch x y V X k=diagonalBulk q branch y V X k := by
      funext h
      simp only [delayBulk,diagonalBulk,hZ,hA,hB]
      simp only [fullClock,W,hxy]
    simp only [hs,hb,hZ]
    have ht := diagonal_finite_transfer q branch y X k ⟨V,hVpos⟩
    simp only [diagonal_original_trace] at ht
    simpa only [fullClock,hxy,Z] using ht

/-- The image interval begins no earlier than the direct interval on the physical radial domain. -/
theorem causalDelayStart_direct_le_image (x y : Iic (0:ℝ)) :
    causalDelayStart false x y ≤ causalDelayStart true x y := by
  have hx : x.val ≤ 0 := x.property
  have hy : y.val ≤ 0 := y.property
  have hm : max (x.val-y.val) 0 ≤ -y.val := max_le (by linarith) (by linarith)
  change 2*max (x.val-y.val) 0 ≤ -2*y.val
  linarith

/-- The exact signed full-source transfer retains both original causal integration domains. -/
theorem signed_delay_finite_transfer (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (X k : ℝ) (V : Ici (causalDelayStart true x y)) :
    (∫ h in causalDelayStart false x y..V.val,
      clockDensity q branch (radialUnit x) (radialUnit y) V h*
        nativeSpinTwoTrace false q h x ![y,X,k])-
    (∫ h in causalDelayStart true x y..V.val,
      clockDensity q branch (radialUnit x) (radialUnit y) V h*
        nativeSpinTwoTrace true q h x ![y,X,k])=
    -(∫ h in causalDelayStart false x y..V.val, delayBulk false q branch x y V X k h)+
      ∫ h in causalDelayStart true x y..V.val, delayBulk true q branch x y V X k h := by
  have hV : causalDelayStart false x y ≤ V.val :=
    (causalDelayStart_direct_le_image x y).trans V.property
  have hd := full_delay_finite_transfer false q branch x y X k ⟨V,hV⟩
  have hi := full_delay_finite_transfer true q branch x y X k V
  change (∫ h in causalDelayStart false x y..V.val,
    clockDensity q branch (radialUnit x) (radialUnit y) V h*nativeSpinTwoTrace false q h x ![y,X,k])=_ at hd
  rw [hd,hi,sub_neg_eq_add]

end
end RHTower.D4BMSpinTwoDelay
