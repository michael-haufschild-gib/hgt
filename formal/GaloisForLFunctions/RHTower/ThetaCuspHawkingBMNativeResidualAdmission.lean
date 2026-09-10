import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullNativeWave
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleGauss
import GaloisForLFunctions.HTGeometry.L2MeromorphicAlgebra
import GaloisForLFunctions.HTGeometry.L2DominatedContinuity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSpatialTests

/-! Uniform angular admission of the literal cutoff-subtracted causal theta response. -/
open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff
namespace RHTower.D4BMNativeResponse
open GaloisForLFunctions.HTGeometry D4BMNativeCircle D4BMCausalKernel
open D4BMJointSource D4BMGlobalAngularResponse D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem nativeMean_joint_continuous (q : XiZeroCopy) :
    Continuous (fun p : ℝ × UpperHalfPlane => mean q p.1 p.2.re (Real.log p.2.im)) := by
  have hmap : Continuous (fun p : (ℝ × UpperHalfPlane) × ℝ =>
      (![p.1.1,p.2,p.1.2.re,Real.log p.1.2.im] : Fin 4 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst.comp continuous_fst
    · exact continuous_snd
    · exact UpperHalfPlane.continuous_re.comp (continuous_snd.comp continuous_fst)
    · exact (UpperHalfPlane.continuous_im.comp (continuous_snd.comp continuous_fst)).log
        (fun p => p.1.2.im_pos.ne')
  have hf : Continuous (fun p : (ℝ × UpperHalfPlane) × ℝ =>
      source q p.1.1 p.2 p.1.2.re (Real.log p.1.2.im)) := by
    have hc := (source_smooth q).continuous.comp hmap
    convert! hc using 1
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (p : ℝ × UpperHalfPlane) theta => source q p.1 theta p.2.re (Real.log p.2.im)) hf 0 (2*Real.pi)
  have he : (fun p : ℝ × UpperHalfPlane => mean q p.1 p.2.re (Real.log p.2.im)) =
      fun p => (1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..(2*Real.pi),
        source q p.1 theta p.2.re (Real.log p.2.im) := by
    funext p
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
    rfl
  rw [he]
  exact hi.const_mul _

private theorem transportedPrincipal_joint_continuous (q : XiZeroCopy) :
    Continuous (fun p : ℝ × UpperHalfPlane => transportedPrincipal q p.1 (Real.log p.2.im)) := by
  have he : (fun p : ℝ × UpperHalfPlane => transportedPrincipal q p.1 (Real.log p.2.im)) =
      fun p => ∑ i : Fin 3, principalAmplitude q i*(p.2.im:ℂ)^(principalExponent q i)*
        legendreKernel (-principalExponent q i) (Real.cosh p.1) := by
    funext p
    simp only [transportedPrincipal,powerCircle_eq_legendre,Real.exp_log p.2.im_pos]
  rw [he]
  apply continuous_finsetSum
  intro i hi
  have hK : ContinuousOn (legendreKernel (-principalExponent q i)) (Ioi 0) :=
    fun z hz => ((legendreKernel_derivatives _ hz).1.continuousAt).continuousWithinAt
  have hk : Continuous (fun p : ℝ × UpperHalfPlane => legendreKernel (-principalExponent q i) (Real.cosh p.1)) :=
    hK.comp_continuous (by fun_prop) (fun p => Real.cosh_pos p.1)
  have hy : Continuous (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)^(principalExponent q i)) :=
    ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).comp continuous_snd).cpow
      continuous_const (fun p => Complex.ofReal_mem_slitPlane.mpr p.2.im_pos)
  exact (hy.const_mul _).mul hk

private theorem nativeCutoffResidual_joint_continuous (q : XiZeroCopy) :
    Continuous (fun p : ℝ × UpperHalfPlane => nativeCutoffResidual q p.1 p.2) := by
  have hcoord : Continuous (coordinates : UpperHalfPlane → Fin 2 → ℝ) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  exact (nativeMean_joint_continuous q).sub
    (((sourceCutoff_smooth.continuous.comp hcoord).comp continuous_snd).mul
      (transportedPrincipal_joint_continuous q))

/-- The actual native cutoff residual is bounded uniformly on the entire modular cell
and every bounded nonnegative radius interval. -/
theorem nativeCutoffResidual_uniform_bound (q : XiZeroCopy) (D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d ∈ Icc 0 D, ∀ z ∈ fd, ‖nativeCutoffResidual q d z‖ ≤ B := by
  obtain ⟨C,hC,hb⟩ := cuspMeanRemainder_rapid_bound q 0
  obtain ⟨A,hA⟩ := (isCompact_Icc.prod (truncated_cell_compact (3+Real.exp D))).exists_bound_of_continuousOn
    (nativeCutoffResidual_joint_continuous q).continuousOn
  refine ⟨max (max A C) 0,le_max_right _ _,?_⟩
  intro d hd z hz
  by_cases hy : z.im ≤ 3+Real.exp D
  · exact (hA (d,z) ⟨hd,hz,hy⟩).trans ((le_max_left A C).trans (le_max_left _ _))
  · have h3 : 3 < z.im := by linarith [Real.exp_pos D]
    have hk : d ≤ Real.log z.im := by
      rw [← Real.exp_le_exp,Real.exp_log z.im_pos]
      exact (Real.exp_le_exp.mpr hd.2).trans (by linarith)
    have h := hb d z.re (Real.log z.im) hd.1 hk
    have he : nativeCutoffResidual q d z = cuspMeanRemainder q d z.re (Real.log z.im) := by
      unfold nativeCutoffResidual cutoff cuspMeanRemainder
      rw [Real.smoothTransition.one_of_one_le (by change 1 ≤ z.im-2; linarith)]
      simp
    rw [he]
    exact (by simpa using h : ‖cuspMeanRemainder q d z.re (Real.log z.im)‖ ≤ C).trans
      ((le_max_right A C).trans (le_max_left _ _))


private def causalRadius (p r a b : ℝ) : ℝ :=
  Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)))

private theorem causalRadius_nonneg (p r a b : ℝ) : 0 ≤ causalRadius p r a b :=
  Real.arcosh_nonneg (le_max_left _ _)

@[fun_prop] private theorem causalRadius_joint_continuous :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => causalRadius z.1.1 z.1.2 z.2.1 z.2.2) := by
  apply Real.continuousOn_arcosh.comp_continuous
  · unfold invariant
    apply Continuous.max continuous_const
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  · intro z; change (1:ℝ) ≤ max 1 _; exact le_max_left _ _

private def residualNullSource (s amplitude : ℂ) (a b : ℝ) : ℂ :=
  oddSource s amplitude ((a+b)/2) ((a-b)/2)

private theorem actualOddSource_continuous (s amplitude : ℂ) :
    Continuous (fun z : ℝ × ℝ => oddSource s amplitude z.1 z.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  convert! h₁.sub h₂ using 1

@[fun_prop] private theorem residualNullSource_joint_continuous (s amplitude : ℂ) :
    Continuous (fun z : ℝ × ℝ => residualNullSource s amplitude z.1 z.2) := by
  have h := (actualOddSource_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  convert! h using 1

private def nativeResidualIntegrand (q : XiZeroCopy) (s amplitude : ℂ)
    (p r a b : ℝ) (z : UpperHalfPlane) : ℂ :=
  nativeCutoffResidual q (causalRadius p r a b) z*residualNullSource s amplitude a b

@[fun_prop] private theorem nativeResidualIntegrand_continuous (q : XiZeroCopy) (s amplitude : ℂ) :
    Continuous (fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × UpperHalfPlane =>
      nativeResidualIntegrand q s amplitude x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 x.2) := by
  have hk := (nativeCutoffResidual_joint_continuous q).comp
    ((causalRadius_joint_continuous.comp continuous_fst).prodMk continuous_snd)
  have hs : Continuous (fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × UpperHalfPlane =>
      residualNullSource s amplitude x.1.2.1 x.1.2.2) :=
    (residualNullSource_joint_continuous s amplitude).comp (continuous_snd.comp continuous_fst)
  exact hk.mul hs

/-- Causal source integration of the original cutoff-subtracted full theta mean. -/
def nativeResidualIntegral (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : UpperHalfPlane) : ℂ :=
  (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, nativeResidualIntegrand q s amplitude p r a b z

/-- A common bound on the actual source-integrated residual, over the complete modular
cell and every bounded nonnegative null-coordinate rectangle. -/
theorem nativeResidualIntegral_uniform_bound (q : XiZeroCopy) (s amplitude : ℂ) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Icc 0 T, ∀ r ∈ Icc 0 T, ∀ z ∈ fd,
      ‖nativeResidualIntegral q s amplitude p r z‖ ≤ B := by
  let box : Set (ℝ × ℝ) := Icc (0:ℝ) T ×ˢ Icc (0:ℝ) T
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  obtain ⟨D,hD⟩ := (hbox.prod hbox).exists_bound_of_continuousOn
    causalRadius_joint_continuous.continuousOn
  obtain ⟨K,hK,hkernel⟩ := nativeCutoffResidual_uniform_bound q (max D 0)
  obtain ⟨S,hS⟩ := hbox.exists_bound_of_continuousOn
    (residualNullSource_joint_continuous s amplitude).continuousOn
  let C := max S 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨K*C*T^2/4,by positivity,?_⟩
  intro p hp r hr z hz
  have hT : 0 ≤ T := hp.1.trans hp.2
  have hb (a b : ℝ) (ha : a ∈ Icc 0 p) (hb : b ∈ Icc 0 r) :
      ‖nativeResidualIntegrand q s amplitude p r a b z‖ ≤ K*C := by
    have haT : a ∈ Icc 0 T := ⟨ha.1,ha.2.trans hp.2⟩
    have hbT : b ∈ Icc 0 T := ⟨hb.1,hb.2.trans hr.2⟩
    have hd : causalRadius p r a b ≤ max D 0 :=
      (le_abs_self _).trans ((hD ((p,r),(a,b)) ⟨⟨hp,hr⟩,haT,hbT⟩).trans (le_max_left _ _))
    have hk := hkernel (causalRadius p r a b) ⟨causalRadius_nonneg _ _ _ _,hd⟩ z hz
    have hs : ‖residualNullSource s amplitude a b‖ ≤ C := (hS (a,b) ⟨haT,hbT⟩).trans (le_max_left _ _)
    exact (norm_mul _ _).trans_le (mul_le_mul hk hs (norm_nonneg _) hK)
  have hi (a : ℝ) (ha : a ∈ Icc 0 p) :
      ‖∫ b in (0:ℝ)..r, nativeResidualIntegrand q s amplitude p r a b z‖ ≤ K*C*r := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := r)
      (f := fun b => nativeResidualIntegrand q s amplitude p r a b z) (C := K*C)
      (fun b hb' => hb a b ha (by simpa only [uIcc_of_le hr.1] using uIoc_subset_uIcc hb'))
    simpa only [sub_zero,abs_of_nonneg hr.1] using h
  have ho := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := p) (C := K*C*r)
    (fun a ha => hi a (by simpa only [uIcc_of_le hp.1] using uIoc_subset_uIcc ha))
  rw [nativeResidualIntegral,norm_mul,norm_div,norm_one,Complex.norm_ofNat]
  calc
    _ ≤ (1/4:ℝ)*(K*C*r*p) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [sub_zero,abs_of_nonneg hp.1] using ho
    _ = K*C*(r*p)/4 := by ring
    _ ≤ K*C*(T*T)/4 := by gcongr <;> linarith [hp.1,hp.2,hr.1,hr.2]
    _ = K*C*T^2/4 := by ring


@[fun_prop] private theorem nativeResidualIntegrand_comp {P : Type*} [TopologicalSpace P]
    (q : XiZeroCopy) (s amplitude : ℂ) (p r a b : P → ℝ) (z : P → UpperHalfPlane)
    (hp : Continuous p) (hr : Continuous r) (ha : Continuous a) (hb : Continuous b) (hz : Continuous z) :
    Continuous (fun x => nativeResidualIntegrand q s amplitude (p x) (r x) (a x) (b x) (z x)) := by
  have hc := (nativeResidualIntegrand_continuous q s amplitude).comp
    (((hp.prodMk hr).prodMk (ha.prodMk hb)).prodMk hz)
  convert! hc using 1

private theorem nativeResidualIntegral_joint_continuous (q : XiZeroCopy) (s amplitude : ℂ) :
    Continuous (fun x : (ℝ × ℝ) × UpperHalfPlane => nativeResidualIntegral q s amplitude x.1.1 x.1.2 x.2) := by
  have hi : Continuous (fun x : ((ℝ × ℝ) × UpperHalfPlane) × ℝ =>
      ∫ b in (0:ℝ)..x.1.1.2, nativeResidualIntegrand q s amplitude x.1.1.1 x.1.1.2 x.2 b x.1.2) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0)
    · fun_prop
    · fun_prop
  have ho := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0)
    (f := fun (x : (ℝ × ℝ) × UpperHalfPlane) a => ∫ b in (0:ℝ)..x.1.2,
      nativeResidualIntegrand q s amplitude x.1.1 x.1.2 a b x.2) hi (show Continuous (fun x : (ℝ × ℝ) × UpperHalfPlane => x.1.1) by fun_prop)
  exact ho.const_mul (1/4:ℂ)

private theorem nativeResidualIntegral_angular_memLp (q : XiZeroCopy) (s amplitude : ℂ)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    MemLp (nativeResidualIntegral q s amplitude p r) 2 D4BMModularCore.measure := by
  obtain ⟨B,hB,hbound⟩ := nativeResidualIntegral_uniform_bound q s amplitude (max p r)
  have hc := (nativeResidualIntegral_joint_continuous q s amplitude).comp
    (show Continuous (fun z : UpperHalfPlane => ((p,r),z)) by fun_prop)
  apply MemLp.of_bound hc.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  exact hbound p ⟨hp,le_max_left _ _⟩ r ⟨hr,le_max_right _ _⟩ z hz

private def principalResidualIntegrand (q : XiZeroCopy) (s amplitude : ℂ) (i : Fin 3)
    (p r a b : ℝ) (z : UpperHalfPlane) : ℂ :=
  (principalAmplitude q i*cutoffPower (principalExponent q i) (coordinates z))*
    (legendreKernel (-principalExponent q i) (Real.cosh (causalRadius p r a b))*residualNullSource s amplitude a b)

private theorem scalarKernel_radius (nu : ℂ) {p r a b : ℝ} (ha : a ≤ p) (hb : b ≤ r) :
    riemannKernel nu ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2) =
      legendreKernel nu (Real.cosh (causalRadius p r a b)) := by
  have hc : |(p-r)/2-(a-b)/2| ≤ (p+r-a-b)/2 := by rw [abs_le]; constructor <;> linarith
  rw [causalRadius,Real.cosh_arcosh (le_max_left _ _),max_eq_right (invariant_causal ⟨_,_,_,hc⟩)]
  rfl

private theorem principalNullResponse_integral (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 3) {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (z : UpperHalfPlane) :
    principalNullResponse q s amplitude i p r*cutoffPower (principalExponent q i) (coordinates z) =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        principalResidualIntegrand q s amplitude i p r a b z := by
  unfold principalNullResponse
  rw [radialResponse_null_native _ s amplitude hp hr]
  calc
    _ = (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        (principalAmplitude q i*cutoffPower (principalExponent q i) (coordinates z))*
          (riemannKernel (-principalExponent q i) ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)*
            oddSource s amplitude ((a+b)/2) ((a-b)/2)) := by
      simp only [intervalIntegral.integral_const_mul]
      ring
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro b hb
      dsimp only [principalResidualIntegrand,residualNullSource]
      rw [scalarKernel_radius _ (show a ≤ p from
        (show a ∈ Icc 0 p by simpa only [uIcc_of_le hp] using ha).2)
        (show b ≤ r from (show b ∈ Icc 0 r by simpa only [uIcc_of_le hr] using hb).2)]

private def fullThetaIntegrand (q : XiZeroCopy) (s amplitude : ℂ)
    (p r a b : ℝ) (z : UpperHalfPlane) : ℂ :=
  mean q (causalRadius p r a b) z.re (Real.log z.im)*residualNullSource s amplitude a b

private theorem fullNullResponse_integral (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : UpperHalfPlane) :
    fullNullResponse q s amplitude p r z.re (Real.log z.im) =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, fullThetaIntegrand q s amplitude p r a b z := by
  change (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    ((1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..(2*Real.pi),
      source q (causalRadius p r a b) theta z.re (Real.log z.im))*residualNullSource s amplitude a b = _
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  rfl


private theorem fullThetaIntegrand_continuous (q : XiZeroCopy) (s amplitude : ℂ)
    (p r : ℝ) (z : UpperHalfPlane) :
    Continuous (fun x : ℝ × ℝ => fullThetaIntegrand q s amplitude p r x.1 x.2 z) := by
  have hd : Continuous (fun x : ℝ × ℝ => causalRadius p r x.1 x.2) := by
    have hc := causalRadius_joint_continuous.comp
      (show Continuous (fun x : ℝ × ℝ => ((p,r),x)) by fun_prop)
    convert! hc using 1
  have hc := ((nativeMean_joint_continuous q).comp (hd.prodMk (continuous_const : Continuous (fun _ : ℝ × ℝ => z)))).mul
    (residualNullSource_joint_continuous s amplitude)
  convert! hc using 1

private theorem principalResidualIntegrand_continuous (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 3) (p r : ℝ) (z : UpperHalfPlane) :
    Continuous (fun x : ℝ × ℝ => principalResidualIntegrand q s amplitude i p r x.1 x.2 z) := by
  have hd : Continuous (fun x : ℝ × ℝ => causalRadius p r x.1 x.2) := by
    have hc := causalRadius_joint_continuous.comp
      (show Continuous (fun x : ℝ × ℝ => ((p,r),x)) by fun_prop)
    convert! hc using 1
  have hK : ContinuousOn (legendreKernel (-principalExponent q i)) (Ioi 0) :=
    fun y hy => ((legendreKernel_derivatives _ hy).1.continuousAt).continuousWithinAt
  have hk := hK.comp_continuous (Real.continuous_cosh.comp hd) (fun x => Real.cosh_pos _)
  have hc := (hk.mul (residualNullSource_joint_continuous s amplitude)).const_mul
    (principalAmplitude q i*cutoffPower (principalExponent q i) (coordinates z))
  convert! hc using 1

private theorem residualIntegrand_split (q : XiZeroCopy) (s amplitude : ℂ)
    (p r a b : ℝ) (z : UpperHalfPlane) :
    nativeResidualIntegrand q s amplitude p r a b z = fullThetaIntegrand q s amplitude p r a b z-
      ∑ i : Fin 3, principalResidualIntegrand q s amplitude i p r a b z := by
  dsimp only [nativeResidualIntegrand,nativeCutoffResidual,fullThetaIntegrand,transportedPrincipal,
    principalResidualIntegrand,cutoffPower]
  rw [sub_mul,Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [powerCircle_eq_legendre,Real.exp_log z.im_pos]
  change cutoff (coordinates z)*(principalAmplitude q i*(z.im:ℂ)^principalExponent q i*
    legendreKernel (-principalExponent q i) (Real.cosh (causalRadius p r a b)))*
      residualNullSource s amplitude a b = _
  rw [show coordinates z 1=z.im by rfl]
  ring

private theorem rectangle_sub_sum (f : ℝ → ℝ → ℂ) (g : Fin 3 → ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : ∀ i, Continuous (Function.uncurry (g i))) (p r : ℝ) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b-∑ i : Fin 3, g i a b) =
      (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b)-
        ∑ i : Fin 3, ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, g i a b := by
  have hs : Continuous (fun x : ℝ × ℝ => ∑ i : Fin 3, g i x.1 x.2) := continuous_finsetSum _ (fun i _ => hg i)
  have hi (a : ℝ) : (∫ b in (0:ℝ)..r, f a b-∑ i : Fin 3, g i a b) =
      (∫ b in (0:ℝ)..r, f a b)-∑ i : Fin 3, ∫ b in (0:ℝ)..r, g i a b := by
    rw [intervalIntegral.integral_sub ((hf.uncurry_left a).intervalIntegrable 0 r)
      ((Continuous.uncurry_left (f := fun a b => ∑ i : Fin 3, g i a b) a hs).intervalIntegrable 0 r),
      intervalIntegral.integral_finsetSum (fun i _ => ((hg i).uncurry_left a).intervalIntegrable 0 r)]
  have ho (i : Fin 3) : Continuous (fun a => ∫ b in (0:ℝ)..r, g i a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hg i) 0 r
  simp_rw [hi]
  rw [intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r).intervalIntegrable 0 p)
    ((continuous_finsetSum _ (fun i _ => ho i)).intervalIntegrable 0 p),
    intervalIntegral.integral_finsetSum (fun i _ => (ho i).intervalIntegrable 0 p)]

/-- The literal cutoff residual equals integration of the original cutoff-subtracted
circle mean. Every transported principal amplitude and the null Jacobian are retained. -/
private theorem fullNullResidual_integral_positive (q : XiZeroCopy) (s amplitude : ℂ)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (z : UpperHalfPlane) :
    fullNullResidual q s amplitude p r z.re (Real.log z.im) = nativeResidualIntegral q s amplitude p r z := by
  rw [fullNullResidual,Real.exp_log z.im_pos,fullNullResponse_integral]
  change (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, fullThetaIntegrand q s amplitude p r a b z)-
    (∑ i : Fin 3, principalNullResponse q s amplitude i p r*cutoffPower (principalExponent q i) (coordinates z)) = _
  simp_rw [principalNullResponse_integral q s amplitude _ hp hr z]
  rw [nativeResidualIntegral]
  simp_rw [residualIntegrand_split]
  rw [rectangle_sub_sum (fun a b => fullThetaIntegrand q s amplitude p r a b z)
    (fun i a b => principalResidualIntegrand q s amplitude i p r a b z)
    (fullThetaIntegrand_continuous q s amplitude p r z)
    (fun i => principalResidualIntegrand_continuous q s amplitude i p r z),mul_sub,Finset.mul_sum]

/-- The original full theta residual belongs to its actual modular L² space at every
nonnegative null target, with no supplied admission premise. -/
private theorem fullNullResidual_angular_memLp (q : XiZeroCopy) (s amplitude : ℂ)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    MemLp (fun z : UpperHalfPlane => fullNullResidual q s amplitude p r z.re (Real.log z.im))
      2 D4BMModularCore.measure := by
  have he := funext (fullNullResidual_integral_positive q s amplitude hp hr)
  rw [he]
  exact nativeResidualIntegral_angular_memLp q s amplitude hp hr


private theorem actualOddSource_zero (s amplitude : ℂ) {tau x : ℝ} (h : tau < |x|) :
    oddSource s amplitude tau x = 0 := by
  by_cases hn : x ≤ 0
  · simp only [oddSource,min_eq_left hn,min_eq_right (neg_nonneg.mpr hn),source_boundary,sub_zero]
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonpos hn] at h
    linarith
  · have hp : 0 ≤ x := le_of_not_ge hn
    simp only [oddSource,min_eq_right hp,min_eq_left (neg_nonpos.mpr hp),source_boundary,zero_sub]
    apply neg_eq_zero.mpr
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonneg hp] at h
    linarith

private theorem residualNullSource_left_zero (s amplitude : ℂ) {a : ℝ} (ha : a ≤ 0) (b : ℝ) :
    residualNullSource s amplitude a b = 0 := by
  have he : EqOn (fun a => residualNullSource s amplitude a b) (fun _ => 0) (Iio 0) := by
    intro a ha
    apply actualOddSource_zero
    have := neg_le_abs ((a-b)/2)
    change a < 0 at ha
    linarith
  have hc := Continuous.uncurry_right (f := residualNullSource s amplitude) b
    (residualNullSource_joint_continuous s amplitude)
  exact he.closure hc continuous_const (by simpa only [closure_Iio,mem_Iic] using ha)

private theorem residualNullSource_right_zero (s amplitude : ℂ) (a : ℝ) {b : ℝ} (hb : b ≤ 0) :
    residualNullSource s amplitude a b = 0 := by
  have he : EqOn (residualNullSource s amplitude a) (fun _ => 0) (Iio 0) := by
    intro b hb
    apply actualOddSource_zero
    have := le_abs_self ((a-b)/2)
    change b < 0 at hb
    linarith
  have hc := Continuous.uncurry_left (f := residualNullSource s amplitude) a
    (residualNullSource_joint_continuous s amplitude)
  exact he.closure hc continuous_const (by simpa only [closure_Iio,mem_Iic] using hb)

private theorem nullSource_integral_nonpositive (K : ℝ → ℝ → ℂ) (s amplitude : ℂ)
    {p r : ℝ} (h : p ≤ 0 ∨ r ≤ 0) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, K a b*residualNullSource s amplitude a b) = 0 := by
  calc
    _ = ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, (0:ℂ) := by
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro b hb
      dsimp only
      rcases h with hp | hr
      · have ha0 : a ≤ 0 := (show a ∈ Icc p 0 by simpa only [uIcc_of_ge hp] using ha).2
        rw [residualNullSource_left_zero s amplitude ha0 b,mul_zero]
      · have hb0 : b ≤ 0 := (show b ∈ Icc r 0 by simpa only [uIcc_of_ge hr] using hb).2
        rw [residualNullSource_right_zero s amplitude a hb0,mul_zero]
    _ = 0 := by simp

private theorem radialNull_nonpositive (nu s amplitude : ℂ) {p r : ℝ} (h : p ≤ 0 ∨ r ≤ 0) :
    radialResponse nu s amplitude ((p+r)/2) ((p-r)/2) = 0 := by
  have hz (a b : ℝ) (h : a < 0 ∨ b < 0) : radialResponse nu s amplitude ((a+b)/2) ((a-b)/2) = 0 := by
    by_cases ht : (a+b)/2 ≤ 0
    · exact radialResponse_zero_of_nonpos nu s amplitude _ _ ht
    · apply radialResponse_zero_outside
      rw [max_eq_left (by linarith : 0 ≤ (a+b)/2)]
      rcases h with ha | hb
      · have := neg_le_abs ((a-b)/2); linarith
      · have := le_abs_self ((a-b)/2); linarith
  rcases h with hp | hr
  · have he : EqOn (fun a => radialResponse nu s amplitude ((a+r)/2) ((a-r)/2)) (fun _ => 0) (Iio 0) :=
      fun a ha => hz a r (Or.inl ha)
    have hc := (radialResponse_continuous nu s amplitude).comp
      (show Continuous (fun a : ℝ => ((a+r)/2,(a-r)/2)) by fun_prop)
    exact he.closure hc continuous_const (by simpa only [closure_Iio,mem_Iic] using hp)
  · have he : EqOn (fun b => radialResponse nu s amplitude ((p+b)/2) ((p-b)/2)) (fun _ => 0) (Iio 0) :=
      fun b hb => hz p b (Or.inr hb)
    have hc := (radialResponse_continuous nu s amplitude).comp
      (show Continuous (fun b : ℝ => ((p+b)/2,(p-b)/2)) by fun_prop)
    exact he.closure hc continuous_const (by simpa only [closure_Iio,mem_Iic] using hr)

private theorem fullNullResidual_nonpositive (q : XiZeroCopy) (s amplitude : ℂ)
    {p r : ℝ} (h : p ≤ 0 ∨ r ≤ 0) (z : UpperHalfPlane) :
    fullNullResidual q s amplitude p r z.re (Real.log z.im) = 0 := by
  have hu : fullNullResponse q s amplitude p r z.re (Real.log z.im) = 0 := by
    rw [fullNullResponse_integral]
    change (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
      mean q (causalRadius p r a b) z.re (Real.log z.im)*residualNullSource s amplitude a b) = 0
    rw [nullSource_integral_nonpositive _ s amplitude h,mul_zero]
  rw [fullNullResidual,hu]
  simp only [principalNullResponse,radialNull_nonpositive _ s amplitude h,mul_zero,zero_mul,
    Finset.sum_const_zero,sub_self]

private theorem nativeResidualIntegral_nonpositive (q : XiZeroCopy) (s amplitude : ℂ)
    {p r : ℝ} (h : p ≤ 0 ∨ r ≤ 0) (z : UpperHalfPlane) :
    nativeResidualIntegral q s amplitude p r z = 0 := by
  change (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    nativeCutoffResidual q (causalRadius p r a b) z*residualNullSource s amplitude a b) = 0
  rw [nullSource_integral_nonpositive _ s amplitude h,mul_zero]

/-- Exact residual integral identity on all real null coordinates, including the
characteristic edges and the zero field outside the original source cone. -/
theorem fullNullResidual_eq_nativeResidualIntegral (q : XiZeroCopy) (s amplitude : ℂ)
    (p r : ℝ) (z : UpperHalfPlane) :
    fullNullResidual q s amplitude p r z.re (Real.log z.im) = nativeResidualIntegral q s amplitude p r z := by
  by_cases hp : 0 ≤ p
  · by_cases hr : 0 ≤ r
    · exact fullNullResidual_integral_positive q s amplitude hp hr z
    · rw [fullNullResidual_nonpositive q s amplitude (Or.inr (le_of_not_ge hr)) z,
        nativeResidualIntegral_nonpositive q s amplitude (Or.inr (le_of_not_ge hr)) z]
  · rw [fullNullResidual_nonpositive q s amplitude (Or.inl (le_of_not_ge hp)) z,
      nativeResidualIntegral_nonpositive q s amplitude (Or.inl (le_of_not_ge hp)) z]


/-- The literal full theta residual on the original radial/modular product coordinates. -/
def nativeJointResidualField (q : XiZeroCopy) (s amplitude : ℂ) (tau : ℝ) (z : ℝ × UpperHalfPlane) : ℂ :=
  fullNullResidual q s amplitude (tau+z.1) (tau-z.1) z.2.re (Real.log z.2.im)

private theorem nativeJointResidualField_continuous (q : XiZeroCopy) (s amplitude : ℂ) :
    Continuous (fun x : ℝ × (ℝ × UpperHalfPlane) => nativeJointResidualField q s amplitude x.1 x.2) := by
  simp only [nativeJointResidualField,fullNullResidual_eq_nativeResidualIntegral]
  have hc := (nativeResidualIntegral_joint_continuous q s amplitude).comp
    (show Continuous (fun x : ℝ × (ℝ × UpperHalfPlane) => ((x.1+x.2.1,x.1-x.2.1),x.2.2)) by fun_prop)
  convert! hc using 1

private def jointMajorant (T B : ℝ) : ℝ × UpperHalfPlane → ℝ :=
  (Icc (-T) T ×ˢ (Set.univ : Set UpperHalfPlane)).indicator (fun _ => B)

private theorem jointMajorant_memLp (T B : ℝ) :
    MemLp (jointMajorant T B) 2 (radialMeasure.prod D4BMModularCore.measure) := by
  apply memLp_indicator_const 2 (measurableSet_Icc.prod MeasurableSet.univ) B
  right
  rw [Measure.prod_prod]
  apply ENNReal.mul_ne_top
  · exact ne_of_lt ((Measure.restrict_apply_le (μ := volume) (Iio (0:ℝ)) (Icc (-T) T)).trans_lt
      (measure_Icc_lt_top (μ := volume)))
  · exact measure_ne_top D4BMModularCore.measure Set.univ

private theorem nativeJointResidualField_uniform_bound (q : XiZeroCopy) (s amplitude : ℂ) (T : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ tau : ℝ, |tau| ≤ T → ∀ z : ℝ × UpperHalfPlane, z.2 ∈ fd →
      ‖nativeJointResidualField q s amplitude tau z‖ ≤ jointMajorant T B z := by
  obtain ⟨B,hB,hbound⟩ := nativeResidualIntegral_uniform_bound q s amplitude (2*T)
  refine ⟨B,hB,?_⟩
  intro tau ht z hz
  have htT : tau ≤ T := (le_abs_self tau).trans ht
  by_cases hx : |z.1| ≤ T
  · have hm : z ∈ Icc (-T) T ×ˢ (Set.univ : Set UpperHalfPlane) := ⟨abs_le.mp hx,mem_univ _⟩
    rw [jointMajorant,indicator_of_mem hm]
    by_cases hp : 0 ≤ tau+z.1
    · by_cases hr : 0 ≤ tau-z.1
      · rw [nativeJointResidualField,fullNullResidual_eq_nativeResidualIntegral]
        exact hbound (tau+z.1) ⟨hp,by linarith [(abs_le.mp hx).2]⟩
          (tau-z.1) ⟨hr,by linarith [(abs_le.mp hx).1]⟩ z.2 hz
      · rw [nativeJointResidualField,fullNullResidual_nonpositive q s amplitude (Or.inr (le_of_not_ge hr)),norm_zero]
        exact hB
    · rw [nativeJointResidualField,fullNullResidual_nonpositive q s amplitude (Or.inl (le_of_not_ge hp)),norm_zero]
      exact hB
  · have hm : z ∉ Icc (-T) T ×ˢ (Set.univ : Set UpperHalfPlane) := fun h => hx (abs_le.mpr h.1)
    have hn : tau+z.1 ≤ 0 ∨ tau-z.1 ≤ 0 := by
      by_contra h
      simp only [not_or,not_le] at h
      apply hx
      apply abs_le.mpr
      constructor <;> linarith [h.1,h.2]
    rw [jointMajorant,indicator_of_notMem hm,nativeJointResidualField,
      fullNullResidual_nonpositive q s amplitude hn,norm_zero]

/-- The literal causal residual belongs to the actual radial/modular joint Hilbert
space at every real time, without any supplied domain or source-admission hypothesis. -/
theorem nativeJointResidualField_memLp (q : XiZeroCopy) (s amplitude : ℂ) (tau : ℝ) :
    MemLp (nativeJointResidualField q s amplitude tau) 2 (radialMeasure.prod D4BMModularCore.measure) := by
  obtain ⟨B,hB,hbound⟩ := nativeJointResidualField_uniform_bound q s amplitude |tau|
  have hc := (nativeJointResidualField_continuous q s amplitude).comp
    (show Continuous (fun z : ℝ × UpperHalfPlane => (tau,z)) by fun_prop)
  apply (jointMajorant_memLp |tau| B).mono' hc.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)] with z hz
  exact hbound tau le_rfl z hz

/-- Actual L² class of the literal causal cutoff residual in the original joint space. -/
def nativeJointResidual (q : XiZeroCopy) (s amplitude : ℂ) (tau : ℝ) : SpatialSpace :=
  (nativeJointResidualField_memLp q s amplitude tau).toLp (nativeJointResidualField q s amplitude tau)

/-- The original full-source residual is a strongly continuous curve in the physical
radial/modular L² space, including its original onset and characteristic edges. -/
theorem nativeJointResidual_continuous (q : XiZeroCopy) (s amplitude : ℂ) :
    Continuous (nativeJointResidual q s amplitude) := by
  apply continuous_iff_continuousAt.mpr
  intro tau
  let T := |tau|+1
  obtain ⟨B,hB,hbound⟩ := nativeJointResidualField_uniform_bound q s amplitude T
  have hc : ContinuousOn (nativeJointResidual q s amplitude) (Icc (-T) T) := by
    apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (fun u : Icc (-T) T => nativeJointResidual q s amplitude u.1)
    apply continuous_toLp_two_of_dominated (radialMeasure.prod D4BMModularCore.measure)
      (fun u : Icc (-T) T => nativeJointResidualField q s amplitude u.1)
      (fun u => nativeJointResidualField_memLp q s amplitude u.1)
      (jointMajorant T B) (jointMajorant_memLp T B)
    · intro u
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)] with z hz
      exact hbound u.1 (abs_le.mpr u.2) z hz
    · apply Eventually.of_forall
      intro z
      have hh := (nativeJointResidualField_continuous q s amplitude).comp
        (show Continuous (fun u : Icc (-T) T => (u.1,z)) by fun_prop)
      convert! hh using 1
  apply hc.continuousAt
  apply Icc_mem_nhds
  · dsimp only [T]
    linarith [neg_abs_le tau]
  · dsimp only [T]
    linarith [le_abs_self tau]


/-- The constructed joint vector represents the literal theta residual in the original
product measure, retaining the original radial and logarithmic-height coordinates. -/
theorem nativeJointResidual_original_ae (q : XiZeroCopy) (s amplitude : ℂ) (tau : ℝ) :
    (nativeJointResidual q s amplitude tau : ℝ × UpperHalfPlane → ℂ) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      (fun z => fullNullResidual q s amplitude (tau+z.1) (tau-z.1) z.2.re (Real.log z.2.im)) :=
  (nativeJointResidualField_memLp q s amplitude tau).coeFn_toLp

/-- The actual joint residual vanishes before and at the original source onset. -/
theorem nativeJointResidual_zero_of_nonpos (q : XiZeroCopy) (s amplitude : ℂ) {tau : ℝ} (ht : tau ≤ 0) :
    nativeJointResidual q s amplitude tau = 0 := by
  apply Lp.ext
  filter_upwards [nativeJointResidual_original_ae q s amplitude tau,
    Lp.coeFn_zero ℂ 2 (radialMeasure.prod D4BMModularCore.measure)] with z hz h0
  rw [hz,h0]
  have hn : tau+z.1 ≤ 0 ∨ tau-z.1 ≤ 0 := by
    by_contra h
    simp only [not_or,not_le] at h
    linarith [h.1,h.2]
  exact fullNullResidual_nonpositive q s amplitude hn z.2

/-- Literal double time primitive on the original radial/modular product coordinates. -/
def nativeJointTimePrimitiveField (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (z : ℝ × UpperHalfPlane) : ℂ :=
  nativeResidualTimePrimitive q s amplitude t z.1 z.2.re (Real.log z.2.im)

private theorem nativeJointTimePrimitiveField_continuous (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    Continuous (nativeJointTimePrimitiveField q s amplitude t) := by
  have hc := (nativeJointResidualField_continuous q s amplitude).comp
    (show Continuous (fun p : (ℝ × UpperHalfPlane) × ℝ => (p.2,p.1)) by fun_prop)
  have hw : Continuous (fun p : (ℝ × UpperHalfPlane) × ℝ => ((t-p.2:ℝ):ℂ)) := by fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hw.mul hc) 0 t

private theorem time_interval_abs_le {t u : ℝ} (hu : u ∈ uIcc (0:ℝ) t) : |u| ≤ |t| := by
  by_cases ht : 0 ≤ t
  · have h := (show u ∈ Icc (0:ℝ) t by simpa only [uIcc_of_le ht] using hu)
    rw [abs_of_nonneg h.1,abs_of_nonneg ht]
    exact h.2
  · have ht' := le_of_not_ge ht
    have h := (show u ∈ Icc t (0:ℝ) by simpa only [uIcc_of_ge ht'] using hu)
    rw [abs_of_nonpos h.2,abs_of_nonpos ht']
    linarith [h.1]

/-- The actual native time primitive is square integrable in the original joint
space, with no energy-domain admission premise. -/
theorem nativeJointTimePrimitiveField_memLp (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    MemLp (nativeJointTimePrimitiveField q s amplitude t) 2
      (radialMeasure.prod D4BMModularCore.measure) := by
  obtain ⟨B,hB,hbound⟩ := nativeJointResidualField_uniform_bound q s amplitude |t|
  have hm := (jointMajorant_memLp |t| B).const_mul (2*|t|^2)
  apply hm.mono' (nativeJointTimePrimitiveField_continuous q s amplitude t).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)] with z hz
  have hD : 0 ≤ jointMajorant |t| B z := by
    unfold jointMajorant
    exact Set.indicator_nonneg (fun _ _ => hB) z
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t)
    (f := fun u => ((t-u:ℝ):ℂ)*nativeJointResidualField q s amplitude u z)
    (C := 2*|t| *jointMajorant |t| B z) (fun u hu => by
      have hu' := time_interval_abs_le (uIoc_subset_uIcc hu)
      have hd : |t-u| ≤ 2*|t| := (abs_sub t u).trans (by linarith)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul hd (hbound u hu' z hz) (norm_nonneg _) (by positivity))
  change ‖nativeJointTimePrimitiveField q s amplitude t z‖ ≤ _
  convert! hh using 1
  simp only [sub_zero]
  ring

private theorem timePrimitive_radial_memLp (f : ℝ × ℝ → ℂ) (hf : Continuous f)
    (hz : ∀ u x : ℝ, max u 0 < |x| → f (u,x)=0) (t : ℝ) :
    MemLp (fun x : ℝ => ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*f (u,x)) 2 radialMeasure := by
  have hc : Continuous (fun x : ℝ => ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*f (u,x)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ => ((t-p.2:ℝ):ℂ))).mul
      (hf.comp (continuous_snd.prodMk continuous_fst))
  have hk : HasCompactSupport (fun x : ℝ => ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*f (u,x)) := by
    apply HasCompactSupport.intro (K := Icc (-|t|) |t|) isCompact_Icc
    intro x hx
    have hx' : |t| < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    calc
      _ = ∫ u in (0:ℝ)..t, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have ht := time_interval_abs_le hu
        have hu' : max u 0 ≤ |t| := max_le ((le_abs_self u).trans ht) (abs_nonneg t)
        change ((t-u:ℝ):ℂ)*f (u,x) = 0
        rw [hz u x (hu'.trans_lt hx'),mul_zero]
      _ = 0 := by simp
  exact (hc.memLp_of_hasCompactSupport (μ := volume) (p := 2) hk).restrict (Iio (0:ℝ))


private def nativePrincipalStaticCoefficient (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 3) (u x : ℝ) : ℂ :=
  principalAmplitude q i * radialResponse (-principalExponent q i) s amplitude u x /
    (Real.cosh x:ℂ)^2

private theorem nativePrincipalStaticCoefficient_continuous (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 3) : Continuous (fun p : ℝ × ℝ => nativePrincipalStaticCoefficient q s amplitude i p.1 p.2) := by
  exact ((radialResponse_continuous (-principalExponent q i) s amplitude).const_mul
    (principalAmplitude q i)).div (by fun_prop)
      (fun p => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (Real.cosh_pos p.2).ne'))

private theorem nativePrincipalStaticCoefficient_zero (q : XiZeroCopy) (s amplitude : ℂ)
    (i : Fin 3) (u x : ℝ) (h : max u 0 < |x|) :
    nativePrincipalStaticCoefficient q s amplitude i u x = 0 := by
  simp only [nativePrincipalStaticCoefficient,radialResponse_zero_outside _ s amplitude u x h,
    mul_zero,zero_div]

private theorem nativeResidualStaticForcing_separated (q : XiZeroCopy) (s amplitude : ℂ)
    (u x : ℝ) (z : UpperHalfPlane) :
    nativeResidualStaticForcing q s amplitude u x z.re (Real.log z.im) =
      oddSource s amplitude u x * squareResidual q (coordinates z) +
        ∑ i : Fin 3, nativePrincipalStaticCoefficient q s amplitude i u x *
          cutoffCommutator (principalExponent q i) (coordinates z) := by
  unfold nativeResidualStaticForcing principalNullResponse
  rw [Real.exp_log z.im_pos,show (u+x+(u-x))/2 = u by ring,
    show (u+x-(u-x))/2 = x by ring,Finset.sum_div]
  congr 1
  · exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i hi
    unfold nativePrincipalStaticCoefficient coordinates
    ring

/-- The time integral of the complete literal forcing, including all cutoff commutators. -/
def nativeJointIntegratedForcing (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (z : ℝ × UpperHalfPlane) : ℂ :=
  ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*
    nativeResidualStaticForcing q s amplitude u z.1 z.2.re (Real.log z.2.im)

private theorem nativeJointIntegratedForcing_separated (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (z : ℝ × UpperHalfPlane) :
    nativeJointIntegratedForcing q s amplitude t z =
      (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*oddSource s amplitude u z.1)*
        squareResidual q (coordinates z.2) +
      ∑ i : Fin 3,
        (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ)*nativePrincipalStaticCoefficient q s amplitude i u z.1)*
          cutoffCommutator (principalExponent q i) (coordinates z.2) := by
  have hw : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ)) := by fun_prop
  have hc := (actualOddSource_continuous s amplitude).comp
    (continuous_id.prodMk (continuous_const (y := z.1)))
  have hi (i : Fin 3) := (nativePrincipalStaticCoefficient_continuous q s amplitude i).comp
    (continuous_id.prodMk (continuous_const (y := z.1)))
  have hmain : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ)*oddSource s amplitude u z.1 *
      squareResidual q (coordinates z.2)) := (hw.mul hc).mul_const _
  have hterm (i : Fin 3) : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ)*
      nativePrincipalStaticCoefficient q s amplitude i u z.1 *
        cutoffCommutator (principalExponent q i) (coordinates z.2)) := (hw.mul (hi i)).mul_const _
  have hsum : Continuous (fun u : ℝ => ∑ i : Fin 3, ((t-u:ℝ):ℂ)*
      nativePrincipalStaticCoefficient q s amplitude i u z.1 *
        cutoffCommutator (principalExponent q i) (coordinates z.2)) :=
    continuous_finsetSum _ (fun i _ => hterm i)
  unfold nativeJointIntegratedForcing
  simp_rw [nativeResidualStaticForcing_separated,mul_add,Finset.mul_sum,← mul_assoc]
  rw [intervalIntegral.integral_add (hmain.intervalIntegrable 0 t) (hsum.intervalIntegrable 0 t),
    intervalIntegral.integral_finsetSum (fun i _ => (hterm i).intervalIntegrable 0 t)]
  simp only [intervalIntegral.integral_mul_const]

/-- The actual integrated forcing belongs to the original joint L² space. No
spectral chamber, principal-channel deletion or energy-domain premise is used. -/
theorem nativeJointIntegratedForcing_memLp (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    MemLp (nativeJointIntegratedForcing q s amplitude t) 2
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hm := timePrimitive_radial_memLp (fun p => oddSource s amplitude p.1 p.2)
    (actualOddSource_continuous s amplitude)
    (fun u x h => actualOddSource_zero s amplitude ((le_max_left u 0).trans_lt h)) t
  have hi (i : Fin 3) := timePrimitive_radial_memLp
    (fun p => nativePrincipalStaticCoefficient q s amplitude i p.1 p.2)
    (nativePrincipalStaticCoefficient_continuous q s amplitude i)
    (nativePrincipalStaticCoefficient_zero q s amplitude i) t
  have hmain := l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _ hm
    (squareResidual_memLp q)
  have hsum := memLp_finsetSum (s := Finset.univ) (fun i _ =>
    l2SeparatedRepresentative_memLp radialMeasure D4BMModularCore.measure _ _ (hi i)
      (cutoffCommutator_memLp (principalExponent q i)))
  apply (hmain.add hsum).ae_eq
  exact Filter.Eventually.of_forall (fun z => (nativeJointIntegratedForcing_separated q s amplitude t z).symm)

/-- The literal elliptic right-hand side for the native double time primitive. -/
def nativeJointEllipticForcing (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (z : ℝ × UpperHalfPlane) : ℂ :=
  nativeJointIntegratedForcing q s amplitude t z - nativeJointResidualField q s amplitude t z

/-- Both terms in the native elliptic equation are admitted in the original joint L² space. -/
theorem nativeJointEllipticForcing_memLp (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    MemLp (nativeJointEllipticForcing q s amplitude t) 2
      (radialMeasure.prod D4BMModularCore.measure) :=
  (nativeJointIntegratedForcing_memLp q s amplitude t).sub
    (nativeJointResidualField_memLp q s amplitude t)

/-- Joint continuity of the literal residual in its original time, radius and
upper-half-plane coordinates. -/
theorem nativeJointResidualField_joint_continuous (q : XiZeroCopy) (s amplitude : ℂ) :
    Continuous (fun x : ℝ × (ℝ × UpperHalfPlane) =>
      nativeJointResidualField q s amplitude x.1 x.2) :=
  nativeJointResidualField_continuous q s amplitude

end
end RHTower.D4BMNativeResponse
