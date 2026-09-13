import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalPotential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOnsetGreenReconstruction

/-! The full native causal potential is the original direct-minus-image source action. -/
namespace RHTower.D4BMOriginalRetardedIdentity
open GaloisForLFunctions.HTGeometry D4BMNativeCircle D4BMCausalKernel
open D4BMNativeResponse D4BMJointSource D4BMModularCore D4BMHorizon
open D4BMOriginalCausalPotential D4BMOnsetGreenReconstruction
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace


private theorem triangle_swap (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, ∫ y in x..r, f x y) = ∫ y in l..r, ∫ x in l..y, f x y := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let g (x y : ℝ) := if x ≤ y then f x y else 0
  have hi : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hg : Integrable (Function.uncurry g) (μ.prod μ) := by
    convert! hi.indicator (measurableSet_le measurable_fst measurable_snd) using 1
  have hswap := integral_integral_swap hg
  have hleft : (∫ x in l..r, ∫ y in x..r, f x y) = ∫ x, ∫ y, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    have hset : Ioc l r ∩ Ici x = Icc x r := by
      ext y
      simp only [mem_inter_iff,mem_Ioc,mem_Ici,mem_Icc]
      constructor
      · rintro ⟨hxy,hy⟩; exact ⟨hy,hxy.2⟩
      · rintro ⟨hxy,hy⟩; exact ⟨⟨hx.1.trans_le hxy,hy⟩,hxy⟩
    have he : g x = (Ici x).indicator (f x) := by
      ext y; simp only [g,Set.indicator_apply,mem_Ici]
    change _ = ∫ y in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx.2]
  have hright : (∫ y in l..r, ∫ x in l..y, f x y) = ∫ y, ∫ x, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    dsimp only
    have hset : Ioc l r ∩ Iic y = Ioc l y := by
      ext x
      simp only [mem_inter_iff,mem_Ioc,mem_Iic]
      constructor
      · rintro ⟨hxy,hx⟩; exact ⟨hxy.1,hx⟩
      · rintro ⟨hx,hxy⟩; exact ⟨⟨hx,hxy.trans hy.2⟩,hxy⟩
    have he : (fun x => g x y) = (Iic y).indicator (fun x => f x y) := by
      ext x; simp only [g,Set.indicator_apply,mem_Iic]
    change _ = ∫ x in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Iic,hset,intervalIntegral.integral_of_le hy.1.le]
  rw [hleft,hright]
  exact hswap


private theorem rectangle_triangles (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) {p : ℝ} (hp : 0 ≤ p) (r : ℝ) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b)=
      (∫ a in (0:ℝ)..p, ∫ b in a..r, f a b)+
      (∫ a in (0:ℝ)..p, ∫ b in a..p, f b a) := by
  have hslice (a : ℝ) : Continuous (f a) := hf.comp (continuous_const.prodMk continuous_id)
  have hz : Continuous (fun a => ∫ b in (0:ℝ)..a, f a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_id
  have hr : Continuous (fun a => ∫ b in (0:ℝ)..r, f a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r
  have htail : Continuous (fun a => ∫ b in a..r, f a b) := by
    convert! hr.sub hz using 1
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      ((hslice a).intervalIntegrable 0 r) ((hslice a).intervalIntegrable 0 a)).symm
  have he (a : ℝ) : (∫ b in (0:ℝ)..r, f a b)=
      (∫ b in a..r, f a b)+(∫ b in (0:ℝ)..a, f a b) := by
    rw [add_comm]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((hslice a).intervalIntegrable 0 a) ((hslice a).intervalIntegrable a r)).symm
  simp_rw [he]
  rw [intervalIntegral.integral_add (htail.intervalIntegrable 0 p) (hz.intervalIntegrable 0 p)]
  congr 1
  exact (triangle_swap (fun a b => f b a) (hf.comp continuous_swap) hp).symm

private def closedKernel (q : XiZeroCopy) (p r X k a b : ℝ) : ℂ :=
  mean q (Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)))) X k

private theorem closedKernel_continuous (q : XiZeroCopy) (p r X k : ℝ) :
    Continuous (Function.uncurry (closedKernel q p r X k)) := by
  have hz : Continuous (fun z : ℝ × ℝ =>
      max 1 (invariant ((p+r-z.1-z.2)/2) ((p-r)/2) ((z.1-z.2)/2))) := by
    apply Continuous.max continuous_const
    unfold invariant
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have hd := Real.continuousOn_arcosh.comp_continuous hz
    (fun z => (show (1:ℝ) ≤ max 1 _ from le_max_left _ _))
  exact (mean_radial_smooth q X k).continuous.comp hd

private def reducedNull (s amp : ℂ) (a b : ℝ) : ℂ :=
  timeReducedCoefficient s amp ((a+b)/2) ((a-b)/2)

private theorem oddSource_continuous (s amp : ℂ) :
    Continuous (fun z : ℝ × ℝ => oddSource s amp z.1 z.2) := by
  have h1 := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h2 := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  convert! h1.sub h2 using 1

private theorem oddSource_upper (s amp : ℂ) {a b : ℝ} (hab : a ≤ b) :
    oddSource s amp ((a+b)/2) ((a-b)/2)=reducedNull s amp a b := by
  have hx : (a-b)/2 ≤ 0 := by linarith
  simp only [oddSource,min_eq_left hx,min_eq_right (neg_nonneg.mpr hx),source_boundary,sub_zero]
  rfl

private theorem oddSource_lower (s amp : ℂ) {a b : ℝ} (hab : a ≤ b) :
    oddSource s amp ((b+a)/2) ((b-a)/2) = -reducedNull s amp a b := by
  have hx : 0 ≤ (b-a)/2 := by linarith
  simp only [oddSource,min_eq_right hx,min_eq_left (neg_nonpos.mpr hx),source_boundary,zero_sub]
  rw [show (b+a)/2=(a+b)/2 by ring,show -((b-a)/2)=(a-b)/2 by ring]
  rfl

private theorem native_rectangle (q : XiZeroCopy) (s amp : ℂ) (p r X k : ℝ) :
    fullNullResponse q s amp p r X k=
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        closedKernel q p r X k a b*oddSource s amp ((a+b)/2) ((a-b)/2) := by
  change (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    ((1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..(2*Real.pi),
      source q (Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2))))
        theta X k)*oddSource s amp ((a+b)/2) ((a-b)/2) = _
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  rfl

private theorem native_triangles (q : XiZeroCopy) (s amp : ℂ) {p r : ℝ}
    (hp : 0 ≤ p) (hpr : p ≤ r) (X k : ℝ) :
    fullNullResponse q s amp p r X k=
      (∫ a in (0:ℝ)..p, ∫ b in a..r, closedKernel q p r X k a b*reducedNull s amp a b)/4-
      (∫ a in (0:ℝ)..p, ∫ b in a..p, closedKernel q p r X k b a*reducedNull s amp a b)/4 := by
  let f (a b : ℝ) := closedKernel q p r X k a b*oddSource s amp ((a+b)/2) ((a-b)/2)
  have ho := (oddSource_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  have hf : Continuous (Function.uncurry f) := by
    convert! (closedKernel_continuous q p r X k).mul ho using 1
  rw [native_rectangle,rectangle_triangles f hf hp r]
  have hu : (∫ a in (0:ℝ)..p, ∫ b in a..r, f a b)=
      ∫ a in (0:ℝ)..p, ∫ b in a..r, closedKernel q p r X k a b*reducedNull s amp a b := by
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a ≤ p := (show a ∈ Icc 0 p by simpa [uIcc_of_le hp] using ha).2
    apply intervalIntegral.integral_congr
    intro b hb
    have hb' : a ≤ b := (show b ∈ Icc a r by simpa [uIcc_of_le (ha'.trans hpr)] using hb).1
    dsimp only [f]
    rw [oddSource_upper s amp hb']
  have hl : (∫ a in (0:ℝ)..p, ∫ b in a..p, f b a)=
      -(∫ a in (0:ℝ)..p, ∫ b in a..p, closedKernel q p r X k b a*reducedNull s amp a b) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a ≤ p := (show a ∈ Icc 0 p by simpa [uIcc_of_le hp] using ha).2
    dsimp only
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro b hb
    have hb' : a ≤ b := (show b ∈ Icc a p by simpa [uIcc_of_le ha'] using hb).1
    dsimp only [f]
    rw [oddSource_lower s amp hb',mul_neg]
  rw [hu,hl]
  ring

/-- The complete original reduced forcing, before principal subtraction. -/
def reducedField (q : XiZeroCopy) (s amp : ℂ) (tau x : ℝ) (z : Point) : ℂ :=
  timeReducedCoefficient s amp tau x*fullSquarePotential q z

private theorem average_const_mul (c : ℂ) (F : ℝ → ℂ) :
    D4BMNativeCircle.average (fun theta => c*F theta)=c*D4BMNativeCircle.average F := by
  unfold D4BMNativeCircle.average
  rw [integral_const_mul]
  ring

/-- The full native odd-source rectangle equals the original retarded direct-minus-image
action of the unchanged reduced source, including both characteristic endpoints. -/
theorem fullNullResponse_eq_retarded_reduced (q : XiZeroCopy) (s amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    fullNullResponse q s amp p (p+width) X k=
      retardedNullAction (reducedField q s amp) p width X k := by
  rw [native_triangles q s amp (p := (p:ℝ)) (r := (p:ℝ)+width)
    p.property (le_add_of_nonneg_right width.property) X k]
  unfold retardedNullAction
  change _=(∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..((p:ℝ)+width),
    D4BMNativeCircle.average (fun theta => reducedNull s amp a b*
      source q (Real.arcosh (max 1 (invariant ((2*p+width-a-b)/2) (-(width:ℝ)/2) ((a-b)/2)))) theta X k))/4-
    (∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..(p:ℝ),
    D4BMNativeCircle.average (fun theta => reducedNull s amp a b*
      source q (Real.arcosh (max 1 (invariant ((2*p+width-a-b)/2) (-(width:ℝ)/2) (-(a-b)/2)))) theta X k))/4
  simp_rw [average_const_mul]
  dsimp only [closedKernel,mean]
  rw [show (p:ℝ)+((p:ℝ)+width)=2*p+width by ring,
    show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring]
  congr 2
  · apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro b hb
    dsimp only
    ring
  · apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro b hb
    dsimp only
    rw [show (2*(p:ℝ)+width-b-a)/2=(2*p+width-a-b)/2 by ring,
      show (b-a)/2=-(a-b)/2 by ring]
    ring

private def sampleRadius (image : Bool) (p r a b : ℝ) : ℝ :=
  Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2)
    (if image then -(a-b)/2 else (a-b)/2)))

private theorem sampleRadius_continuous (image : Bool) (p r : ℝ) :
    Continuous (Function.uncurry (sampleRadius image p r)) := by
  have hz : Continuous (fun z : ℝ × ℝ => max 1 (invariant ((p+r-z.1-z.2)/2) ((p-r)/2)
      (if image then -(z.1-z.2)/2 else (z.1-z.2)/2))) := by
    apply Continuous.max continuous_const
    unfold invariant
    apply Continuous.div
    · cases image <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
    · cases image <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
    · intro z
      exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  exact Real.continuousOn_arcosh.comp_continuous hz
    (fun z => (show (1:ℝ) ≤ max 1 _ from le_max_left _ _))

private def samplePoint (image : Bool) (p r X k a b theta : ℝ) : Point :=
  logCircle (sampleRadius image p r a b) theta X k

private theorem samplePoint_pos (image : Bool) (p r X k a b theta : ℝ) :
    0 < samplePoint image p r X k a b theta 1 :=
  mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))

private theorem samplePoint_continuous (image : Bool) (p r X k : ℝ) :
    Continuous (fun z : (ℝ × ℝ) × ℝ => samplePoint image p r X k z.1.1 z.1.2 z.2) := by
  have hd0 := (sampleRadius_continuous image p r).comp
    (continuous_fst : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1))
  have hd : Continuous (fun z : (ℝ × ℝ) × ℝ => sampleRadius image p r z.1.1 z.1.2) := by
    convert! hd0 using 1
  have hD : Continuous (fun z : (ℝ × ℝ) × ℝ => denominator (sampleRadius image p r z.1.1 z.1.2) z.2) :=
    (Real.continuous_cosh.comp hd).sub ((Real.continuous_sinh.comp hd).mul
      (Real.continuous_cos.comp continuous_snd))
  have hn (z : (ℝ × ℝ) × ℝ) : denominator (sampleRadius image p r z.1.1 z.1.2) z.2 ≠ 0 :=
    (denominator_pos _ _).ne'
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun z : (ℝ × ℝ) × ℝ => X+Real.exp k*
      (Real.sinh (sampleRadius image p r z.1.1 z.1.2)*Real.sin z.2/
        denominator (sampleRadius image p r z.1.1 z.1.2) z.2))
    exact continuous_const.add (continuous_const.mul (((Real.continuous_sinh.comp hd).mul (Real.continuous_sin.comp continuous_snd)).div hD hn))
  · change Continuous (fun z : (ℝ × ℝ) × ℝ => Real.exp k*
      (1/denominator (sampleRadius image p r z.1.1 z.1.2) z.2))
    exact continuous_const.mul (continuous_const.div hD hn)

private theorem square_comp {P : Type*} [TopologicalSpace P] (q : XiZeroCopy)
    (z : P → Point) (hz : Continuous z) (hpos : ∀ t, 0 < z t 1) :
    Continuous (fun t => fullSquarePotential q (z t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (fullSquarePotential_smooth q (z t) (hpos t) 0).continuousAt.comp hz.continuousAt

private theorem gradient_comp {P : Type*} [TopologicalSpace P] (q : XiZeroCopy)
    (z : P → Point) (hz : Continuous z) (hpos : ∀ t, 0 < z t 1) :
    Continuous (fun t => fullGradientEnergy q (z t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (fullGradientEnergy_smooth q (z t) (hpos t)).continuousAt.comp hz.continuousAt

private theorem original_comp {P : Type*} [TopologicalSpace P] (q : XiZeroCopy)
    (branch : Bool) (amp : ℂ) (tau x : P → ℝ) (z : P → Point)
    (ht : Continuous tau) (hx : Continuous x) (hz : Continuous z) (hpos : ∀ t, 0 < z t 1) :
    Continuous (fun t => timeOriginalForcing q branch amp (tau t) (x t) (z t)) := by
  have hF := square_comp q z hz hpos
  have hG := gradient_comp q z hz hpos
  have hU : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun t => (radialUnit_hasDerivAt t).continuousAt)
  have hA : Continuous (sourceAmplitude (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t => (sourceAmplitude_hasDerivAt _ _ _ _ t).continuousAt)
  have hH : Continuous (timeOnset (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun t => (timeOnset_hasDerivAt _ t).continuousAt)
  unfold timeOriginalForcing originalForcing
  fun_prop

private theorem reduced_comp {P : Type*} [TopologicalSpace P] (q : XiZeroCopy)
    (s amp : ℂ) (tau x : P → ℝ) (z : P → Point)
    (ht : Continuous tau) (hx : Continuous x) (hz : Continuous z) (hpos : ∀ t, 0 < z t 1) :
    Continuous (fun t => reducedField q s amp (tau t) (x t) (z t)) := by
  have hF := square_comp q z hz hpos
  have hC := (timeReducedCoefficient_joint_continuous s amp).comp (ht.prodMk hx)
  convert! hC.mul hF using 1

private def circleSource (S : ℝ → ℝ → Point → ℂ) (image : Bool) (p r X k a b : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta => S ((a+b)/2) ((a-b)/2) (samplePoint image p r X k a b theta))

private theorem averaged_continuous {f : (ℝ × ℝ) × ℝ → ℂ} (hf : Continuous f) :
    Continuous (fun z : ℝ × ℝ => D4BMNativeCircle.average (fun theta => f (z,theta))) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (z : ℝ × ℝ) (theta : ℝ) => f (z,theta)) hf 0 (2*Real.pi)
  have hs := (continuous_const : Continuous (fun _ : ℝ × ℝ => (1/(2*Real.pi:ℂ)))).mul h
  simp only [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)] at hs
  exact hs

private theorem original_sample_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p r X k : ℝ) :
    Continuous (fun z : (ℝ × ℝ) × ℝ => timeOriginalForcing q branch amp ((z.1.1+z.1.2)/2)
      ((z.1.1-z.1.2)/2) (samplePoint image p r X k z.1.1 z.1.2 z.2)) :=
  original_comp q branch amp _ _ _ (by fun_prop) (by fun_prop)
    (samplePoint_continuous image p r X k) (fun z => samplePoint_pos image p r X k z.1.1 z.1.2 z.2)

private theorem reduced_sample_continuous (q : XiZeroCopy) (s amp : ℂ)
    (image : Bool) (p r X k : ℝ) :
    Continuous (fun z : (ℝ × ℝ) × ℝ => reducedField q s amp ((z.1.1+z.1.2)/2)
      ((z.1.1-z.1.2)/2) (samplePoint image p r X k z.1.1 z.1.2 z.2)) :=
  reduced_comp q s amp _ _ _ (by fun_prop) (by fun_prop)
    (samplePoint_continuous image p r X k) (fun z => samplePoint_pos image p r X k z.1.1 z.1.2 z.2)

private theorem average_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    D4BMNativeCircle.average (fun t => f t-g t)=D4BMNativeCircle.average f-D4BMNativeCircle.average g := by
  unfold D4BMNativeCircle.average
  rw [integral_sub (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring

private theorem circle_source_difference (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p r X k a b : ℝ) :
    circleSource (timeOriginalForcing q branch amp) image p r X k a b-
      circleSource (reducedField q (physicalRate q branch) amp) image p r X k a b=
      circleSource (timeFieldWave (timeLiftField q branch amp)) image p r X k a b := by
  have hF := (original_sample_continuous q branch amp image p r X k).comp
    (show Continuous (fun theta : ℝ => ((a,b),theta)) by fun_prop)
  have hR := (reduced_sample_continuous q (physicalRate q branch) amp image p r X k).comp
    (show Continuous (fun theta : ℝ => ((a,b),theta)) by fun_prop)
  dsimp only [Function.comp_def] at hF hR
  unfold circleSource
  rw [← average_sub hF hR]
  congr 1
  funext theta
  rw [timeOriginalForcing_gradient_absorption q branch amp _ _ _ (samplePoint_pos image p r X k a b theta)]
  simp only [reducedField,add_sub_cancel_right]

private def triangle (f : ℝ → ℝ → ℂ) (p r : ℝ) : ℂ :=
  ∫ a in (0:ℝ)..p, ∫ b in a..r, f a b

private theorem triangle_sub (f g : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    triangle (fun a b => f a b-g a b) p r=triangle f p r-triangle g p r := by
  have hc (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) :
      Continuous (fun a => ∫ b in a..r, f a b) := by
    have h1 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf 0 r
    have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0) hf continuous_id
    convert! h1.sub h2 using 1
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      ((hf.uncurry_left a).intervalIntegrable 0 r) ((hf.uncurry_left a).intervalIntegrable 0 a)).symm
  unfold triangle
  simp_rw [intervalIntegral.integral_sub ((hf.uncurry_left _).intervalIntegrable _ _)
    ((hg.uncurry_left _).intervalIntegrable _ _)]
  exact intervalIntegral.integral_sub ((hc f hf).intervalIntegrable 0 p) ((hc g hg).intervalIntegrable 0 p)

private theorem action_triangles (S : ℝ → ℝ → Point → ℂ) (p width : NNReal) (X k : ℝ) :
    retardedNullAction S p width X k=
      triangle (circleSource S false p (p+width) X k) p (p+width)/4-
      triangle (circleSource S true p (p+width) X k) p p/4 := by
  unfold retardedNullAction triangle circleSource samplePoint sampleRadius
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [show (p:ℝ)+((p:ℝ)+width)=2*p+width by ring,
    show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring]
  rfl

/-- The original retarded source action retains the exact reduced forcing and full lift. -/
theorem retarded_original_source_difference (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    retardedNullAction (timeOriginalForcing q branch amp) p width X k-
      retardedNullAction (reducedField q (physicalRate q branch) amp) p width X k=
      retardedNullAction (timeFieldWave (timeLiftField q branch amp)) p width X k := by
  have hcF (image : Bool) : Continuous (Function.uncurry
      (circleSource (timeOriginalForcing q branch amp) image p (p+width) X k)) :=
    averaged_continuous (original_sample_continuous q branch amp image p (p+width) X k)
  have hcR (image : Bool) : Continuous (Function.uncurry
      (circleSource (reducedField q (physicalRate q branch) amp) image p (p+width) X k)) :=
    averaged_continuous (reduced_sample_continuous q (physicalRate q branch) amp image p (p+width) X k)
  have he (image : Bool) (r : ℝ) :
      triangle (circleSource (timeOriginalForcing q branch amp) image p (p+width) X k) p r-
        triangle (circleSource (reducedField q (physicalRate q branch) amp) image p (p+width) X k) p r=
        triangle (circleSource (timeFieldWave (timeLiftField q branch amp)) image p (p+width) X k) p r := by
    rw [← triangle_sub _ _ (hcF image) (hcR image)]
    congr 1
    funext a b
    exact circle_source_difference q branch amp image p (p+width) X k a b
  simp only [action_triangles]
  linear_combination he false (p+width)/4-he true p/4

/-- The actual restored causal potential is the original direct-minus-image retarded
source action, with every original gradient and fixed-onset contribution retained. -/
theorem originalPotential_eq_retarded (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    originalPotential q branch amp p (p+width) X k=
      retardedNullAction (timeOriginalForcing q branch amp) p width X k := by
  have h := retarded_original_source_difference q branch amp p width X k
  rw [← fullNullResponse_eq_retarded_reduced q (physicalRate q branch) amp p width X k,
    retardedNullAction_lift_wave] at h
  have hl : timeLiftField q branch amp ((2*(p:ℝ)+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]=
      nullLift (physicalRate q branch) amp p (p+width)*sourceProfile q X k := by
    unfold timeLiftField timeRadialLift nullLift sourceProfile
    rw [show (2*(p:ℝ)+width)/2+ -(width:ℝ)/2=p by ring,
      show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring]
  rw [hl] at h
  unfold originalPotential
  linear_combination -h

/-- The constructed native potential retains the complete causal onset pulse when
expressed through the original angular seed and lift. -/
theorem originalPotential_onset_reconstruction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    originalPotential q branch amp p (p+width) X k=
      timeLiftField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]-
      timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]/
        D4BMGlobalAngularResponse.parameter q branch+
      retardedNullAction (fullSourceOnsetPulse q branch amp) p width X k/
        D4BMGlobalAngularResponse.parameter q branch := by
  rw [originalPotential_eq_retarded,originalForcing_retarded_reconstruction]

end
end RHTower.D4BMOriginalRetardedIdentity
