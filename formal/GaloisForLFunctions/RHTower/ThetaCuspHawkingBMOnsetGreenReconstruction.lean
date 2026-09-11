import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat
import Mathlib.MeasureTheory.Integral.Prod

/-! Original causal Green reconstruction of the fixed onset wave images. -/
/-! Finite causal reconstruction of the original theta-cusp forcing and onset pulse.

Reciprocal closed-cone Goursat primitives and two triangular Green identities recover
both actual wave images. Their AdS diagonal terms cancel only after direct and image
integration. Source-circle averaging and justified finite integral linearity then give
`R_F = lift - seed / alpha + R_P / alpha` for the unchanged forcing and onset pulse.
Physical radial/left-QNM domain admission and complete current extinction remain separate.
-/

namespace RHTower.D4BMOnsetGreenReconstruction
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularCircleAction D4BMFullAngularGoursat
open D4BMJointSource MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

@[fun_prop] private theorem integral_continuous {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (f : X → ℝ → ℂ) (hf : Continuous (Function.uncurry f))
    (l r : X → ℝ) (hl : Continuous l) (hr : Continuous r) :
    Continuous (fun x => ∫ t in l x..r x, f x t) := by
  have h₁ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hr
  have h₂ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hf hl
  convert! h₁.sub h₂ using 1
  funext x
  exact (intervalIntegral.integral_interval_sub_left
    ((hf.uncurry_left x).intervalIntegrable 0 (r x))
    ((hf.uncurry_left x).intervalIntegrable 0 (l x))).symm

private theorem rectangle_swap (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  exact (hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

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


private def triangle (f : ℝ → ℝ → ℂ) (p r : ℝ) : ℂ :=
  ∫ a in (0:ℝ)..p, ∫ b in a..r, f a b

private theorem slice_second (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) (a : ℝ) :
    Continuous (f a) := hf.comp (continuous_const.prodMk continuous_id)
private theorem slice_first (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) (b : ℝ) :
    Continuous (fun a => f a b) := hf.comp (continuous_id.prodMk continuous_const)

private theorem inner_continuous (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) (r : ℝ) :
    Continuous (fun a => ∫ b in a..r, f a b) :=
  integral_continuous f hf (fun a => a) (fun _ => r) continuous_id continuous_const

private theorem triangle_sub (f g : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    triangle (fun a b => f a b-g a b) p r=triangle f p r-triangle g p r := by
  unfold triangle
  simp_rw [intervalIntegral.integral_sub ((slice_second f hf _).intervalIntegrable _ _)
    ((slice_second g hg _).intervalIntegrable _ _)]
  exact intervalIntegral.integral_sub ((inner_continuous f hf r).intervalIntegrable _ _)
    ((inner_continuous g hg r).intervalIntegrable _ _)

private theorem triangle_split (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) (p r : ℝ) :
    triangle f p r=triangle f p p+∫ b in p..r, ∫ a in (0:ℝ)..p, f a b := by
  have he (a : ℝ) : (∫ b in a..r, f a b)=(∫ b in a..p, f a b)+(∫ b in p..r, f a b) :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((slice_second f hf a).intervalIntegrable _ _)
      ((slice_second f hf a).intervalIntegrable _ _)).symm
  unfold triangle
  simp_rw [he]
  rw [intervalIntegral.integral_add ((inner_continuous f hf p).intervalIntegrable _ _)
    ((integral_continuous f hf (fun _ => p) (fun _ => r) continuous_const continuous_const).intervalIntegrable _ _)]
  rw [rectangle_swap f hf 0 p p r]

private theorem triangle_first (A D : ℝ → ℝ → ℂ)
    (hA : Continuous (Function.uncurry A)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ a b, HasDerivAt (fun x => A x b) (D a b) a)
    {p r : ℝ} (hp : 0 ≤ p) :
    triangle D p r=(∫ b in p..r, A p b)-(∫ b in (0:ℝ)..r, A 0 b)+
      ∫ a in (0:ℝ)..p, A a a := by
  have hFTC (b u : ℝ) (hu : 0 ≤ u) : (∫ a in (0:ℝ)..u, D a b)=A u b-A 0 b :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu (slice_first A hA b).continuousOn
      (fun a _ => hd a b) ((slice_first D hD b).intervalIntegrable _ _)
  rw [triangle_split D hD p r]
  have ht : triangle D p p=∫ b in (0:ℝ)..p, A b b-A 0 b := by
    unfold triangle
    rw [triangle_swap D hD hp]
    apply intervalIntegral.integral_congr
    intro b hb
    exact hFTC b b (show 0 ≤ b from (show b ∈ Icc 0 p by simpa [uIcc_of_le hp] using hb).1)
  rw [ht]
  simp_rw [hFTC _ p hp]
  have hc : Continuous (fun a => A a a) := hA.comp (continuous_id.prodMk continuous_id)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
      ((slice_second A hA 0).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((slice_second A hA p).intervalIntegrable _ _)
      ((slice_second A hA 0).intervalIntegrable _ _)]
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((slice_second A hA 0).intervalIntegrable 0 p) ((slice_second A hA 0).intervalIntegrable p r)
  linear_combination -he

private theorem triangle_second (B E : ℝ → ℝ → ℂ)
    (hB : Continuous (Function.uncurry B)) (hE : Continuous (Function.uncurry E))
    (hd : ∀ a b, HasDerivAt (B a) (E a b) b)
    {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) :
    triangle E p r=∫ a in (0:ℝ)..p, B a r-B a a := by
  unfold triangle
  apply intervalIntegral.integral_congr
  intro a ha
  have ha' : a ≤ r := (show a ∈ Icc 0 p by simpa [uIcc_of_le hp] using ha).2.trans hpr
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha' (slice_second B hB a).continuousOn
    (fun b _ => hd a b) ((slice_second E hE a).intervalIntegrable _ _)

private theorem triangle_green (K Ka Kab beta betab betaab : ℝ → ℝ → ℂ)
    (hK : Continuous (Function.uncurry K)) (hKa : Continuous (Function.uncurry Ka))
    (hKab : Continuous (Function.uncurry Kab)) (hbeta : Continuous (Function.uncurry beta))
    (hbetab : Continuous (Function.uncurry betab)) (hbetaab : Continuous (Function.uncurry betaab))
    (hK_a : ∀ a b, HasDerivAt (fun x => K x b) (Ka a b) a)
    (hKa_b : ∀ a b, HasDerivAt (Ka a) (Kab a b) b)
    (hbeta_b : ∀ a b, HasDerivAt (beta a) (betab a b) b)
    (hbetab_a : ∀ a b, HasDerivAt (fun x => betab x b) (betaab a b) a)
    (hdiag : ∀ a, beta a a=0) (hpast : ∀ b, betab 0 b=0)
    {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) (hedge : ∀ a, Ka a r=0) :
    triangle (fun a b => K a b*betaab a b-beta a b*Kab a b) p r=
      (∫ b in p..r, K p b*betab p b)+∫ a in (0:ℝ)..p, K a a*betab a a := by
  have hfirst := triangle_first (fun a b => K a b*betab a b)
    (fun a b => Ka a b*betab a b+K a b*betaab a b)
    (hK.mul hbetab) ((hKa.mul hbetab).add (hK.mul hbetaab))
    (fun a b => (hK_a a b).mul (hbetab_a a b)) hp (r := r)
  have hsecond := triangle_second (fun a b => beta a b*Ka a b)
    (fun a b => betab a b*Ka a b+beta a b*Kab a b)
    (hbeta.mul hKa) ((hbetab.mul hKa).add (hbeta.mul hKab))
    (fun a b => (hbeta_b a b).mul (hKa_b a b)) hp hpr
  have he : (fun a b => K a b*betaab a b-beta a b*Kab a b)=
      fun a b => (Ka a b*betab a b+K a b*betaab a b)-
        (betab a b*Ka a b+beta a b*Kab a b) := by funext a b; ring
  rw [he,triangle_sub (fun a b => Ka a b*betab a b+K a b*betaab a b)
    (fun a b => betab a b*Ka a b+beta a b*Kab a b) ((hKa.mul hbetab).add (hK.mul hbetaab))
    ((hbetab.mul hKa).add (hbeta.mul hKab)),hfirst,hsecond]
  simp only [hpast,hedge,hdiag,mul_zero,zero_mul,sub_self,intervalIntegral.integral_zero,sub_zero]

private def firstPrimitive (g : ℝ → ℝ → ℂ) (u v : ℝ) : ℂ := ∫ t in (0:ℝ)..v, g u t
private def primitive (c : ℂ) (g : ℝ → ℝ → ℂ) (u v : ℝ) : ℂ :=
  c+∫ s in (0:ℝ)..u, firstPrimitive g s v

private theorem firstPrimitive_continuous (g : ℝ → ℝ → ℂ) (hg : Continuous (Function.uncurry g)) :
    Continuous (Function.uncurry (firstPrimitive g)) := by
  exact integral_continuous (fun z : ℝ × ℝ => fun t => g z.1 t)
    (hg.comp (show Continuous (fun z : (ℝ × ℝ) × ℝ => (z.1.1,z.2)) by fun_prop)) (fun _ => 0) Prod.snd continuous_const continuous_snd

private theorem primitive_continuous (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) : Continuous (Function.uncurry (primitive c g)) := by
  apply continuous_const.add
  exact integral_continuous (fun z : ℝ × ℝ => fun s => firstPrimitive g s z.2)
    ((firstPrimitive_continuous g hg).comp (show Continuous (fun z : (ℝ × ℝ) × ℝ => (z.2,z.1.2)) by fun_prop)) (fun _ => 0) Prod.fst
    continuous_const continuous_fst

private theorem firstPrimitive_second (g : ℝ → ℝ → ℂ) (hg : Continuous (Function.uncurry g)) (u v : ℝ) :
    HasDerivAt (firstPrimitive g u) (g u v) v := by
  have hc := slice_second g hg u
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 v)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

private theorem primitive_first (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (u v : ℝ) :
    HasDerivAt (fun a => primitive c g a v) (firstPrimitive g u v) u := by
  have hc := slice_first (firstPrimitive g) (firstPrimitive_continuous g hg) v
  simpa only [zero_add] using! (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_add c

private def backKernel (c : ℂ) (g : ℝ → ℝ → ℂ) (p r a b : ℝ) : ℂ :=
  primitive c g (p-a) (r-b)
private def backFirst (g : ℝ → ℝ → ℂ) (p r a b : ℝ) : ℂ :=
  -firstPrimitive g (p-a) (r-b)
private def backMixed (g : ℝ → ℝ → ℂ) (p r a b : ℝ) : ℂ := g (p-a) (r-b)

private theorem backKernel_continuous (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    Continuous (Function.uncurry (backKernel c g p r)) :=
  (primitive_continuous c g hg).comp (show Continuous (fun z : ℝ × ℝ => (p-z.1,r-z.2)) by fun_prop)
private theorem backFirst_continuous (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    Continuous (Function.uncurry (backFirst g p r)) :=
  ((firstPrimitive_continuous g hg).comp (show Continuous (fun z : ℝ × ℝ => (p-z.1,r-z.2)) by fun_prop)).neg
private theorem backMixed_continuous (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    Continuous (Function.uncurry (backMixed g p r)) := hg.comp (show Continuous (fun z : ℝ × ℝ => (p-z.1,r-z.2)) by fun_prop)

private theorem backKernel_first (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r a b : ℝ) :
    HasDerivAt (fun z => backKernel c g p r z b) (backFirst g p r a b) a := by
  apply ((primitive_first c g hg (p-a) (r-b)).scomp a ((hasDerivAt_id a).const_sub p)).congr_deriv
  simp only [backFirst,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul]

private theorem backFirst_second (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r a b : ℝ) :
    HasDerivAt (backFirst g p r a) (backMixed g p r a b) b := by
  apply (((firstPrimitive_second g hg (p-a) (r-b)).scomp b
    ((hasDerivAt_id b).const_sub r)).neg).congr_deriv
  simp only [backMixed,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,neg_neg]

private theorem backKernel_top (c : ℂ) (g : ℝ → ℝ → ℂ) (p r b : ℝ) :
    backKernel c g p r p b=c := by
  simp only [backKernel,primitive,sub_self,intervalIntegral.integral_same,add_zero]
private theorem backFirst_edge (g : ℝ → ℝ → ℂ) (p r a : ℝ) : backFirst g p r a r=0 := by
  simp only [backFirst,firstPrimitive,sub_self,intervalIntegral.integral_same,neg_zero]

private theorem backKernel_diagonal (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r a : ℝ) :
    backKernel c g p r a a=backKernel c (fun u v => g v u) r p a a := by
  unfold backKernel primitive firstPrimitive
  rw [rectangle_swap g hg 0 (p-a) 0 (r-a)]

private theorem paired_green (c : ℂ) (g beta betab betaab : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (hbeta : Continuous (Function.uncurry beta))
    (hbetab : Continuous (Function.uncurry betab)) (hbetaab : Continuous (Function.uncurry betaab))
    (hbeta_b : ∀ a b, HasDerivAt (beta a) (betab a b) b)
    (hbetab_a : ∀ a b, HasDerivAt (fun x => betab x b) (betaab a b) a)
    (hdiag : ∀ a, beta a a=0) (hpast : ∀ b, betab 0 b=0)
    {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) :
    triangle (fun a b => backKernel c g p r a b*betaab a b-beta a b*backMixed g p r a b) p r-
      triangle (fun a b => backKernel c (fun u v => g v u) r p a b*betaab a b-
        beta a b*backMixed (fun u v => g v u) r p a b) p p=c*beta p r := by
  have hgs : Continuous (Function.uncurry (fun u v => g v u)) := hg.comp continuous_swap
  have hd := triangle_green (backKernel c g p r) (backFirst g p r) (backMixed g p r)
    beta betab betaab (backKernel_continuous c g hg p r) (backFirst_continuous g hg p r)
    (backMixed_continuous g hg p r) hbeta hbetab hbetaab (backKernel_first c g hg p r)
    (backFirst_second g hg p r) hbeta_b hbetab_a hdiag hpast hp hpr (backFirst_edge g p r)
  have hi := triangle_green (backKernel c (fun u v => g v u) r p)
    (backFirst (fun u v => g v u) r p) (backMixed (fun u v => g v u) r p)
    beta betab betaab (backKernel_continuous c _ hgs r p) (backFirst_continuous _ hgs r p)
    (backMixed_continuous _ hgs r p) hbeta hbetab hbetaab (backKernel_first c _ hgs r p)
    (backFirst_second _ hgs r p) hbeta_b hbetab_a hdiag hpast hp (le_refl p)
    (backFirst_edge _ r p)
  rw [hd,hi]
  simp only [backKernel_top,intervalIntegral.integral_same,zero_add,
    backKernel_diagonal c g hg p r]
  rw [add_sub_cancel_right,intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpr
    (slice_second beta hbeta p).continuousOn (fun b _ => hbeta_b p b)
    ((slice_second betab hbetab p).intervalIntegrable p r),hdiag,sub_zero]

private def radialSeed (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (t : ℝ) : ℂ :=
  if i then sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch) t
  else radialLift (physicalRate q branch) 0 amp 1 t
private def radialSeedFirst (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (t : ℝ) : ℂ :=
  if i then sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) t
  else radialLiftFirst (physicalRate q branch) 0 amp 1 t
private def radialSeedSecond (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (t : ℝ) : ℂ :=
  if i then sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) t
  else radialLiftSecond (physicalRate q branch) 0 amp 1 t

private theorem radialSeed_first (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (t : ℝ) :
    HasDerivAt (radialSeed q branch amp i) (radialSeedFirst q branch amp i t) t := by
  cases i
  · exact radialLift_hasDerivAt _ _ _ _ _
  · exact sourceSeedField_hasDerivAt _ _ _ _ _ _
private theorem radialSeed_second (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (t : ℝ) :
    HasDerivAt (radialSeedFirst q branch amp i) (radialSeedSecond q branch amp i t) t := by
  cases i
  · exact radialLiftFirst_hasDerivAt _ _ _ _ _
  · exact sourceSeedFieldFirst_hasDerivAt _ _ _ _ _ _

private theorem radialSeed_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) :
    Continuous (radialSeed q branch amp i) :=
  continuous_iff_continuousAt.mpr (fun t => (radialSeed_first q branch amp i t).continuousAt)
private theorem radialSeedFirst_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) :
    Continuous (radialSeedFirst q branch amp i) :=
  continuous_iff_continuousAt.mpr (fun t => (radialSeed_second q branch amp i t).continuousAt)
private theorem radialSeedSecond_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) :
    Continuous (radialSeedSecond q branch amp i) := by
  have hA : Continuous (sourceAmplitude (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t => (sourceAmplitude_hasDerivAt _ _ _ _ t).continuousAt)
  have hU : Continuous radialUnit :=
    continuous_iff_continuousAt.mpr (fun t => (radialUnit_hasDerivAt t).continuousAt)
  cases i
  · change Continuous (fun t => radialLiftSecond (physicalRate q branch) 0 amp 1 t)
    dsimp only [radialLiftSecond,liftSecondPolynomial,amplitudeRate]
    fun_prop
  · change Continuous (fun t => sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) t)
    dsimp only [sourceSeedFieldSecond,sourceSeedPolynomial,sourceSeedFirst,sourceSeedSecond,amplitudeRate]
    fun_prop

private theorem radialSeed_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) :
    radialSeed q branch amp i 0=0 := by
  cases i <;> simp [radialSeed,radialLift,sourceSeedField,sourceSeedPolynomial,radialUnit]

private def beta (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (a b : ℝ) : ℂ :=
  radialSeed q branch amp i ((a-b)/2)*timeOnset (2*physicalRate q branch) a
private def betaB (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (a b : ℝ) : ℂ :=
  -radialSeedFirst q branch amp i ((a-b)/2)/2*timeOnset (2*physicalRate q branch) a
private def betaAB (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (a b : ℝ) : ℂ :=
  -radialSeedSecond q branch amp i ((a-b)/2)/4*timeOnset (2*physicalRate q branch) a-
    radialSeedFirst q branch amp i ((a-b)/2)/2*timeOnsetFirst (2*physicalRate q branch) a

private theorem onset_continuous (v : ℂ) : Continuous (timeOnset v) :=
  continuous_iff_continuousAt.mpr (fun t => (timeOnset_hasDerivAt v t).continuousAt)
private theorem onsetFirst_continuous (v : ℂ) : Continuous (timeOnsetFirst v) :=
  continuous_iff_continuousAt.mpr (fun t => (timeOnsetFirst_hasDerivAt v t).continuousAt)

private theorem beta_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) :
    Continuous (Function.uncurry (beta q branch amp i)) :=
  ((radialSeed_continuous q branch amp i).comp (show Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) by fun_prop)).mul
    ((onset_continuous _).comp continuous_fst)
private theorem betaB_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) :
    Continuous (Function.uncurry (betaB q branch amp i)) :=
  ((((radialSeedFirst_continuous q branch amp i).comp (show Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) by fun_prop)).neg).div_const 2).mul
    ((onset_continuous _).comp continuous_fst)
private theorem betaAB_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) :
    Continuous (Function.uncurry (betaAB q branch amp i)) :=
  (((((radialSeedSecond_continuous q branch amp i).comp (show Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) by fun_prop)).neg).div_const 4).mul
    ((onset_continuous _).comp continuous_fst)).sub
      ((((radialSeedFirst_continuous q branch amp i).comp (show Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) by fun_prop)).div_const 2).mul
        ((onsetFirst_continuous _).comp continuous_fst))

private theorem beta_second (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (a b : ℝ) :
    HasDerivAt (beta q branch amp i a) (betaB q branch amp i a b) b := by
  have hd := (radialSeed_first q branch amp i ((a-b)/2)).scomp b
    (((hasDerivAt_id b).const_sub a).div_const 2)
  apply (hd.mul_const (timeOnset (2*physicalRate q branch) a)).congr_deriv
  dsimp only [betaB]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem betaB_first (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (a b : ℝ) :
    HasDerivAt (fun z => betaB q branch amp i z b) (betaAB q branch amp i a b) a := by
  have hd := (radialSeed_second q branch amp i ((a-b)/2)).scomp a
    (((hasDerivAt_id a).sub_const b).div_const 2)
  apply (((hd.neg).div_const 2).mul (timeOnset_hasDerivAt (2*physicalRate q branch) a)).congr_deriv
  dsimp only [betaAB]
  simp only [Function.comp_apply, Pi.neg_apply, id_eq, Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem beta_diagonal (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (a : ℝ) :
    beta q branch amp i a a=0 := by
  simp only [beta,sub_self,zero_div,radialSeed_zero,zero_mul]
private theorem betaB_past (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) (b : ℝ) :
    betaB q branch amp i 0 b=0 := by
  rw [betaB,timeOnset_zero_of_nonpos _ (le_refl 0),mul_zero]

open D4BMNativeCircle UpperHalfPlane D4BMAngularSeries

private theorem laplace_circle_smooth (q : XiZeroCopy) (X k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k)) := by
  have hp (p : ℝ × ℝ) : 0 < logCircle p.1 p.2 X k 1 :=
    mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have he : (fun p : ℝ × ℝ => scalarLaplacian (fullSquarePotential q) (logCircle p.1 p.2 X k))=
      fun p => (logCircle p.1 p.2 X k 1:ℂ)^2*
        (coordDeriv 0 (coordDeriv 0 (fullSquarePotential q)) (logCircle p.1 p.2 X k)+
         coordDeriv 1 (coordDeriv 1 (fullSquarePotential q)) (logCircle p.1 p.2 X k)) := by
    funext p
    exact scalarLaplacian_eq _ _ (hp p)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hs : ContDiffAt ℝ ∞ (fullSquarePotential q) (logCircle p.1 p.2 X k) :=
    contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (hp p) n)
  have hj (i : Fin 2) : ContDiffAt ℝ ∞ (coordDeriv i (coordDeriv i (fullSquarePotential q)))
      (logCircle p.1 p.2 X k) :=
    coordDeriv_contDiffAt (m := ∞)
      (by simpa using coordDeriv_contDiffAt (m := ∞) (by simpa using hs) i) i
  have hc : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => logCircle r.1 r.2 X k) p := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := exact (denominator_pos _ _).ne')
  have hy : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => (logCircle r.1 r.2 X k 1:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_pi.mp hc 1)
  exact (hy.pow 2).mul (((hj 0).comp p hc).add ((hj 1).comp p hc))


private def laplaceMean (q : XiZeroCopy) (d X k : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle d theta X k))

private theorem average_parameter_continuous (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    Continuous (fun t => D4BMNativeCircle.average (fun theta => F (t,theta))) := by
  have he : (fun t => D4BMNativeCircle.average (fun theta => F (t,theta))) = fun t =>
      (1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..2*Real.pi, F (t,theta) := by
    funext t
    rw [intervalIntegral.integral_of_le (by positivity)]
    rfl
  rw [he]
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t theta => F (t,theta)) hF continuous_const)

private theorem laplaceMean_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (fun d => laplaceMean q d X k) :=
  average_parameter_continuous _ (laplace_circle_smooth q X k).continuous

private def field (q : XiZeroCopy) (branch i : Bool) (X k : ℝ) : ℂ :=
  if i then fullAngularField q branch ![X,Real.exp k] else fullSquarePotential q ![X,Real.exp k]
private def circleMean (q : XiZeroCopy) (branch i : Bool) (d X k : ℝ) : ℂ :=
  if i then angularMean q branch d X k else D4BMNativeCircle.mean q d X k
private def circleAction (q : XiZeroCopy) (branch i : Bool) (d X k : ℝ) : ℂ :=
  if i then parameter q branch*(angularMean q branch d X k+D4BMNativeCircle.mean q d X k)
  else laplaceMean q d X k
private def kernel (q : XiZeroCopy) (branch i : Bool) (h x y X k : ℝ) : ℂ :=
  circleMean q branch i (Real.arcosh (invariant h x y)) X k
private def radius (z : ℝ) : ℝ := Real.arcosh (max 1 z)
private def forcing (q : XiZeroCopy) (branch i : Bool) (x X k u v : ℝ) : ℂ :=
  circleAction q branch i (radius (invariant ((u+v)/2) (x+(v-u)/2) x)) X k/
    (4*(Real.cosh (x+(v-u)/2):ℂ)^2)

private theorem circleAction_continuous (q : XiZeroCopy) (branch i : Bool) (X k : ℝ) :
    Continuous (fun d => circleAction q branch i d X k) := by
  cases i
  · exact laplaceMean_continuous q X k
  · exact continuous_const.mul ((angularMean_smooth q branch X k).continuous.add
      (D4BMNativeCircle.mean_radial_smooth q X k).continuous)
private theorem radius_continuous : Continuous radius :=
  Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun z => le_max_left 1 z)
private theorem forcing_continuous (q : XiZeroCopy) (branch i : Bool) (x X k : ℝ) :
    Continuous (Function.uncurry (forcing q branch i x X k)) := by
  have hz : Continuous (fun z : ℝ × ℝ => invariant ((z.1+z.2)/2) (x+(z.2-z.1)/2) x) := by
    unfold invariant
    exact (show Continuous (fun z : ℝ × ℝ => Real.cosh ((z.1+z.2)/2)+
      Real.sinh (x+(z.2-z.1)/2)*Real.sinh x) by fun_prop).div
      (by fun_prop) (fun z => mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne')
  exact ((circleAction_continuous q branch i X k).comp (radius_continuous.comp hz)).div
    (by fun_prop) (fun z => mul_ne_zero (by norm_num)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')))
private theorem null_cone (x : ℝ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |x+(v-u)/2-x| ≤ (u+v)/2 := by
  apply abs_le.mpr
  constructor <;> linarith
private theorem forcing_raw (q : XiZeroCopy) (branch i : Bool) (x X k : ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    forcing q branch i x X k u v=
      circleAction q branch i (Real.arcosh (invariant ((u+v)/2) (x+(v-u)/2) x)) X k/
        (4*(Real.cosh (x+(v-u)/2):ℂ)^2) := by
  have hz := invariant_causal (⟨_,_,_,null_cone x hu hv⟩ : CausalPoint)
  dsimp only [forcing,radius]
  rw [max_eq_right hz]
private theorem invariant_reciprocal (h x y : ℝ) : invariant h x y=invariant h y x := by
  unfold invariant
  rw [mul_comm (Real.sinh x),mul_comm (Real.cosh x)]
private theorem kernel_reciprocal (q : XiZeroCopy) (branch i : Bool) (h x y X k : ℝ) :
    kernel q branch i h x y X k=kernel q branch i h y x X k := by
  unfold kernel
  rw [invariant_reciprocal]

private theorem kernel_goursat (q : XiZeroCopy) (branch i : Bool) (p : CausalPoint) (X k : ℝ) :
    kernel q branch i p.time p.target p.source X k=field q branch i X k+
      ∫ a in (0:ℝ)..(p.time+p.target-p.source), ∫ b in (0:ℝ)..(p.time-p.target+p.source),
        circleAction q branch i
          (Real.arcosh (invariant ((a+b)/2) (p.source+(a-b)/2) p.source)) X k/
          (4*(Real.cosh (p.source+(a-b)/2):ℂ)^2) := by
  cases i
  · have h := nativeRiemannKernel_goursat q p X k
    have he (z : ℝ) : D4BMNativeCircle.angularAction q z X k=laplaceMean q (Real.arcosh z) X k :=
      mean_laplacian_commutes q (Real.arcosh z) X k
    simpa only [kernel,circleMean,field,circleAction,↓reduceIte,nativeRiemannKernel,
      D4BMNativeCircle.angularKernel,he] using! h
  · exact fullAngularRiemannKernel_goursat q branch p X k

private theorem primitive_kernel (q : XiZeroCopy) (branch i : Bool) (x X k : ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    primitive (field q branch i X k) (forcing q branch i x X k) u v=
      kernel q branch i ((u+v)/2) x (x+(v-u)/2) X k := by
  rw [kernel_reciprocal]
  have h := kernel_goursat q branch i (⟨_,_,_,null_cone x hu hv⟩ : CausalPoint) X k
  dsimp only at h
  rw [show (u+v)/2+(x+(v-u)/2)-x=v by ring,
    show (u+v)/2-(x+(v-u)/2)+x=u by ring] at h
  rw [h]
  unfold primitive firstPrimitive
  rw [rectangle_swap _ (forcing_continuous q branch i x X k) 0 u 0 v]
  apply congrArg (fun z : ℂ => field q branch i X k+z)
  apply intervalIntegral.integral_congr
  intro a ha
  have ha₀ := (show a ∈ Icc 0 v by simpa [uIcc_of_le hv] using ha).1
  apply intervalIntegral.integral_congr
  intro b hb
  have hb₀ := (show b ∈ Icc 0 u by simpa [uIcc_of_le hu] using hb).1
  dsimp only
  rw [forcing_raw q branch i x X k hb₀ ha₀]
  rw [add_comm b a]

private theorem primitive_swap (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (u v : ℝ) :
    primitive c (fun a b => g b a) u v=primitive c g v u := by
  unfold primitive firstPrimitive
  apply congrArg (fun z : ℂ => c+z)
  exact rectangle_swap (fun a b => g b a) (hg.comp continuous_swap) 0 u 0 v

private def sourceKernel (q : XiZeroCopy) (branch i image : Bool)
    (p r X k a b : ℝ) : ℂ :=
  kernel q branch i ((p+r-a-b)/2) ((p-r)/2)
    (if image then -(a-b)/2 else (a-b)/2) X k
private def sourceAction (q : XiZeroCopy) (branch i image : Bool)
    (p r X k a b : ℝ) : ℂ :=
  circleAction q branch i
    (Real.arcosh (invariant ((p+r-a-b)/2) ((p-r)/2)
      (if image then -(a-b)/2 else (a-b)/2))) X k/
      (4*(Real.cosh ((a-b)/2):ℂ)^2)
private def waveIntegrand (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i image : Bool)
    (p r X k a b : ℝ) : ℂ :=
  sourceKernel q branch i image p r X k a b*betaAB q branch amp i a b-
    beta q branch amp i a b*sourceAction q branch i image p r X k a b

private theorem direct_kernel (q : XiZeroCopy) (branch i : Bool) (p r X k a b : ℝ)
    (ha : a ≤ p) (hb : b ≤ r) :
    backKernel (field q branch i X k) (forcing q branch i ((p-r)/2) X k) p r a b=
      sourceKernel q branch i false p r X k a b := by
  rw [backKernel,primitive_kernel q branch i _ X k (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  unfold sourceKernel
  rw [show (p-a+(r-b))/2=(p+r-a-b)/2 by ring,
    show (p-r)/2+(r-b-(p-a))/2=(a-b)/2 by ring]
  rfl
private theorem image_kernel (q : XiZeroCopy) (branch i : Bool) (p r X k a b : ℝ)
    (ha : a ≤ p) (hpr : p ≤ r) (hb : b ≤ p) :
    backKernel (field q branch i X k) (fun u v => forcing q branch i ((p-r)/2) X k v u) r p a b=
      sourceKernel q branch i true p r X k a b := by
  rw [backKernel,primitive_swap _ _ (forcing_continuous q branch i _ X k),
    primitive_kernel q branch i _ X k (sub_nonneg.mpr hb) (sub_nonneg.mpr (ha.trans hpr))]
  unfold sourceKernel
  rw [show (p-b+(r-a))/2=(p+r-a-b)/2 by ring,
    show (p-r)/2+(r-a-(p-b))/2=-(a-b)/2 by ring]
  rfl
private theorem direct_action (q : XiZeroCopy) (branch i : Bool) (p r X k a b : ℝ)
    (ha : a ≤ p) (hb : b ≤ r) :
    backMixed (forcing q branch i ((p-r)/2) X k) p r a b=
      sourceAction q branch i false p r X k a b := by
  rw [backMixed,forcing_raw q branch i _ X k (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  rw [show (p-a+(r-b))/2=(p+r-a-b)/2 by ring,
    show (p-r)/2+(r-b-(p-a))/2=(a-b)/2 by ring,
    invariant_reciprocal]
  rfl
private theorem image_action (q : XiZeroCopy) (branch i : Bool) (p r X k a b : ℝ)
    (ha : a ≤ p) (hpr : p ≤ r) (hb : b ≤ p) :
    backMixed (fun u v => forcing q branch i ((p-r)/2) X k v u) r p a b=
      sourceAction q branch i true p r X k a b := by
  rw [backMixed,forcing_raw q branch i _ X k (sub_nonneg.mpr hb) (sub_nonneg.mpr (ha.trans hpr))]
  rw [show (p-b+(r-a))/2=(p+r-a-b)/2 by ring,
    show (p-r)/2+(r-a-(p-b))/2=-(a-b)/2 by ring,
    show -(a-b)/2=-((a-b)/2) by ring,Real.cosh_neg,invariant_reciprocal]
  simp only [sourceAction,↓reduceIte,neg_div]

private def angularField (q : XiZeroCopy) (branch i : Bool) (z : Point) : ℂ :=
  if i then fullAngularField q branch z else fullSquarePotential q z
private theorem angularField_false (q : XiZeroCopy) (branch : Bool) :
    angularField q branch false=fullSquarePotential q := rfl
private theorem angularField_true (q : XiZeroCopy) (branch : Bool) :
    angularField q branch true=fullAngularField q branch := rfl
private def onsetField (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool) : ℝ → ℝ → Point → ℂ :=
  if i then timeAngularSeedField q branch amp else timeLiftField q branch amp
private theorem angularField_smooth (q : XiZeroCopy) (branch i : Bool)
    (z : Point) (hz : 0 < z 1) : ContDiffAt ℝ ∞ (angularField q branch i) z := by
  cases i
  · exact contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q z hz n)
  · exact fullAngularField_smooth q branch z hz
private theorem logCircle_smooth (X k : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => logCircle p.1 p.2 X k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := intro z; exact (denominator_pos z.1 z.2).ne')
private theorem angularField_circle_continuous (q : XiZeroCopy) (branch i : Bool) (X k : ℝ) :
    Continuous (fun p : ℝ × ℝ => angularField q branch i (logCircle p.1 p.2 X k)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ((angularField_smooth q branch i (logCircle p.1 p.2 X k)
    (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))).continuousAt).comp (f := fun r : ℝ × ℝ => logCircle r.1 r.2 X k)
      (logCircle_smooth X k).continuous.continuousAt
private theorem angularField_theta_continuous (q : XiZeroCopy) (branch i : Bool) (d X k : ℝ) :
    Continuous (fun theta => angularField q branch i (logCircle d theta X k)) :=
  (angularField_circle_continuous q branch i X k).comp
    (f := fun theta : ℝ => (d,theta)) (show Continuous (fun theta : ℝ => (d,theta)) by fun_prop)
private theorem angularField_average (q : XiZeroCopy) (branch i : Bool) (d X k : ℝ) :
    D4BMNativeCircle.average (fun theta => angularField q branch i (logCircle d theta X k))=circleMean q branch i d X k := by
  cases i <;> rfl
private theorem average_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    D4BMNativeCircle.average (fun theta => f theta+g theta)=D4BMNativeCircle.average f+D4BMNativeCircle.average g := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_add (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring
private theorem average_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    D4BMNativeCircle.average (fun theta => f theta-g theta)=D4BMNativeCircle.average f-D4BMNativeCircle.average g := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_sub (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring
private theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) :
    D4BMNativeCircle.average (fun theta => c*f theta)=c*D4BMNativeCircle.average f := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_const_mul]
  ring

private theorem angularField_equation (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (angularField q branch true) z=
      parameter q branch*(angularField q branch true z+angularField q branch false z) := by
  simp only [angularField_true,angularField_false]
  have h := fullAngularField_equation q branch z hz
  dsimp only [fullSquarePotential]
  linear_combination h
private theorem angularAction_average (q : XiZeroCopy) (branch i : Bool) (d X k : ℝ) :
    D4BMNativeCircle.average (fun theta => scalarLaplacian (angularField q branch i) (logCircle d theta X k))=
      circleAction q branch i d X k := by
  cases i
  · rfl
  · have he (theta : ℝ) : scalarLaplacian (angularField q branch true) (logCircle d theta X k)=
        parameter q branch*(angularField q branch true (logCircle d theta X k)+
          angularField q branch false (logCircle d theta X k)) := by
      exact angularField_equation q branch (logCircle d theta X k)
        (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))
    simp_rw [he]
    rw [average_const_mul,average_add (angularField_theta_continuous q branch true d X k)
      (angularField_theta_continuous q branch false d X k),angularField_average,angularField_average]
    rfl
private theorem angularAction_theta_continuous (q : XiZeroCopy) (branch i : Bool) (d X k : ℝ) :
    Continuous (fun theta => scalarLaplacian (angularField q branch i) (logCircle d theta X k)) := by
  cases i
  · rw [angularField_false]
    exact (laplace_circle_smooth q X k).continuous.comp
      (f := fun theta : ℝ => (d,theta)) (show Continuous (fun theta : ℝ => (d,theta)) by fun_prop)
  · have he : (fun theta => scalarLaplacian (angularField q branch true) (logCircle d theta X k))=
        fun theta => parameter q branch*(angularField q branch true (logCircle d theta X k)+
          angularField q branch false (logCircle d theta X k)) := by
      funext theta
      exact angularField_equation q branch (logCircle d theta X k)
        (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))
    rw [he]
    exact continuous_const.mul ((angularField_theta_continuous q branch true d X k).add
      (angularField_theta_continuous q branch false d X k))
private theorem radial_metric (t : ℝ) : 1-(radialUnit t:ℂ)^2=1/(Real.cosh t:ℂ)^2 := by
  have hn : (Real.cosh t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have he : (Real.cosh t:ℂ)^2-(Real.sinh t:ℂ)^2=1 := by exact_mod_cast Real.cosh_sq_sub_sinh_sq t
  dsimp only [radialUnit]
  simp only [Complex.ofReal_div,Complex.ofReal_neg]
  field_simp [hn]
  linear_combination he

private theorem onsetField_wave (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool)
    (a b : ℝ) (z : Point) (hz : 0 < z 1) :
    timeFieldWave (onsetField q branch amp i) ((a+b)/2) ((a-b)/2) z=
      4*betaAB q branch amp i a b*angularField q branch i z-
        beta q branch amp i a b*scalarLaplacian (angularField q branch i) z/
          (Real.cosh ((a-b)/2):ℂ)^2 := by
  have ht : (a+b)/2+(a-b)/2=a := by ring
  cases i
  · rw [show onsetField q branch amp false=timeLiftField q branch amp by rfl,
      timeLiftField_wave q branch amp _ _ z hz,separatedScalarWave,
      (radialLift_derivatives (physicalRate q branch) 0 amp 1).2,radial_metric,ht]
    dsimp only [betaAB,beta,radialSeed,radialSeedFirst,radialSeedSecond,angularField]
    simp only [Bool.false_eq_true,↓reduceIte,angularField_false]
    ring
  · have hL : scalarLaplacian (fun y =>
        timeSourceSeed (physicalRate q branch) amp (parameter q branch) ((a+b)/2) ((a-b)/2)*
          fullAngularField q branch y) z=
        timeSourceSeed (physicalRate q branch) amp (parameter q branch) ((a+b)/2) ((a-b)/2)*
          scalarLaplacian (fullAngularField q branch) z := by
      rw [scalarLaplacian_eq _ z hz,scalarLaplacian_eq _ z hz]
      apply hyperbolicLaplacian_const_mul
      simpa using (contDiffAt_infty.mp (fullAngularField_smooth q branch z hz)) 2
    change timeFieldWave (timeAngularSeedField q branch amp) _ _ z=_
    unfold timeFieldWave timeAngularSeedField
    simp only [deriv_mul_const_field',deriv_mul_const_field]
    rw [hL,← sub_mul,timeSourceSeed_wave,radial_metric,ht]
    dsimp only [betaAB,beta,radialSeed,radialSeedFirst,radialSeedSecond,angularField,timeSourceSeed]
    simp only [↓reduceIte,ht,angularField_true]
    ring

private theorem onsetField_wave_average (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool)
    (a b d X k : ℝ) :
    D4BMNativeCircle.average (fun theta => timeFieldWave (onsetField q branch amp i) ((a+b)/2) ((a-b)/2)
      (logCircle d theta X k))=
      4*betaAB q branch amp i a b*circleMean q branch i d X k-
        beta q branch amp i a b*circleAction q branch i d X k/(Real.cosh ((a-b)/2):ℂ)^2 := by
  have he (theta : ℝ) := onsetField_wave q branch amp i a b (logCircle d theta X k)
    (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))
  simp_rw [he,div_eq_mul_inv,mul_right_comm (beta q branch amp i a b)]
  rw [average_sub ((angularField_theta_continuous q branch i d X k).const_mul _)
    ((angularAction_theta_continuous q branch i d X k).const_mul _),
    average_const_mul,average_const_mul,angularField_average,angularAction_average]
/-- The original retarded circular action in source null coordinates.
The direct triangle is `0≤a≤p, a≤b≤r`; the image triangle is `0≤a≤p, a≤b≤p`.
The factor one quarter combines the original kernel factor one half and null Jacobian. -/
def retardedNullAction (S : ℝ → ℝ → Point → ℂ) (p width : NNReal) (X k : ℝ) : ℂ :=
  (∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..((p:ℝ)+width),
    D4BMNativeCircle.average (fun theta => S ((a+b)/2) ((a-b)/2)
      (logCircle (radius (invariant ((2*p+width-a-b)/2) (-(width:ℝ)/2) ((a-b)/2))) theta X k)))/4-
  (∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..(p:ℝ),
    D4BMNativeCircle.average (fun theta => S ((a+b)/2) ((a-b)/2)
      (logCircle (radius (invariant ((2*p+width-a-b)/2) (-(width:ℝ)/2) (-(a-b)/2))) theta X k)))/4

private def extendedWave (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i image : Bool)
    (p r X k a b : ℝ) : ℂ :=
  if image then
    backKernel (field q branch i X k) (fun u v => forcing q branch i ((p-r)/2) X k v u) r p a b*
      betaAB q branch amp i a b-beta q branch amp i a b*
        backMixed (fun u v => forcing q branch i ((p-r)/2) X k v u) r p a b
  else
    backKernel (field q branch i X k) (forcing q branch i ((p-r)/2) X k) p r a b*
      betaAB q branch amp i a b-beta q branch amp i a b*
        backMixed (forcing q branch i ((p-r)/2) X k) p r a b
private theorem extendedWave_eq (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i image : Bool)
    (p r X k a b : ℝ) (ha : a ≤ p) (hpr : p ≤ r) (hb : b ≤ if image then p else r) :
    extendedWave q branch amp i image p r X k a b=waveIntegrand q branch amp i image p r X k a b := by
  cases image
  · change b ≤ r at hb
    change _=sourceKernel q branch i false p r X k a b*_-_*sourceAction q branch i false p r X k a b
    rw [← direct_kernel q branch i p r X k a b ha hb,← direct_action q branch i p r X k a b ha hb]
    rfl
  · change b ≤ p at hb
    change _=sourceKernel q branch i true p r X k a b*_-_*sourceAction q branch i true p r X k a b
    rw [← image_kernel q branch i p r X k a b ha hpr hb,← image_action q branch i p r X k a b ha hpr hb]
    rfl
private theorem extendedWave_green (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool)
    (p r X k : ℝ) (hp : 0 ≤ p) (hpr : p ≤ r) :
    triangle (extendedWave q branch amp i false p r X k) p r-
      triangle (extendedWave q branch amp i true p r X k) p p=
        field q branch i X k*beta q branch amp i p r :=
  paired_green (field q branch i X k) (forcing q branch i ((p-r)/2) X k)
    (beta q branch amp i) (betaB q branch amp i) (betaAB q branch amp i)
    (forcing_continuous q branch i _ X k) (beta_continuous q branch amp i)
    (betaB_continuous q branch amp i) (betaAB_continuous q branch amp i)
    (beta_second q branch amp i) (betaB_first q branch amp i) (beta_diagonal q branch amp i)
    (betaB_past q branch amp i) hp hpr

private theorem triangle_congr {f g : ℝ → ℝ → ℂ} {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r)
    (he : ∀ a ∈ Icc 0 p, ∀ b ∈ Icc a r, f a b=g a b) : triangle f p r=triangle g p r := by
  unfold triangle
  apply intervalIntegral.integral_congr
  intro a ha
  have ha' : a ∈ Icc 0 p := by simpa [uIcc_of_le hp] using ha
  apply intervalIntegral.integral_congr
  intro b hb
  exact he a ha' b (by simpa [uIcc_of_le (ha'.2.trans hpr)] using hb)
private theorem source_cone (image : Bool) (p r a b : ℝ)
    (ha : a ≤ p) (hpr : p ≤ r) (_hab : a ≤ b) (hb : b ≤ if image then p else r) :
    |(p-r)/2-(if image then -(a-b)/2 else (a-b)/2)| ≤ (p+r-a-b)/2 := by
  cases image <;> simp only [Bool.false_eq_true,↓reduceIte] at hb ⊢
  all_goals apply abs_le.mpr; constructor <;> linarith
private def circleSource (S : ℝ → ℝ → Point → ℂ) (image : Bool) (p r X k a b : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta => S ((a+b)/2) ((a-b)/2)
    (logCircle (radius (invariant ((p+r-a-b)/2) ((p-r)/2)
      (if image then -(a-b)/2 else (a-b)/2))) theta X k))/4
private theorem action_eq_triangles (S : ℝ → ℝ → Point → ℂ) (p width : NNReal) (X k : ℝ) :
    retardedNullAction S p width X k=
      triangle (circleSource S false p (p+width) X k) p (p+width)-
      triangle (circleSource S true p (p+width) X k) p p := by
  unfold retardedNullAction triangle circleSource
  simp only [Bool.false_eq_true,↓reduceIte]
  simp_rw [intervalIntegral.integral_div]
  rw [show (p:ℝ)+((p:ℝ)+width)=2*p+width by ring,
    show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring]

private theorem wave_circleSource (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i image : Bool)
    (p r X k a b : ℝ) (ha : a ≤ p) (hpr : p ≤ r) (hab : a ≤ b)
    (hb : b ≤ if image then p else r) :
    circleSource (timeFieldWave (onsetField q branch amp i)) image p r X k a b=
      extendedWave q branch amp i image p r X k a b := by
  have hz := invariant_causal (⟨_,_,_,source_cone image p r a b ha hpr hab hb⟩ : CausalPoint)
  rw [circleSource,onsetField_wave_average,extendedWave_eq q branch amp i image p r X k a b ha hpr hb]
  dsimp only [waveIntegrand,sourceKernel,sourceAction,kernel,radius]
  rw [max_eq_right hz]
  ring

/-- The original retarded direct/image action reconstructs the constructed angular seed. -/
theorem retardedNullAction_seed_wave (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    retardedNullAction (timeFieldWave (timeAngularSeedField q branch amp)) p width X k=
      timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k] := by
  have hp : 0 ≤ (p:ℝ) := p.property
  have hr : (p:ℝ) ≤ (p:ℝ)+width := by exact le_add_of_nonneg_right width.property
  rw [action_eq_triangles]
  have hd := triangle_congr hp hr (fun a ha b hb =>
    wave_circleSource q branch amp true false p (p+width) X k a b ha.2 hr hb.1 hb.2)
  have hi := triangle_congr hp (le_refl (p:ℝ)) (fun a ha b hb =>
    wave_circleSource q branch amp true true p (p+width) X k a b ha.2 hr hb.1 hb.2)
  simp only [onsetField,↓reduceIte] at hd hi
  rw [hd,hi,extendedWave_green q branch amp true _ _ X k hp hr]
  dsimp only [field,beta,radialSeed,timeAngularSeedField,timeSourceSeed]
  simp only [↓reduceIte]
  rw [show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring,
    show (2*(p:ℝ)+width)/2+ -(width:ℝ)/2=p by ring]
  ring

/-- The original retarded direct/image action reconstructs the prescribed half-square lift. -/
theorem retardedNullAction_lift_wave (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    retardedNullAction (timeFieldWave (timeLiftField q branch amp)) p width X k=
      timeLiftField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k] := by
  have hp : 0 ≤ (p:ℝ) := p.property
  have hr : (p:ℝ) ≤ (p:ℝ)+width := by exact le_add_of_nonneg_right width.property
  rw [action_eq_triangles]
  have hd := triangle_congr hp hr (fun a ha b hb =>
    wave_circleSource q branch amp false false p (p+width) X k a b ha.2 hr hb.1 hb.2)
  have hi := triangle_congr hp (le_refl (p:ℝ)) (fun a ha b hb =>
    wave_circleSource q branch amp false true p (p+width) X k a b ha.2 hr hb.1 hb.2)
  simp only [onsetField,Bool.false_eq_true,↓reduceIte] at hd hi
  rw [hd,hi,extendedWave_green q branch amp false _ _ X k hp hr]
  dsimp only [field,beta,radialSeed,timeLiftField,timeRadialLift]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring,
    show (2*(p:ℝ)+width)/2+ -(width:ℝ)/2=p by ring]
  ring

private theorem sourceRadius_continuous (image : Bool) (p r : ℝ) :
    Continuous (fun z : ℝ × ℝ => radius (invariant ((p+r-z.1-z.2)/2) ((p-r)/2)
      (if image then -(z.1-z.2)/2 else (z.1-z.2)/2))) := by
  apply radius_continuous.comp
  unfold invariant
  cases image <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z
      exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
private theorem circleMean_continuous (q : XiZeroCopy) (branch i : Bool) (X k : ℝ) :
    Continuous (fun d => circleMean q branch i d X k) := by
  cases i
  · exact (D4BMNativeCircle.mean_radial_smooth q X k).continuous
  · exact (angularMean_smooth q branch X k).continuous
private theorem circleSource_wave_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (i image : Bool) (p r X k : ℝ) :
    Continuous (Function.uncurry (circleSource (timeFieldWave (onsetField q branch amp i)) image p r X k)) := by
  have hM := (circleMean_continuous q branch i X k).comp (sourceRadius_continuous image p r)
  have hL := (circleAction_continuous q branch i X k).comp (sourceRadius_continuous image p r)
  have he : Function.uncurry (circleSource (timeFieldWave (onsetField q branch amp i)) image p r X k)=
      fun z : ℝ × ℝ =>
        (4*betaAB q branch amp i z.1 z.2*
          circleMean q branch i (radius (invariant ((p+r-z.1-z.2)/2) ((p-r)/2)
            (if image then -(z.1-z.2)/2 else (z.1-z.2)/2))) X k-
          beta q branch amp i z.1 z.2*
          circleAction q branch i (radius (invariant ((p+r-z.1-z.2)/2) ((p-r)/2)
            (if image then -(z.1-z.2)/2 else (z.1-z.2)/2))) X k/
            (Real.cosh ((z.1-z.2)/2):ℂ)^2)/4 := by
    funext z
    exact congrArg (fun v : ℂ => v/4) (onsetField_wave_average q branch amp i z.1 z.2 _ X k)
  rw [he]
  exact ((((betaAB_continuous q branch amp i).const_mul 4).mul hM).sub
    (((beta_continuous q branch amp i).mul hL).div (by fun_prop)
      (fun z => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')))).div_const 4
private theorem circleSource_pulse_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p r X k : ℝ) :
    Continuous (Function.uncurry (circleSource (fullSourceOnsetPulse q branch amp) image p r X k)) := by
  have hH := (circleMean_continuous q branch true X k).comp (sourceRadius_continuous image p r)
  have hQ := (circleMean_continuous q branch false X k).comp (sourceRadius_continuous image p r)
  have hC := (radialSeedFirst_continuous q branch amp true).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) by fun_prop)
  have hB := (radialSeedFirst_continuous q branch amp false).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) by fun_prop)
  have hχ : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.continuous
  have hE : Continuous (fun z : ℝ × ℝ =>
      ((deriv Real.smoothTransition z.1:ℝ):ℂ)*Complex.exp (2*physicalRate q branch*(z.1:ℂ))) := by
    fun_prop
  have he : Function.uncurry (circleSource (fullSourceOnsetPulse q branch amp) image p r X k)=
      fun z : ℝ × ℝ =>
        (-2*radialSeedFirst q branch amp true ((z.1-z.2)/2)*
          circleMean q branch true (radius (invariant ((p+r-z.1-z.2)/2) ((p-r)/2)
            (if image then -(z.1-z.2)/2 else (z.1-z.2)/2))) X k+
          2*parameter q branch*radialSeedFirst q branch amp false ((z.1-z.2)/2)*
          circleMean q branch false (radius (invariant ((p+r-z.1-z.2)/2) ((p-r)/2)
            (if image then -(z.1-z.2)/2 else (z.1-z.2)/2))) X k)*
          (((deriv Real.smoothTransition z.1:ℝ):ℂ)*Complex.exp (2*physicalRate q branch*(z.1:ℂ)))/4 := by
    funext z
    change onsetAngularMean q branch amp _ _ _ X k/4=_
    rw [onsetAngularMean_eq]
    dsimp only [onsetResponseCoefficient,onsetSourceCoefficient,radialSeedFirst,circleMean]
    simp only [Bool.false_eq_true,↓reduceIte]
    rw [show (z.1+z.2)/2+(z.1-z.2)/2=z.1 by ring]
    ring
  rw [he]
  exact (((hC.const_mul (-2)).mul hH).add ((hB.const_mul (2*parameter q branch)).mul hQ)).mul hE |>.div_const 4

private theorem parameter_ne_zero (q : XiZeroCopy) (branch : Bool) : parameter q branch ≠ 0 := by
  intro he
  have hi : (parameter q branch).im ≠ 0 := by
    cases branch
    · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).2
    · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).1
  rw [he] at hi
  exact hi rfl
private theorem wave_theta_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Bool)
    (a b d X k : ℝ) : Continuous (fun theta =>
      timeFieldWave (onsetField q branch amp i) ((a+b)/2) ((a-b)/2) (logCircle d theta X k)) := by
  have he := fun theta => onsetField_wave q branch amp i a b (logCircle d theta X k)
    (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))
  simp_rw [he]
  exact ((angularField_theta_continuous q branch i d X k).const_mul _).sub
    (((angularAction_theta_continuous q branch i d X k).const_mul _).div_const _)
private theorem pulse_theta_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (a b d X k : ℝ) : Continuous (fun theta =>
      fullSourceOnsetPulse q branch amp ((a+b)/2) ((a-b)/2) (logCircle d theta X k)) := by
  have he := fun theta => fullSourceOnsetPulse_transition q branch amp ((a+b)/2) ((a-b)/2)
    (logCircle d theta X k)
  simp_rw [he]
  exact (((angularField_theta_continuous q branch true d X k).const_mul _).add
    ((angularField_theta_continuous q branch false d X k).const_mul _)).mul_const _ |>.mul_const _

private theorem circleSource_decomposition (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p r X k a b : ℝ) :
    circleSource (timeOriginalForcing q branch amp) image p r X k a b=
      circleSource (timeFieldWave (timeLiftField q branch amp)) image p r X k a b-
      circleSource (timeFieldWave (timeAngularSeedField q branch amp)) image p r X k a b/parameter q branch+
      circleSource (fullSourceOnsetPulse q branch amp) image p r X k a b/parameter q branch := by
  let d := radius (invariant ((p+r-a-b)/2) ((p-r)/2) (if image then -(a-b)/2 else (a-b)/2))
  have he (theta : ℝ) : timeOriginalForcing q branch amp ((a+b)/2) ((a-b)/2) (logCircle d theta X k)=
      timeFieldWave (timeLiftField q branch amp) ((a+b)/2) ((a-b)/2) (logCircle d theta X k)-
      (parameter q branch)⁻¹*timeFieldWave (timeAngularSeedField q branch amp) ((a+b)/2) ((a-b)/2)
        (logCircle d theta X k)+
      (parameter q branch)⁻¹*fullSourceOnsetPulse q branch amp ((a+b)/2) ((a-b)/2) (logCircle d theta X k) := by
    have h := fullSourceOnset_wave_identity q branch amp ((a+b)/2) ((a-b)/2) (logCircle d theta X k)
      (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))
    field_simp [parameter_ne_zero q branch]
    linear_combination h
  change D4BMNativeCircle.average (fun theta => timeOriginalForcing q branch amp ((a+b)/2) ((a-b)/2)
    (logCircle d theta X k))/4=_
  have hQ := wave_theta_continuous q branch amp false a b d X k
  have hH := wave_theta_continuous q branch amp true a b d X k
  simp only [onsetField,Bool.false_eq_true,↓reduceIte] at hQ hH
  simp_rw [he]
  rw [average_add
    (f := fun theta => timeFieldWave (timeLiftField q branch amp) ((a+b)/2) ((a-b)/2) (logCircle d theta X k)-
      (parameter q branch)⁻¹*timeFieldWave (timeAngularSeedField q branch amp) ((a+b)/2) ((a-b)/2) (logCircle d theta X k))
    (g := fun theta => (parameter q branch)⁻¹*fullSourceOnsetPulse q branch amp ((a+b)/2) ((a-b)/2) (logCircle d theta X k))
    (hQ.sub (hH.const_mul ((parameter q branch)⁻¹)))
    ((pulse_theta_continuous q branch amp a b d X k).const_mul ((parameter q branch)⁻¹)),
    average_sub
      (f := fun theta => timeFieldWave (timeLiftField q branch amp) ((a+b)/2) ((a-b)/2) (logCircle d theta X k))
      (g := fun theta => (parameter q branch)⁻¹*timeFieldWave (timeAngularSeedField q branch amp) ((a+b)/2) ((a-b)/2) (logCircle d theta X k))
      hQ (hH.const_mul ((parameter q branch)⁻¹)),average_const_mul,average_const_mul]
  dsimp only [circleSource,d]
  ring

private theorem triangle_add (f g : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    triangle (fun a b => f a b+g a b) p r=triangle f p r+triangle g p r := by
  unfold triangle
  simp_rw [intervalIntegral.integral_add ((slice_second f hf _).intervalIntegrable _ _)
    ((slice_second g hg _).intervalIntegrable _ _)]
  exact intervalIntegral.integral_add ((inner_continuous f hf r).intervalIntegrable _ _)
    ((inner_continuous g hg r).intervalIntegrable _ _)
private theorem triangle_div (f : ℝ → ℝ → ℂ) (c : ℂ) (p r : ℝ) :
    triangle (fun a b => f a b/c) p r=triangle f p r/c := by
  unfold triangle
  simp_rw [intervalIntegral.integral_div]
private theorem triangle_source_decomposition (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p r X k l u : ℝ) :
    triangle (circleSource (timeOriginalForcing q branch amp) image p r X k) l u=
      triangle (circleSource (timeFieldWave (timeLiftField q branch amp)) image p r X k) l u-
      triangle (circleSource (timeFieldWave (timeAngularSeedField q branch amp)) image p r X k) l u/parameter q branch+
      triangle (circleSource (fullSourceOnsetPulse q branch amp) image p r X k) l u/parameter q branch := by
  have he : circleSource (timeOriginalForcing q branch amp) image p r X k=
      fun a b => circleSource (timeFieldWave (timeLiftField q branch amp)) image p r X k a b-
      circleSource (timeFieldWave (timeAngularSeedField q branch amp)) image p r X k a b/parameter q branch+
      circleSource (fullSourceOnsetPulse q branch amp) image p r X k a b/parameter q branch :=
    funext (fun a => funext (fun b => circleSource_decomposition q branch amp image p r X k a b))
  have hQ := circleSource_wave_continuous q branch amp false image p r X k
  have hH := circleSource_wave_continuous q branch amp true image p r X k
  have hP := circleSource_pulse_continuous q branch amp image p r X k
  simp only [onsetField,Bool.false_eq_true,↓reduceIte] at hQ hH
  rw [he,triangle_add
    (fun a b => circleSource (timeFieldWave (timeLiftField q branch amp)) image p r X k a b-
      circleSource (timeFieldWave (timeAngularSeedField q branch amp)) image p r X k a b/parameter q branch)
    (fun a b => circleSource (fullSourceOnsetPulse q branch amp) image p r X k a b/parameter q branch)
    (hQ.sub (hH.div_const _)) (hP.div_const _),
    triangle_sub
      (circleSource (timeFieldWave (timeLiftField q branch amp)) image p r X k)
      (fun a b => circleSource (timeFieldWave (timeAngularSeedField q branch amp)) image p r X k a b/parameter q branch)
      hQ (hH.div_const _),triangle_div,triangle_div]

/-- The literal original forcing response equals its actual wave image plus the unchanged
onset-pulse response. Both physical branches, original angular channels, causal images,
normalization and onset clock are retained; no inverse or extinction premise is assumed. -/
theorem originalForcing_retarded_reconstruction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    retardedNullAction (timeOriginalForcing q branch amp) p width X k=
      timeLiftField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]-
      timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]/parameter q branch+
      retardedNullAction (fullSourceOnsetPulse q branch amp) p width X k/parameter q branch := by
  rw [← retardedNullAction_lift_wave,← retardedNullAction_seed_wave]
  simp only [action_eq_triangles]
  rw [triangle_source_decomposition,triangle_source_decomposition]
  ring

end
end RHTower.D4BMOnsetGreenReconstruction
