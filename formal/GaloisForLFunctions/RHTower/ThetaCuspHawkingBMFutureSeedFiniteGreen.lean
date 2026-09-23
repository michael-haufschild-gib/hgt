import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat
import Mathlib.MeasureTheory.Integral.Prod

/-! Finite future Green reconstruction of the original angular seed.

The direct and image future triangles retain the outgoing-null terminal face.
Reciprocal full angular Goursat primitives identify the actual circle kernels,
and the two diagonal fluxes cancel. The resulting identity integrates the
original onset pulse minus the reduced theta-square source. Its terminal
integral remains explicit; no infinite-face limit or metric/QNM identification
is asserted by these finite identities.
-/

namespace RHTower.D4BMFutureSeedGreen
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularCircleAction D4BMFullAngularGoursat
open D4BMNativeCircle D4BMAngularSeries D4BMJointSource MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false

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

private theorem slice_second (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (a : ℝ) : Continuous (f a) :=
  hf.comp (continuous_const.prodMk continuous_id)

private theorem slice_first (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (b : ℝ) :
    Continuous (fun a => f a b) := hf.comp (continuous_id.prodMk continuous_const)

private def futureIntegral (f : ℝ → ℝ → ℂ) (p r L : ℝ) : ℂ :=
  (∫ v in p..r, ∫ w in r..L, f v w) + ∫ v in r..L, ∫ w in v..L, f v w

private theorem future_sub (f g : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g))
    (p r L : ℝ) :
    futureIntegral (fun v w => f v w-g v w) p r L =
      futureIntegral f p r L-futureIntegral g p r L := by
  unfold futureIntegral
  simp_rw [intervalIntegral.integral_sub ((slice_second f hf _).intervalIntegrable _ _)
    ((slice_second g hg _).intervalIntegrable _ _)]
  have hfi : Continuous (fun v => ∫ w in v..L, f v w) :=
    integral_continuous f hf (fun v => v) (fun _ => L) continuous_id continuous_const
  have hgi : Continuous (fun v => ∫ w in v..L, g v w) :=
    integral_continuous g hg (fun v => v) (fun _ => L) continuous_id continuous_const
  rw [intervalIntegral.integral_sub
    ((integral_continuous f hf _ _ continuous_const continuous_const).intervalIntegrable _ _)
    ((integral_continuous g hg _ _ continuous_const continuous_const).intervalIntegrable _ _),
    intervalIntegral.integral_sub
    (hfi.intervalIntegrable _ _) (hgi.intervalIntegrable _ _)]
  ring

private theorem future_second (A D : ℝ → ℝ → ℂ)
    (hA : Continuous (Function.uncurry A)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ v w, HasDerivAt (A v) (D v w) w)
    {p r L : ℝ} (hrL : r ≤ L) :
    futureIntegral D p r L = (∫ v in p..L, A v L) -
      (∫ v in p..r, A v r) - ∫ v in r..L, A v v := by
  have hFTC (v a b : ℝ) (hab : a ≤ b) :
      (∫ w in a..b, D v w)=A v b-A v a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (slice_second A hA v).continuousOn (fun w _ => hd v w)
      ((slice_second D hD v).intervalIntegrable _ _)
  have htri : (∫ v in r..L, ∫ w in v..L, D v w)=∫ v in r..L, A v L-A v v := by
    apply intervalIntegral.integral_congr
    intro v hv
    exact hFTC v v L (show v ≤ L from
      (show v ∈ Icc r L by simpa [uIcc_of_le hrL] using hv).2)
  unfold futureIntegral
  simp_rw [hFTC _ r L hrL]
  have hdiag : Continuous (fun v => A v v) := hA.comp (continuous_id.prodMk continuous_id)
  rw [htri,intervalIntegral.integral_sub
    ((slice_first A hA L).intervalIntegrable _ _)
    ((slice_first A hA r).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((slice_first A hA L).intervalIntegrable _ _)
    (hdiag.intervalIntegrable _ _)]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((slice_first A hA L).intervalIntegrable p r)
    ((slice_first A hA L).intervalIntegrable r L)
  linear_combination hadd

private theorem future_first_vanish (A D : ℝ → ℝ → ℂ)
    (hA : Continuous (Function.uncurry A)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ v w, HasDerivAt (fun t => A t w) (D v w) v)
    {p r L : ℝ} (hpr : p ≤ r) (hrL : r ≤ L)
    (hdiag : ∀ v, A v v=0) (hedge : ∀ w, A p w=0) :
    futureIntegral D p r L=0 := by
  have hFTC (w a b : ℝ) (hab : a ≤ b) :
      (∫ v in a..b, D v w)=A b w-A a w :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (slice_first A hA w).continuousOn (fun v _ => hd v w)
      ((slice_first D hD w).intervalIntegrable _ _)
  unfold futureIntegral
  rw [rectangle_swap D hD p r r L,triangle_swap D hD hrL]
  have htri : (∫ w in r..L, ∫ v in r..w, D v w)=∫ w in r..L, -A r w := by
    apply intervalIntegral.integral_congr
    intro w hw
    dsimp only
    rw [hFTC w r w (show r ≤ w from
      (show w ∈ Icc r L by simpa [uIcc_of_le hrL] using hw).1),hdiag,zero_sub]
  simp_rw [hFTC _ p r hpr,hedge,sub_zero]
  rw [htri,intervalIntegral.integral_neg,add_neg_cancel]

private theorem future_green (K Kw Kvw b bv bvw : ℝ → ℝ → ℂ)
    (hK : Continuous (Function.uncurry K)) (hKw : Continuous (Function.uncurry Kw))
    (hKvw : Continuous (Function.uncurry Kvw)) (hb : Continuous (Function.uncurry b))
    (hbv : Continuous (Function.uncurry bv)) (hbvw : Continuous (Function.uncurry bvw))
    (hK_w : ∀ v w, HasDerivAt (K v) (Kw v w) w)
    (hKw_v : ∀ v w, HasDerivAt (fun t => Kw t w) (Kvw v w) v)
    (hb_v : ∀ v w, HasDerivAt (fun t => b t w) (bv v w) v)
    (hbv_w : ∀ v w, HasDerivAt (bv v) (bvw v w) w)
    {p r L : ℝ} (hpr : p ≤ r) (hrL : r ≤ L)
    (hdiag : ∀ v, b v v=0) (hedge : ∀ w, Kw p w=0) :
    futureIntegral (fun v w => K v w*bvw v w-b v w*Kvw v w) p r L =
      (∫ v in p..L, K v L*bv v L) - (∫ v in p..r, K v r*bv v r) -
        ∫ v in r..L, K v v*bv v v := by
  have hw := future_second (fun v w => K v w*bv v w)
    (fun v w => Kw v w*bv v w+K v w*bvw v w)
    (hK.mul hbv) ((hKw.mul hbv).add (hK.mul hbvw))
    (fun v w => (hK_w v w).mul (hbv_w v w)) (p := p) hrL
  have hv := future_first_vanish (fun v w => b v w*Kw v w)
    (fun v w => bv v w*Kw v w+b v w*Kvw v w)
    (hb.mul hKw) ((hbv.mul hKw).add (hb.mul hKvw))
    (fun v w => (hb_v v w).mul (hKw_v v w)) hpr hrL
    (fun v => by rw [hdiag,zero_mul]) (fun w => by rw [hedge,mul_zero])
  have he : (fun v w => K v w*bvw v w-b v w*Kvw v w)=
      fun v w => (Kw v w*bv v w+K v w*bvw v w)-
        (bv v w*Kw v w+b v w*Kvw v w) := by funext v w; ring
  rw [he,future_sub (fun v w => Kw v w*bv v w+K v w*bvw v w)
    (fun v w => bv v w*Kw v w+b v w*Kvw v w) ((hKw.mul hbv).add (hK.mul hbvw))
    ((hbv.mul hKw).add (hb.mul hKvw)),hw,hv,sub_zero]

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


private theorem primitive_swap (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (u v : ℝ) :
    primitive c (fun a b => g b a) u v=primitive c g v u := by
  unfold primitive firstPrimitive
  apply congrArg (fun z : ℂ => c+z)
  exact rectangle_swap (fun a b => g b a) (hg.comp continuous_swap) 0 u 0 v

private def forwardKernel (c : ℂ) (g : ℝ → ℝ → ℂ) (p r v w : ℝ) : ℂ :=
  primitive c g (w-r) (v-p)
private def forwardFirst (g : ℝ → ℝ → ℂ) (p r v w : ℝ) : ℂ :=
  firstPrimitive g (w-r) (v-p)
private def forwardMixed (g : ℝ → ℝ → ℂ) (p r v w : ℝ) : ℂ := g (w-r) (v-p)

private theorem forwardKernel_continuous (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    Continuous (Function.uncurry (forwardKernel c g p r)) :=
  (primitive_continuous c g hg).comp
    (show Continuous (fun z : ℝ × ℝ => (z.2-r,z.1-p)) by fun_prop)
private theorem forwardFirst_continuous (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    Continuous (Function.uncurry (forwardFirst g p r)) :=
  (firstPrimitive_continuous g hg).comp
    (show Continuous (fun z : ℝ × ℝ => (z.2-r,z.1-p)) by fun_prop)
private theorem forwardMixed_continuous (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r : ℝ) :
    Continuous (Function.uncurry (forwardMixed g p r)) :=
  hg.comp (show Continuous (fun z : ℝ × ℝ => (z.2-r,z.1-p)) by fun_prop)

private theorem forwardKernel_second (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r v w : ℝ) :
    HasDerivAt (forwardKernel c g p r v) (forwardFirst g p r v w) w := by
  apply ((primitive_first c g hg (w-r) (v-p)).scomp w
    ((hasDerivAt_id w).sub_const r)).congr_deriv
  simp only [forwardFirst,Complex.real_smul,Complex.ofReal_one,one_mul]
private theorem forwardFirst_first (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r v w : ℝ) :
    HasDerivAt (fun t => forwardFirst g p r t w) (forwardMixed g p r v w) v := by
  apply ((firstPrimitive_second g hg (w-r) (v-p)).scomp v
    ((hasDerivAt_id v).sub_const p)).congr_deriv
  simp only [forwardMixed,Complex.real_smul,Complex.ofReal_one,one_mul]

private theorem forwardKernel_bottom (c : ℂ) (g : ℝ → ℝ → ℂ) (p r v : ℝ) :
    forwardKernel c g p r v r=c := by
  simp only [forwardKernel,primitive,sub_self,intervalIntegral.integral_same,add_zero]
private theorem forwardFirst_edge (g : ℝ → ℝ → ℂ) (p r w : ℝ) :
    forwardFirst g p r p w=0 := by
  simp only [forwardFirst,firstPrimitive,sub_self,intervalIntegral.integral_same]
private theorem forwardKernel_diagonal (c : ℂ) (g : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (p r v : ℝ) :
    forwardKernel c g p r v v=forwardKernel c (fun a b => g b a) r p v v := by
  exact (primitive_swap c g hg (v-p) (v-r)).symm

private theorem paired_future_green (c : ℂ) (g b bv bvw : ℝ → ℝ → ℂ)
    (hg : Continuous (Function.uncurry g)) (hb : Continuous (Function.uncurry b))
    (hbv : Continuous (Function.uncurry bv)) (hbvw : Continuous (Function.uncurry bvw))
    (hb_v : ∀ v w, HasDerivAt (fun t => b t w) (bv v w) v)
    (hbv_w : ∀ v w, HasDerivAt (bv v) (bvw v w) w)
    (hdiag : ∀ v, b v v=0) {p r L : ℝ} (hpr : p ≤ r) (hrL : r ≤ L) :
    futureIntegral (fun v w => forwardKernel c g p r v w*bvw v w-
        b v w*forwardMixed g p r v w) p r L-
      futureIntegral (fun v w => forwardKernel c (fun a b => g b a) r p v w*bvw v w-
        b v w*forwardMixed (fun a b => g b a) r p v w) r r L =
      c*b p r+(∫ v in p..L, forwardKernel c g p r v L*bv v L)-
        ∫ v in r..L, forwardKernel c (fun a b => g b a) r p v L*bv v L := by
  have hgs : Continuous (Function.uncurry (fun a b => g b a)) := hg.comp continuous_swap
  have hd := future_green (forwardKernel c g p r) (forwardFirst g p r) (forwardMixed g p r)
    b bv bvw (forwardKernel_continuous c g hg p r) (forwardFirst_continuous g hg p r)
    (forwardMixed_continuous g hg p r) hb hbv hbvw (forwardKernel_second c g hg p r)
    (forwardFirst_first g hg p r) hb_v hbv_w hpr hrL hdiag (forwardFirst_edge g p r)
  have hi := future_green (forwardKernel c (fun a b => g b a) r p)
    (forwardFirst (fun a b => g b a) r p) (forwardMixed (fun a b => g b a) r p)
    b bv bvw (forwardKernel_continuous c _ hgs r p) (forwardFirst_continuous _ hgs r p)
    (forwardMixed_continuous _ hgs r p) hb hbv hbvw (forwardKernel_second c _ hgs r p)
    (forwardFirst_first _ hgs r p) hb_v hbv_w (le_refl r) hrL hdiag
    (forwardFirst_edge _ r p)
  rw [hd,hi]
  simp only [forwardKernel_bottom,intervalIntegral.integral_same,sub_zero,
    forwardKernel_diagonal c g hg p r]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpr
    (slice_first b hb r).continuousOn (fun v _ => hb_v v r)
    ((slice_first bv hbv r).intervalIntegrable _ _),hdiag,zero_sub]
  ring

private def angularAction (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) : ℂ :=
  parameter q branch*(angularMean q branch d X k+D4BMNativeCircle.mean q d X k)
private def radius (z : ℝ) : ℝ := Real.arcosh (max 1 z)
private def forcing (q : XiZeroCopy) (branch : Bool) (x X k u v : ℝ) : ℂ :=
  angularAction q branch (radius (invariant ((u+v)/2) (x+(v-u)/2) x)) X k /
    (4*(Real.cosh (x+(v-u)/2):ℂ)^(2 : ℕ))

private theorem forcing_continuous (q : XiZeroCopy) (branch : Bool) (x X k : ℝ) :
    Continuous (Function.uncurry (forcing q branch x X k)) := by
  have ha : Continuous (fun d => angularAction q branch d X k) :=
    continuous_const.mul ((angularMean_smooth q branch X k).continuous.add
      (D4BMNativeCircle.mean_radial_smooth q X k).continuous)
  have hr : Continuous radius :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
      (fun z => le_max_left 1 z)
  have hz : Continuous (fun z : ℝ × ℝ => invariant ((z.1+z.2)/2) (x+(z.2-z.1)/2) x) := by
    unfold invariant
    exact (show Continuous (fun z : ℝ × ℝ => Real.cosh ((z.1+z.2)/2)+
      Real.sinh (x+(z.2-z.1)/2)*Real.sinh x) by fun_prop).div
      (by fun_prop) (fun z => mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne')
  exact (ha.comp (hr.comp hz)).div (by fun_prop)
    (fun z => mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')))

private theorem null_cone (x : ℝ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |x+(v-u)/2-x| ≤ (u+v)/2 := by
  apply abs_le.mpr
  constructor <;> linarith

private theorem forcing_raw (q : XiZeroCopy) (branch : Bool) (x X k : ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    forcing q branch x X k u v =
      angularAction q branch (Real.arcosh (invariant ((u+v)/2) (x+(v-u)/2) x)) X k /
        (4*(Real.cosh (x+(v-u)/2):ℂ)^(2 : ℕ)) := by
  have hz := invariant_causal (⟨_,_,_,null_cone x hu hv⟩ : CausalPoint)
  dsimp only [forcing,radius]
  rw [max_eq_right hz]

private theorem invariant_reciprocal (h x y : ℝ) : invariant h x y=invariant h y x := by
  unfold invariant
  rw [mul_comm (Real.sinh x),mul_comm (Real.cosh x)]

private theorem primitive_kernel (q : XiZeroCopy) (branch : Bool) (x X k : ℝ)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    primitive (fullAngularField q branch ![X,Real.exp k]) (forcing q branch x X k) u v =
      fullAngularRiemannKernel q branch ((u+v)/2) x (x+(v-u)/2) X k := by
  have hc := null_cone x hu hv
  have h := fullAngularRiemannKernel_goursat q branch
    (⟨(u+v)/2,x+(v-u)/2,x,hc⟩ : CausalPoint) X k
  dsimp only at h
  have he : fullAngularRiemannKernel q branch ((u+v)/2) x (x+(v-u)/2) X k =
      fullAngularRiemannKernel q branch ((u+v)/2) (x+(v-u)/2) x X k := by
    unfold fullAngularRiemannKernel
    rw [invariant_reciprocal]
  rw [he,h]
  rw [show (u+v)/2+(x+(v-u)/2)-x=v by ring,
    show (u+v)/2-(x+(v-u)/2)+x=u by ring]
  unfold primitive firstPrimitive
  rw [rectangle_swap _ (forcing_continuous q branch x X k) 0 u 0 v]
  apply congrArg (fun z : ℂ => fullAngularField q branch ![X,Real.exp k]+z)
  apply intervalIntegral.integral_congr
  intro a ha
  have ha₀ := (show a ∈ Icc 0 v by simpa [uIcc_of_le hv] using ha).1
  apply intervalIntegral.integral_congr
  intro b hb
  have hb₀ := (show b ∈ Icc 0 u by simpa [uIcc_of_le hu] using hb).1
  dsimp only
  rw [forcing_raw q branch x X k hb₀ ha₀]
  rw [add_comm b a]
  rfl

/-- The original radial seed coefficient in ingoing and outgoing source time. -/
def seedNull (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v w : ℝ) : ℂ :=
  sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)*
    timeOnset (2*physicalRate q branch) v

/-- Actual derivative along the ingoing source coordinate, with the fixed onset retained. -/
def seedNullFirst (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v w : ℝ) : ℂ :=
  sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)/2*
    timeOnset (2*physicalRate q branch) v+
  sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)*
    timeOnsetFirst (2*physicalRate q branch) v

private def seedNullMixed (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v w : ℝ) : ℂ :=
  -sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)/4*
    timeOnset (2*physicalRate q branch) v-
  sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)/2*
    timeOnsetFirst (2*physicalRate q branch) v

theorem seedNull_first (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v w : ℝ) :
    HasDerivAt (fun t => seedNull q branch amp t w) (seedNullFirst q branch amp v w) v := by
  have hd := (sourceSeedField_hasDerivAt (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)).scomp v
    (((hasDerivAt_id v).sub_const w).div_const 2)
  apply (hd.mul (timeOnset_hasDerivAt (2*physicalRate q branch) v)).congr_deriv
  dsimp only [seedNullFirst,Function.comp_apply,id_eq]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem seedNullFirst_second (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v w : ℝ) :
    HasDerivAt (seedNullFirst q branch amp v) (seedNullMixed q branch amp v w) w := by
  have h1 := (sourceSeedFieldFirst_hasDerivAt (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)).scomp w
    (((hasDerivAt_id w).const_sub v).div_const 2)
  have h0 := (sourceSeedField_hasDerivAt (physicalRate q branch) 0 amp 1 (parameter q branch) ((v-w)/2)).scomp w
    (((hasDerivAt_id w).const_sub v).div_const 2)
  apply (((h1.div_const 2).mul_const (timeOnset (2*physicalRate q branch) v)).add
    (h0.mul_const (timeOnsetFirst (2*physicalRate q branch) v))).congr_deriv
  dsimp only [seedNullMixed]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

private theorem seedNull_regular (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    Continuous (Function.uncurry (seedNull q branch amp)) ∧
    Continuous (Function.uncurry (seedNullFirst q branch amp)) ∧
    Continuous (Function.uncurry (seedNullMixed q branch amp)) := by
  have h0 : Continuous (sourceSeedField (physicalRate q branch) 0 amp 1 (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun t => (sourceSeedField_hasDerivAt _ _ _ _ _ t).continuousAt)
  have h1 : Continuous (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun t => (sourceSeedFieldFirst_hasDerivAt _ _ _ _ _ t).continuousAt)
  have hA : Continuous (sourceAmplitude (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t => (sourceAmplitude_hasDerivAt _ _ _ _ t).continuousAt)
  have hU : Continuous radialUnit :=
    continuous_iff_continuousAt.mpr (fun t => (radialUnit_hasDerivAt t).continuousAt)
  have h2 : Continuous (sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch)) := by
    change Continuous (fun t => sourceSeedFieldSecond (physicalRate q branch) 0 amp 1 (parameter q branch) t)
    dsimp only [sourceSeedFieldSecond,sourceSeedPolynomial,sourceSeedFirst,sourceSeedSecond,amplitudeRate]
    fun_prop
  have ho : Continuous (timeOnset (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun t => (timeOnset_hasDerivAt _ t).continuousAt)
  have ho1 : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun t => (timeOnsetFirst_hasDerivAt _ t).continuousAt)
  have hc : Continuous (fun z : ℝ × ℝ => (z.1-z.2)/2) := by fun_prop
  exact ⟨(h0.comp hc).mul (ho.comp continuous_fst),
    (((h1.comp hc).div_const 2).mul (ho.comp continuous_fst)).add
      ((h0.comp hc).mul (ho1.comp continuous_fst)),
    ((((h2.comp hc).neg).div_const 4).mul (ho.comp continuous_fst)).sub
      (((h1.comp hc).div_const 2).mul (ho1.comp continuous_fst))⟩

private theorem seedNull_diagonal (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v : ℝ) :
    seedNull q branch amp v v=0 := by
  simp [seedNull,sourceSeedField,sourceSeedPolynomial,radialUnit]

/-- Unscaled full angular mean on an original future direct or image cone. -/
def sourceKernel (q : XiZeroCopy) (branch image : Bool) (p r X k v w : ℝ) : ℂ :=
  fullAngularRiemannKernel q branch ((v+w-p-r)/2) ((p-r)/2)
    (if image then -((v-w)/2) else (v-w)/2) X k

theorem sourceKernel_circleMean (q : XiZeroCopy) (branch image : Bool) (p r X k v w : ℝ) :
    sourceKernel q branch image p r X k v w=
      angularMean q branch (Real.arcosh (invariant ((v+w-p-r)/2) ((p-r)/2)
        (if image then -((v-w)/2) else (v-w)/2))) X k := rfl

private def sourceAction (q : XiZeroCopy) (branch image : Bool) (p r X k v w : ℝ) : ℂ :=
  angularAction q branch (Real.arcosh (invariant ((v+w-p-r)/2) ((p-r)/2)
    (if image then -((v-w)/2) else (v-w)/2))) X k /
    (4*(Real.cosh ((v-w)/2):ℂ)^(2 : ℕ))

private theorem direct_kernel (q : XiZeroCopy) (branch : Bool) (p r X k v w : ℝ)
    (hv : p ≤ v) (hw : r ≤ w) :
    forwardKernel (fullAngularField q branch ![X,Real.exp k])
      (forcing q branch ((p-r)/2) X k) p r v w=sourceKernel q branch false p r X k v w := by
  rw [forwardKernel,primitive_kernel q branch _ X k (sub_nonneg.mpr hw) (sub_nonneg.mpr hv)]
  rw [show (w-r+(v-p))/2=(v+w-p-r)/2 by ring,
    show (p-r)/2+(v-p-(w-r))/2=(v-w)/2 by ring]
  rfl

private theorem image_kernel (q : XiZeroCopy) (branch : Bool) (p r X k v w : ℝ)
    (hv : r ≤ v) (hpr : p ≤ r) (hw : r ≤ w) :
    forwardKernel (fullAngularField q branch ![X,Real.exp k])
      (fun a b => forcing q branch ((p-r)/2) X k b a) r p v w=
      sourceKernel q branch true p r X k v w := by
  rw [forwardKernel,primitive_swap _ _ (forcing_continuous q branch _ X k),
    primitive_kernel q branch _ X k (sub_nonneg.mpr hv) (sub_nonneg.mpr (hpr.trans hw))]
  rw [show (v-r+(w-p))/2=(v+w-p-r)/2 by ring,
    show (p-r)/2+(w-p-(v-r))/2=-((v-w)/2) by ring]
  rfl

private theorem direct_action (q : XiZeroCopy) (branch : Bool) (p r X k v w : ℝ)
    (hv : p ≤ v) (hw : r ≤ w) :
    forwardMixed (forcing q branch ((p-r)/2) X k) p r v w=
      sourceAction q branch false p r X k v w := by
  rw [forwardMixed,forcing_raw q branch _ X k (sub_nonneg.mpr hw) (sub_nonneg.mpr hv)]
  rw [show (w-r+(v-p))/2=(v+w-p-r)/2 by ring,
    show (p-r)/2+(v-p-(w-r))/2=(v-w)/2 by ring,
    invariant_reciprocal]
  rfl

private theorem image_action (q : XiZeroCopy) (branch : Bool) (p r X k v w : ℝ)
    (hv : r ≤ v) (hpr : p ≤ r) (hw : r ≤ w) :
    forwardMixed (fun a b => forcing q branch ((p-r)/2) X k b a) r p v w=
      sourceAction q branch true p r X k v w := by
  dsimp only [forwardMixed]
  rw [forcing_raw q branch _ X k (sub_nonneg.mpr hv) (sub_nonneg.mpr (hpr.trans hw))]
  rw [show (v-r+(w-p))/2=(v+w-p-r)/2 by ring,
    show (p-r)/2+(w-p-(v-r))/2=-((v-w)/2) by ring,
    invariant_reciprocal,Real.cosh_neg]
  rfl

private theorem circle_continuous (f : Point → ℂ)
    (hf : ∀ z, 0 < z 1 → ContinuousAt f z) (d X k : ℝ) :
    Continuous (fun theta => f (logCircle d theta X k)) := by
  have hc : Continuous (fun theta : ℝ => logCircle d theta X k) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := intro theta; exact (denominator_pos d theta).ne')
  exact continuous_iff_continuousAt.mpr (fun theta =>
    (hf _ (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))).comp hc.continuousAt)

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

private theorem radial_metric (t : ℝ) : 1-(radialUnit t:ℂ)^(2 : ℕ)=1/(Real.cosh t:ℂ)^(2 : ℕ) := by
  have hn : (Real.cosh t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have he : (Real.cosh t:ℂ)^(2 : ℕ)-(Real.sinh t:ℂ)^(2 : ℕ)=1 := by exact_mod_cast Real.cosh_sq_sub_sinh_sq t
  dsimp only [radialUnit]
  simp only [Complex.ofReal_div,Complex.ofReal_neg]
  field_simp [hn]
  linear_combination he

private theorem seed_wave (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v w : ℝ) (z : Point) (hz : 0 < z 1) :
    timeFieldWave (timeAngularSeedField q branch amp) ((v+w)/2) ((v-w)/2) z=
      4*seedNullMixed q branch amp v w*fullAngularField q branch z-
        seedNull q branch amp v w*scalarLaplacian (fullAngularField q branch) z /
          (Real.cosh ((v-w)/2):ℂ)^(2 : ℕ) := by
  have hL : scalarLaplacian (fun y =>
      timeSourceSeed (physicalRate q branch) amp (parameter q branch) ((v+w)/2) ((v-w)/2)*
        fullAngularField q branch y) z=
      timeSourceSeed (physicalRate q branch) amp (parameter q branch) ((v+w)/2) ((v-w)/2)*
        scalarLaplacian (fullAngularField q branch) z := by
    rw [scalarLaplacian_eq _ z hz,scalarLaplacian_eq _ z hz]
    apply hyperbolicLaplacian_const_mul
    exact (contDiffAt_infty.mp (fullAngularField_smooth q branch z hz)) 2
  unfold timeFieldWave timeAngularSeedField
  simp only [deriv_mul_const_field',deriv_mul_const_field]
  rw [hL,← sub_mul,timeSourceSeed_wave,radial_metric]
  dsimp only [seedNullMixed,seedNull,timeSourceSeed]
  rw [show (v+w)/2+(v-w)/2=v by ring]
  ring

private theorem seed_wave_mean (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v w d X k : ℝ) :
    D4BMNativeCircle.average (fun theta =>
      timeFieldWave (timeAngularSeedField q branch amp) ((v+w)/2) ((v-w)/2)
        (logCircle d theta X k))/4 =
      angularMean q branch d X k*seedNullMixed q branch amp v w-
        seedNull q branch amp v w*angularAction q branch d X k /
          (4*(Real.cosh ((v-w)/2):ℂ)^(2 : ℕ)) := by
  have hb := circle_continuous (fullAngularField q branch)
    (fun z hz => (fullAngularField_smooth q branch z hz).continuousAt) d X k
  have hq := circle_continuous (fullSquarePotential q)
    (fun z hz => (fullSquarePotential_smooth q z hz 0).continuousAt) d X k
  have he (theta : ℝ) :
      timeFieldWave (timeAngularSeedField q branch amp) ((v+w)/2) ((v-w)/2) (logCircle d theta X k)=
      (4*seedNullMixed q branch amp v w-seedNull q branch amp v w*parameter q branch/
        (Real.cosh ((v-w)/2):ℂ)^(2 : ℕ))*fullAngularField q branch (logCircle d theta X k)-
      (seedNull q branch amp v w*parameter q branch/(Real.cosh ((v-w)/2):ℂ)^(2 : ℕ))*
        fullSquarePotential q (logCircle d theta X k) := by
    have hz : 0 < logCircle d theta X k 1 :=
      mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
    rw [seed_wave q branch amp _ _ _ hz,fullAngularField_equation q branch _ hz]
    dsimp only [fullSquarePotential]
    ring
  simp_rw [he]
  rw [average_sub (hb.const_mul _) (hq.const_mul _),average_const_mul,average_const_mul]
  change ((4*seedNullMixed q branch amp v w-_/(_ : ℂ)^(2 : ℕ))*angularMean q branch d X k-
    (_/(_ : ℂ)^(2 : ℕ))*D4BMNativeCircle.mean q d X k)/4=_
  dsimp only [angularAction]
  ring

/-- Future source-circle integral in the exact direct and image null regions;
the factor one quarter is the kernel factor times the coordinate Jacobian. -/
def finiteFutureAction (S : ℝ → ℝ → Point → ℂ) (p r L X k : ℝ) : ℂ :=
  let F (image : Bool) (v w : ℝ) := D4BMNativeCircle.average (fun theta =>
    S ((v+w)/2) ((v-w)/2) (logCircle (Real.arcosh (invariant ((v+w-p-r)/2) ((p-r)/2)
      (if image then -((v-w)/2) else (v-w)/2))) theta X k))/4
  futureIntegral (F false) p r L-futureIntegral (F true) r r L

/-- The retained outgoing-null terminal face, with the actual seed derivative. -/
def seedTerminal (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r L X k : ℝ) : ℂ :=
  (∫ v in p..L, sourceKernel q branch false p r X k v L*seedNullFirst q branch amp v L)-
    ∫ v in r..L, sourceKernel q branch true p r X k v L*seedNullFirst q branch amp v L

private theorem future_congr {f g : ℝ → ℝ → ℂ} {p r L : ℝ}
    (hpr : p ≤ r) (hrL : r ≤ L)
    (he : ∀ v w, p ≤ v → r ≤ w → v ≤ w → w ≤ L → f v w=g v w) :
    futureIntegral f p r L=futureIntegral g p r L := by
  unfold futureIntegral
  congr 1
  · apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc p r := by simpa [uIcc_of_le hpr] using hv
    apply intervalIntegral.integral_congr
    intro w hw
    have hw' : w ∈ Icc r L := by simpa [uIcc_of_le hrL] using hw
    exact he v w hv'.1 hw'.1 (hv'.2.trans hw'.1) hw'.2
  · apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc r L := by simpa [uIcc_of_le hrL] using hv
    apply intervalIntegral.integral_congr
    intro w hw
    have hw' : w ∈ Icc v L := by simpa [uIcc_of_le hv'.2] using hw
    exact he v w (hpr.trans hv'.1) (hv'.1.trans hw'.1) hw'.1 hw'.2

private theorem finite_future_seed_wave_raw (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r L X k : ℝ) (hpr : p ≤ r) (hrL : r ≤ L) :
    finiteFutureAction (timeFieldWave (timeAngularSeedField q branch amp)) p r L X k =
      fullAngularField q branch ![X,Real.exp k]*seedNull q branch amp p r+
        seedTerminal q branch amp p r L X k := by
  let c := fullAngularField q branch ![X,Real.exp k]
  let g := forcing q branch ((p-r)/2) X k
  obtain ⟨h0,h1,h2⟩ := seedNull_regular q branch amp
  have hg : Continuous (Function.uncurry g) := forcing_continuous q branch _ X k
  have h := paired_future_green c g (seedNull q branch amp) (seedNullFirst q branch amp)
    (seedNullMixed q branch amp) hg h0 h1 h2 (seedNull_first q branch amp)
    (seedNullFirst_second q branch amp) (seedNull_diagonal q branch amp) hpr hrL
  let F (image : Bool) (v w : ℝ) := D4BMNativeCircle.average (fun theta =>
    timeFieldWave (timeAngularSeedField q branch amp) ((v+w)/2) ((v-w)/2)
      (logCircle (Real.arcosh (invariant ((v+w-p-r)/2) ((p-r)/2)
        (if image then -((v-w)/2) else (v-w)/2))) theta X k))/4
  have hd : futureIntegral (fun v w => forwardKernel c g p r v w*seedNullMixed q branch amp v w-
      seedNull q branch amp v w*forwardMixed g p r v w) p r L=futureIntegral (F false) p r L :=
    future_congr hpr hrL (fun v w hv hw _ _ => by
    rw [direct_kernel q branch p r X k v w hv hw,direct_action q branch p r X k v w hv hw]
    rw [sourceKernel_circleMean]
    dsimp only [F,sourceAction]
    rw [seed_wave_mean]
    ring)
  have hi : futureIntegral (fun v w => forwardKernel c (fun a b => g b a) r p v w*seedNullMixed q branch amp v w-
      seedNull q branch amp v w*forwardMixed (fun a b => g b a) r p v w) r r L=futureIntegral (F true) r r L :=
    future_congr (le_refl r) hrL (fun v w hv hw _ _ => by
    rw [image_kernel q branch p r X k v w hv hpr hw,image_action q branch p r X k v w hv hpr hw]
    rw [sourceKernel_circleMean]
    dsimp only [F,sourceAction]
    rw [seed_wave_mean]
    ring)
  change futureIntegral (F false) p r L-futureIntegral (F true) r r L=_
  rw [← hd,← hi,h]
  have htd : (∫ v in p..L, forwardKernel c g p r v L*seedNullFirst q branch amp v L)=
      ∫ v in p..L, sourceKernel q branch false p r X k v L*seedNullFirst q branch amp v L := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [direct_kernel q branch p r X k v L
      (show p ≤ v from (show v ∈ Icc p L by simpa [uIcc_of_le (hpr.trans hrL)] using hv).1) hrL]
  have hti : (∫ v in r..L, forwardKernel c (fun a b => g b a) r p v L*seedNullFirst q branch amp v L)=
      ∫ v in r..L, sourceKernel q branch true p r X k v L*seedNullFirst q branch amp v L := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [image_kernel q branch p r X k v L
      (show r ≤ v from (show v ∈ Icc r L by simpa [uIcc_of_le hrL] using hv).1) hpr hrL]
  rw [htd,hti]
  dsimp only [seedTerminal,c]
  ring

/-- Finite future reconstruction of the original seed wave, including its outgoing-null
terminal face. All field, derivative and characteristic identities are proved from the
original source; no wave, matching or vanishing-boundary premise is supplied. -/
theorem finite_future_seed_wave (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : ℝ) (width span : NNReal) (X k : ℝ) :
    finiteFutureAction (timeFieldWave (timeAngularSeedField q branch amp))
      p (p+width) (p+width+span) X k =
      timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]+
        seedTerminal q branch amp p (p+width) (p+width+span) X k := by
  rw [finite_future_seed_wave_raw q branch amp p (p+width) (p+width+span) X k
    (by linarith [width.coe_nonneg]) (by linarith [span.coe_nonneg])]
  dsimp only [seedNull,timeAngularSeedField,timeSourceSeed]
  rw [show (p-(p+width))/2=-(width:ℝ)/2 by ring,
    show (2*p+width)/2+ -(width:ℝ)/2=p by ring]
  ring

private theorem finiteFutureAction_congr {S T : ℝ → ℝ → Point → ℂ}
    (he : ∀ t y z, 0 < z 1 → S t y z=T t y z) (p r L X k : ℝ) :
    finiteFutureAction S p r L X k=finiteFutureAction T p r L X k := by
  have hf (image : Bool) (v w : ℝ) :
      D4BMNativeCircle.average (fun theta => S ((v+w)/2) ((v-w)/2)
        (logCircle (Real.arcosh (invariant ((v+w-p-r)/2) ((p-r)/2)
          (if image then -((v-w)/2) else (v-w)/2))) theta X k))=
      D4BMNativeCircle.average (fun theta => T ((v+w)/2) ((v-w)/2)
        (logCircle (Real.arcosh (invariant ((v+w-p-r)/2) ((p-r)/2)
          (if image then -((v-w)/2) else (v-w)/2))) theta X k)) := by
    apply congrArg D4BMNativeCircle.average
    funext theta
    exact he _ _ _ (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))
  have hfalse := hf false
  have htrue := hf true
  simp only [Bool.false_eq_true,↓reduceIte] at hfalse htrue
  simp only [finiteFutureAction,Bool.false_eq_true,↓reduceIte]
  simp_rw [hfalse,htrue]

/-- The same finite reconstruction integrates the original onset pulse minus the
original reduced source, with its literal theta square and parameter. -/
theorem finite_future_source_balance (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : ℝ) (width span : NNReal) (X k : ℝ) :
    finiteFutureAction (fun t y z => fullSourceOnsetPulse q branch amp t y z-
        parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*fullSquarePotential q z)
      p (p+width) (p+width+span) X k =
      timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]+
        seedTerminal q branch amp p (p+width) (p+width+span) X k := by
  have he (t y : ℝ) (z : Point) (hz : 0 < z 1) :
      fullSourceOnsetPulse q branch amp t y z-
        parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*fullSquarePotential q z=
      timeFieldWave (timeAngularSeedField q branch amp) t y z := by
    have h1 := fullSourceOnset_wave_identity q branch amp t y z hz
    have h2 := timeOriginalForcing_gradient_absorption q branch amp t y z hz
    linear_combination -h1+parameter q branch*h2
  rw [finiteFutureAction_congr he]
  exact finite_future_seed_wave q branch amp p width span X k

end
end RHTower.D4BMFutureSeedGreen
