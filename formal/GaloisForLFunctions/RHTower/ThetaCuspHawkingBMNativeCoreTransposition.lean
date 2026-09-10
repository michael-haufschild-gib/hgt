import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeJointEnergy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoreOperator

/-! Transposition of the literal native elliptic equation against the original smooth core. -/
open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ComplexConjugate ContDiff
namespace RHTower.D4BMNativeResponse
open D4BMJointWave D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem core_inner_integral (f g : CoreField) :
    Integrable (fun z => conj (f.field z)*g.field z) D4BMModularCore.measure ∧
    inner ℂ (fieldVector f) (fieldVector g) =
      ∫ z, conj (f.field z)*g.field z ∂D4BMModularCore.measure := by
  have he : (fun z => inner ℂ (fieldVector f z) (fieldVector g z)) =ᵐ[D4BMModularCore.measure]
      (fun z => conj (f.field z)*g.field z) := by
    filter_upwards [(core_field_memLp f.field f.smooth f.compact).coeFn_toLp,
      (core_field_memLp g.field g.smooth g.compact).coeFn_toLp] with z hf hg
    change fieldVector f z = _ at hf
    change fieldVector g z = _ at hg
    rw [hf,hg]
    simp only [RCLike.inner_apply,mul_comm]
  exact ⟨(L2.integrable_inner (𝕜 := ℂ) (fieldVector f) (fieldVector g)).congr he,
    (L2.inner_def _ _).trans (integral_congr_ae he)⟩

private theorem core_second_green (f g : CoreField) :
    inner ℂ (fieldVector f.laplacian) (fieldVector g) =
      inner ℂ (fieldVector f) (fieldVector g.laplacian) := by
  have hf := f.completed_green ⟨frameGraph g,frameGraph_mem g⟩
  have hg := g.completed_green ⟨frameGraph f,frameGraph_mem f⟩
  change inner ℂ (derivativeVector f 1) (derivativeVector g 1)+
    inner ℂ (derivativeVector f Complex.I) (derivativeVector g Complex.I) =
      -inner ℂ (fieldVector f.laplacian) (fieldVector g) at hf
  change inner ℂ (derivativeVector g 1) (derivativeVector f 1)+
    inner ℂ (derivativeVector g Complex.I) (derivativeVector f Complex.I) =
      -inner ℂ (fieldVector g.laplacian) (fieldVector f) at hg
  have hc := congrArg conj hg
  simp only [map_add,map_neg,inner_conj_symm] at hc
  exact neg_injective (hf.symm.trans hc)

private theorem primitive_cutoff_germ (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (n : ℕ) (z : UpperHalfPlane) (hz : z ∈ fd) (hy : z.im < 2*((n:ℝ)+1)) :
    (nativeTimePrimitiveCutoff q s amplitude t x n 0).field =ᶠ[𝓝 z]
      globalNativeTimePrimitive q s amplitude t x := by
  have hn : (0:ℝ) ≤ n := by positivity
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by linarith
  filter_upwards [modularCuspCutoff_germ _ hN z hz,
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hy] with w hw hwy
  change modularCuspCutoff _ w^(0+1)*_ = _
  rw [hw,scaledCuspCutoff_low _ _ (by positivity) hwy.le]
  simp

/-- The literal untruncated native primitive satisfies the second angular Green identity
against every original compact modular test, including tests crossing the joined cell sides. -/
theorem nativeTimePrimitive_angular_transposition (q : XiZeroCopy) (s amplitude : ℂ)
    (t x : ℝ) (g : CoreField) :
    Integrable (fun z => conj (chartLaplacian g.field z)*
      globalNativeTimePrimitive q s amplitude t x z) D4BMModularCore.measure ∧
    Integrable (fun z => conj (g.field z)*
      chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z) D4BMModularCore.measure ∧
    (∫ z, conj (chartLaplacian g.field z)*globalNativeTimePrimitive q s amplitude t x z
      ∂D4BMModularCore.measure) =
    ∫ z, conj (g.field z)*chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z
      ∂D4BMModularCore.measure := by
  obtain ⟨K,hK,hg⟩ := g.compact
  obtain ⟨L,hL,hl⟩ := g.laplacian.compact
  obtain ⟨C,hC⟩ := (hK.union hL).exists_bound_of_continuousOn
    UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨n,hn⟩ := exists_nat_gt C
  let F := nativeTimePrimitiveCutoff q s amplitude t x n 0
  have hgerm (z : UpperHalfPlane) (hz : z ∈ fd) (hk : z ∈ K ∪ L) :
      F.field =ᶠ[𝓝 z] globalNativeTimePrimitive q s amplitude t x := by
    apply primitive_cutoff_germ q s amplitude t x n z hz
    have hh := hC z hk
    rw [Real.norm_eq_abs,abs_of_pos z.im_pos] at hh
    have hn0 : (0:ℝ) ≤ n := by positivity
    linarith
  have he₁ : (fun z => conj (g.laplacian.field z)*F.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => conj (chartLaplacian g.field z)*globalNativeTimePrimitive q s amplitude t x z) := by
    filter_upwards [ae_mem_interior] with z hz
    have hfd : z ∈ fd := fdo_subset_fd hz
    by_cases hzL : z ∈ L
    · rw [(hgerm z hfd (Or.inr hzL)).eq_of_nhds]
      rfl
    · rw [hl z hfd hzL]
      change conj (0:ℂ)*_ = conj (g.laplacian.field z)*_
      rw [hl z hfd hzL]
      simp only [map_zero,zero_mul]
  have he₂ : (fun z => conj (g.field z)*F.laplacian.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => conj (g.field z)*chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z) := by
    filter_upwards [ae_mem_interior] with z hz
    have hfd : z ∈ fd := fdo_subset_fd hz
    by_cases hzK : z ∈ K
    · change conj (g.field z)*chartLaplacian F.field z = _
      rw [chartLaplacian_congr (hgerm z hfd (Or.inl hzK))]
    · simp only [hg z hfd hzK,map_zero,zero_mul]
  have h₁ := core_inner_integral g.laplacian F
  have h₂ := core_inner_integral g F.laplacian
  refine ⟨h₁.1.congr he₁,h₂.1.congr he₂,?_⟩
  rw [← integral_congr_ae he₁,← integral_congr_ae he₂,← h₁.2,← h₂.2]
  exact core_second_green g F

private theorem radial_pair_integrable (f : RadialCore) (W : ℝ → ℂ) (hW : Continuous W) :
    Integrable (fun x => conj (f.field x)*W x) := by
  apply ((Complex.conjCLE.continuous.comp f.smooth.continuous).mul hW).integrable_of_hasCompactSupport
  exact HasCompactSupport.intro f.compact (fun x hx => by
    change conj (f.field x)*W x = 0
    simp only [image_eq_zero_of_notMem_tsupport hx,map_zero,zero_mul])

private theorem radial_pair_full (f : RadialCore) (W : ℝ → ℂ) :
    (∫ x, conj (f.field x)*W x ∂radialMeasure) = ∫ x, conj (f.field x)*W x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (f.support h)),map_zero,zero_mul]

private theorem radial_second_green (f : RadialCore) (W : ℝ → ℂ)
    (hW : ∀ x, HasDerivAt W (deriv W x) x)
    (hW' : ∀ x, HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hW'' : Continuous (deriv (deriv W))) :
    (∫ x, conj (deriv (deriv f.field) x)*W x ∂radialMeasure) =
      ∫ x, conj (f.field x)*deriv (deriv W) x ∂radialMeasure := by
  have h0 : Continuous W := continuous_iff_continuousAt.mpr (fun x => (hW x).continuousAt)
  have h1 : Continuous (deriv W) := continuous_iff_continuousAt.mpr (fun x => (hW' x).continuousAt)
  have hd (g : RadialCore) (x : ℝ) :
      HasDerivAt (fun y => conj (g.field y)) (conj (deriv g.field x)) x :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      ((g.smooth.differentiable (by simp) x).hasDerivAt)
  have hi₁ := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => conj (deriv f.field x)) (u' := fun x => conj (deriv (deriv f.field) x))
    (v := W) (v' := deriv W) (fun x _ => hd f.differentiate x) (fun x _ => hW x)
    (radial_pair_integrable f.differentiate _ h1)
    (radial_pair_integrable f.differentiate.differentiate _ h0)
    (radial_pair_integrable f.differentiate _ h0)
  have hi₂ := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => conj (f.field x)) (u' := fun x => conj (deriv f.field x))
    (v := deriv W) (v' := deriv (deriv W)) (fun x _ => hd f x) (fun x _ => hW' x)
    (radial_pair_integrable f _ hW'') (radial_pair_integrable f.differentiate _ h1)
    (radial_pair_integrable f _ h1)
  change (∫ x, conj (f.differentiate.differentiate.field x)*W x ∂radialMeasure) = _
  rw [radial_pair_full,radial_pair_full]
  change (∫ x, conj (deriv (deriv f.field) x)*W x) = _
  linear_combination hi₁-hi₂

/-- The actual native radial second derivative transposes onto every original radial core test. -/
theorem nativeTimePrimitive_radial_transposition (q : XiZeroCopy) (s amplitude : ℂ)
    (t X k : ℝ) (f : RadialCore) :
    (∫ x, conj (deriv (deriv f.field) x)*nativeResidualTimePrimitive q s amplitude t x X k
      ∂radialMeasure) =
    ∫ x, conj (f.field x)*
      deriv (deriv (fun y => nativeResidualTimePrimitive q s amplitude t y X k)) x
        ∂radialMeasure := by
  apply radial_second_green
  · exact fun x => (nativeResidualTimePrimitive_radial_hasDerivAt q s amplitude t x X k).1
  · exact fun x => (nativeResidualTimePrimitive_radial_hasDerivAt q s amplitude t x X k).2
  · have hc : Continuous (fun x : ℝ => ((t,x),(X,k))) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    exact (nativeResidualTimePrimitive_joint_spatial_jets q s amplitude).2.2.1.comp hc

private abbrev nativeRadialSecond (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  deriv (deriv (fun x => nativeResidualTimePrimitive q s amplitude t x p.2.re (Real.log p.2.im))) p.1

private abbrev nativeAngularSecond (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  (p.2.im:ℂ)^2*deriv (deriv (fun X => nativeResidualTimePrimitive q s amplitude t p.1 X (Real.log p.2.im))) p.2.re +
    deriv (deriv (fun k => nativeResidualTimePrimitive q s amplitude t p.1 p.2.re k)) (Real.log p.2.im) -
    deriv (fun k => nativeResidualTimePrimitive q s amplitude t p.1 p.2.re k) (Real.log p.2.im)

private theorem native_second_continuous (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    Continuous (nativeJointTimePrimitiveField q s amplitude t) ∧
    Continuous (nativeRadialSecond q s amplitude t) ∧
    Continuous (nativeAngularSecond q s amplitude t) := by
  obtain ⟨h0,_,hxx,_,hXX,hk,hkk⟩ := nativeResidualTimePrimitive_joint_spatial_jets q s amplitude
  have hlog : Continuous (fun z : UpperHalfPlane => Real.log z.im) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Real.continuousAt_log z.im_pos.ne').comp UpperHalfPlane.continuous_im.continuousAt
  have hc : Continuous (fun p : ℝ × UpperHalfPlane => ((t,p.1),(p.2.re,Real.log p.2.im))) :=
    (continuous_const.prodMk continuous_fst).prodMk
      ((UpperHalfPlane.continuous_re.comp continuous_snd).prodMk (hlog.comp continuous_snd))
  have hy : Continuous (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)) := by fun_prop
  exact ⟨h0.comp hc,hxx.comp hc,
    ((hy.pow 2).mul (hXX.comp hc)).add (hkk.comp hc) |>.sub (hk.comp hc)⟩

private theorem core_product_pair_integrable (f : RadialCore) (g : CoreField)
    (H : ℝ × UpperHalfPlane → ℂ) (hH : Continuous H) :
    Integrable (fun p => conj (f.field p.1)*conj (g.field p.2)*H p)
      (radialMeasure.prod D4BMModularCore.measure) := by
  obtain ⟨K,hK,hg⟩ := g.compact
  let S := tsupport f.field ×ˢ K
  have hS : IsCompact S := f.compact.prod hK
  have hc : Continuous (fun p : ℝ × UpperHalfPlane => conj (f.field p.1)*conj (g.field p.2)*H p) :=
    ((Complex.conjCLE.continuous.comp (f.smooth.continuous.comp continuous_fst)).mul
      (Complex.conjCLE.continuous.comp (g.smooth.continuous.comp continuous_snd))).mul hH
  have hi := (integrable_indicator_iff hS.measurableSet).mpr
    (hc.continuousOn.integrableOn_compact (μ := radialMeasure.prod D4BMModularCore.measure) hS)
  apply hi.congr
  have hz : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, p.2 ∈ fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [hz] with p hp
  by_cases hs : p ∈ S
  · simp only [indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    by_cases hf : p.1 ∈ tsupport f.field
    · have hn : p.2 ∉ K := fun hk => hs ⟨hf,hk⟩
      simp only [hg p.2 hp hn,map_zero,mul_zero,zero_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hf,map_zero,zero_mul]

private theorem separated_pair_integral (f : RadialCore) (g : CoreField)
    (H : ℝ × UpperHalfPlane → ℂ) (hH : MemLp H 2 (radialMeasure.prod D4BMModularCore.measure)) :
    inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) (hH.toLp H) =
      ∫ p, conj (f.field p.1)*conj (g.field p.2)*H p ∂(radialMeasure.prod D4BMModularCore.measure) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hf : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
      radialValue f p.1 = f.field p.1 := Measure.quasiMeasurePreserving_fst.ae (radialValue_ae f)
  have hg : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
      fieldVector g p.2 = g.field p.2 := Measure.quasiMeasurePreserving_snd.ae
    (core_field_memLp g.field g.smooth g.compact).coeFn_toLp
  filter_upwards [l2SeparatedProduct_ae (radialValue f) (fieldVector g),hH.coeFn_toLp,hf,hg]
    with p hp hH hf hg
  change fieldVector g p.2 = g.field p.2 at hg
  rw [hp,hH]
  simp only [l2SeparatedFun,hf,hg,RCLike.inner_apply,map_mul]
  ring

private abbrev corePair (f : RadialCore) (g : CoreField) (H : ℝ × UpperHalfPlane → ℂ) : ℂ :=
  ∫ p, conj (f.field p.1)*conj (g.field p.2)*H p ∂(radialMeasure.prod D4BMModularCore.measure)

private theorem radial_product_transposition (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (f : RadialCore) (g : CoreField) :
    corePair f.differentiate.differentiate g (nativeJointTimePrimitiveField q s amplitude t) =
      corePair f g (nativeRadialSecond q s amplitude t) := by
  obtain ⟨hW,hR,_⟩ := native_second_continuous q s amplitude t
  unfold corePair
  rw [integral_prod_symm _ (core_product_pair_integrable _ _ _ hW),
    integral_prod_symm _ (core_product_pair_integrable _ _ _ hR)]
  apply integral_congr_ae
  filter_upwards with z
  simp_rw [mul_right_comm _ (conj (g.field z)),integral_mul_const]
  congr 1
  exact nativeTimePrimitive_radial_transposition q s amplitude t z.re (Real.log z.im) f

private theorem angular_literal_transposition (q : XiZeroCopy) (s amplitude : ℂ) (t x : ℝ)
    (g : CoreField) :
    (∫ z, conj (g.laplacian.field z)*nativeJointTimePrimitiveField q s amplitude t (x,z)
      ∂D4BMModularCore.measure) =
    ∫ z, conj (g.field z)*nativeAngularSecond q s amplitude t (x,z) ∂D4BMModularCore.measure := by
  have hW : (fun z => conj (g.laplacian.field z)*globalNativeTimePrimitive q s amplitude t x z) =ᵐ[
      D4BMModularCore.measure] (fun z => conj (g.laplacian.field z)*nativeJointTimePrimitiveField q s amplitude t (x,z)) := by
    filter_upwards [ae_mem_interior] with z hz
    rw [(globalNativeTimePrimitive_germ q s amplitude t x z (fdo_subset_fd hz)).eq_of_nhds]
    rfl
  have hL : (fun z => conj (g.field z)*chartLaplacian (globalNativeTimePrimitive q s amplitude t x) z) =ᵐ[
      D4BMModularCore.measure] (fun z => conj (g.field z)*nativeAngularSecond q s amplitude t (x,z)) := by
    filter_upwards [ae_mem_interior] with z hz
    rw [nativeTimePrimitive_chart_laplacian q s amplitude t x z (fdo_subset_fd hz)]
  rw [← integral_congr_ae hW,← integral_congr_ae hL]
  exact (nativeTimePrimitive_angular_transposition q s amplitude t x g).2.2

private theorem angular_product_transposition (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (f : RadialCore) (g : CoreField) :
    corePair f g.laplacian (nativeJointTimePrimitiveField q s amplitude t) =
      corePair f g (nativeAngularSecond q s amplitude t) := by
  obtain ⟨hW,_,hL⟩ := native_second_continuous q s amplitude t
  unfold corePair
  rw [integral_prod _ (core_product_pair_integrable _ _ _ hW),
    integral_prod _ (core_product_pair_integrable _ _ _ hL)]
  apply integral_congr_ae
  filter_upwards with x
  simp_rw [mul_assoc,integral_const_mul]
  rw [angular_literal_transposition]

private theorem elliptic_product_pair (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (f : RadialCore) (g : CoreField) :
    -corePair f g (nativeRadialSecond q s amplitude t)-
      corePair f.angularWeighted.angularWeighted g (nativeAngularSecond q s amplitude t) =
      corePair f g (nativeJointEllipticForcing q s amplitude t) := by
  obtain ⟨_,hR,hL⟩ := native_second_continuous q s amplitude t
  have hiR := core_product_pair_integrable f g _ hR
  have hiL := core_product_pair_integrable f.angularWeighted.angularWeighted g _ hL
  have hiN : Integrable (fun p => -(conj (f.field p.1)*conj (g.field p.2)*nativeRadialSecond q s amplitude t p))
      (radialMeasure.prod D4BMModularCore.measure) := hiR.neg
  unfold corePair
  rw [← integral_neg,← integral_sub hiN hiL]
  apply integral_congr_ae
  have hz : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, p.2 ∈ fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [hz] with p hp
  have he := nativeTimePrimitive_original_elliptic_equation q s amplitude t p.1 p.2 hp
  rw [nativeTimePrimitive_chart_laplacian q s amplitude t p.1 p.2 hp] at he
  rw [← he]
  change -(conj (f.field p.1)*conj (g.field p.2)*nativeRadialSecond q s amplitude t p)-
    conj (angularWeight p.1*(angularWeight p.1*f.field p.1))*conj (g.field p.2)*
      nativeAngularSecond q s amplitude t p =
    conj (f.field p.1)*conj (g.field p.2)*
      (-nativeRadialSecond q s amplitude t p-nativeAngularSecond q s amplitude t p/(Real.cosh p.1:ℂ)^2)
  simp only [map_mul]
  rw [show conj (angularWeight p.1) = angularWeight p.1 from Complex.conj_ofReal _]
  simp only [angularWeight,Complex.ofReal_inv,div_eq_mul_inv]
  ring

/-- The native primitive satisfies the actual mass-minus-Laplacian transposition against
every separated generator of the original completed joint form domain. -/
theorem nativeTimePrimitive_core_transposition (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ)
    (f : RadialCore) (g : CoreField) :
    inner ℂ (jointCoreDifferential f g)
      ((nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t)) =
    inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g))
      ((nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t)+
       (nativeJointEllipticForcing_memLp q s amplitude t).toLp
        (nativeJointEllipticForcing q s amplitude t)) := by
  rw [jointCoreDifferential,inner_sub_left,inner_sub_left,inner_add_right]
  have hr : radialDerivative f.differentiate = radialValue f.differentiate.differentiate := rfl
  rw [hr,← RadialCore.angularWeighted_value f.angularWeighted]
  simp only [separated_pair_integral]
  change corePair f g (nativeJointTimePrimitiveField q s amplitude t)-
    corePair f.differentiate.differentiate g (nativeJointTimePrimitiveField q s amplitude t)-
    corePair f.angularWeighted.angularWeighted g.laplacian (nativeJointTimePrimitiveField q s amplitude t) =
    corePair f g (nativeJointTimePrimitiveField q s amplitude t)+
    corePair f g (nativeJointEllipticForcing q s amplitude t)
  rw [radial_product_transposition,angular_product_transposition]
  linear_combination elliptic_product_pair q s amplitude t f g

end
end RHTower.D4BMNativeResponse
