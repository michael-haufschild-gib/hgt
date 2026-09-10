import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeForcedIntegral
import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Exact forced equations for the original native causal response.

The original onset support makes the intersection of source and retarded cones a null rectangle.
Its Jacobian and the Riemann kernel's Goursat identity give the forced integral equation. Two
applications of FTC give the mixed derivative equation; changing back gives the full spatial
free-wave Duhamel equation. No identification with the massive L² evolution is assumed here.
-/

open MeasureTheory Set Filter Topology Module
namespace RHTower.D4BMNativeResponse
open D4BMCausalKernel D4BMJointSource
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

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

private theorem corner_swap (f : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (hf : Continuous f)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q,
      ∫ c in a..p, ∫ d in b..q, f ((a,b),(c,d))) =
      ∫ c in (0:ℝ)..p, ∫ d in (0:ℝ)..q,
        ∫ a in (0:ℝ)..c, ∫ b in (0:ℝ)..d, f ((a,b),(c,d)) := by
  calc
    _ = ∫ a in (0:ℝ)..p, ∫ c in a..p,
        ∫ b in (0:ℝ)..q, ∫ d in b..q, f ((a,b),(c,d)) := by
      apply intervalIntegral.integral_congr
      intro a ha
      exact rectangle_swap (fun b c => ∫ d in b..q, f ((a,b),(c,d))) (by fun_prop) 0 q a p
    _ = ∫ c in (0:ℝ)..p, ∫ a in (0:ℝ)..c,
        ∫ b in (0:ℝ)..q, ∫ d in b..q, f ((a,b),(c,d)) :=
      triangle_swap (fun a c => ∫ b in (0:ℝ)..q, ∫ d in b..q, f ((a,b),(c,d)))
        (by fun_prop) hp
    _ = ∫ c in (0:ℝ)..p, ∫ a in (0:ℝ)..c,
        ∫ d in (0:ℝ)..q, ∫ b in (0:ℝ)..d, f ((a,b),(c,d)) := by
      apply intervalIntegral.integral_congr
      intro c hc
      apply intervalIntegral.integral_congr
      intro a ha
      exact triangle_swap (fun b d => f ((a,b),(c,d))) (by fun_prop) hq
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro c hc
      exact rectangle_swap (fun a d => ∫ b in (0:ℝ)..d, f ((a,b),(c,d)))
        (by fun_prop) 0 c 0 q

private def nullKernel (nu : ℂ) (p q a b : ℝ) : ℂ :=
  legendreKernel nu (max 1 (invariant ((p+q-a-b)/2) ((p-q)/2) ((a-b)/2)))

private theorem nullKernel_continuous (nu : ℂ) :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => nullKernel nu z.1.1 z.1.2 z.2.1 z.2.2) := by
  have hi : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      max 1 (invariant ((z.1.1+z.1.2-z.2.1-z.2.2)/2)
        ((z.1.1-z.1.2)/2) ((z.2.1-z.2.2)/2))) := by
    unfold invariant
    apply Continuous.max continuous_const
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have hP : ContinuousOn (legendreKernel nu) (Ioi 0) :=
    fun z hz => ((legendreKernel_derivatives nu hz).1.continuousAt).continuousWithinAt
  apply hP.comp_continuous hi
  intro z
  change (0:ℝ) < max 1 _
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

private theorem null_cone {p q a b : ℝ} (ha : a ≤ p) (hb : b ≤ q) :
    |(p-q)/2-(a-b)/2| ≤ (p+q-a-b)/2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem nullKernel_eq (nu : ℂ) {p q a b : ℝ} (ha : a ≤ p) (hb : b ≤ q) :
    nullKernel nu p q a b = riemannKernel nu ((p+q-a-b)/2) ((p-q)/2) ((a-b)/2) := by
  unfold nullKernel riemannKernel
  rw [max_eq_right (invariant_causal ⟨_,_,_,null_cone ha hb⟩)]

private def nullPotential (nu : ℂ) (c d : ℝ) : ℂ :=
  nu*(nu+1)/(4*(Real.cosh ((c-d)/2):ℂ)^2)

private theorem nullPotential_continuous (nu : ℂ) :
    Continuous (fun p : ℝ × ℝ => nullPotential nu p.1 p.2) := by
  unfold nullPotential
  apply Continuous.div continuous_const
  · fun_prop
  · intro p
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast (Real.cosh_pos _).ne'))

private theorem nullKernel_goursat (nu : ℂ) {p q a b : ℝ} (ha : a ≤ p) (hb : b ≤ q) :
    nullKernel nu p q a b = 1+∫ c in a..p, ∫ d in b..q,
      nullPotential nu c d*nullKernel nu c d a b := by
  have hg := riemannKernel_goursat nu ⟨_,_,_,null_cone ha hb⟩
  dsimp only at hg
  rw [nullKernel_eq nu ha hb]
  rw [show (p+q-a-b)/2+(p-q)/2-(a-b)/2 = p-a by ring,
    show (p+q-a-b)/2-(p-q)/2+(a-b)/2 = q-b by ring] at hg
  rw [hg]
  congr 1
  let f (c d : ℝ) := nullPotential nu c d*nullKernel nu c d a b
  have hs (c : ℝ) : (∫ v in (0:ℝ)..(q-b), f c (v+b)) = ∫ d in b..q, f c d := by
    simpa only [zero_add,sub_add_cancel] using
      intervalIntegral.integral_comp_add_right (f := f c) (a := (0:ℝ)) (b := q-b) b
  have ht : (∫ u in (0:ℝ)..(p-a), ∫ v in (0:ℝ)..(q-b), f (u+a) (v+b)) =
      ∫ c in a..p, ∫ d in b..q, f c d := by
    simp_rw [hs]
    simpa only [zero_add,sub_add_cancel] using intervalIntegral.integral_comp_add_right
      (f := fun c => ∫ d in b..q, f c d) (a := (0:ℝ)) (b := p-a) a
  rw [← ht]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu0 : 0 ≤ u := (show u ∈ Icc 0 (p-a) by simpa [uIcc_of_le (sub_nonneg.mpr ha)] using hu).1
  apply intervalIntegral.integral_congr
  intro v hv
  have hv0 : 0 ≤ v := (show v ∈ Icc 0 (q-b) by simpa [uIcc_of_le (sub_nonneg.mpr hb)] using hv).1
  dsimp only [f,nullPotential,characteristicKernel]
  rw [nullKernel_eq nu (by linarith : a ≤ u+a) (by linarith : b ≤ v+b)]
  congr 2 <;> congr 1 <;> ring_nf

private def nullResponse (nu : ℂ) (f : ℝ × ℝ → ℂ) (p q : ℝ) : ℂ :=
  (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, nullKernel nu p q a b*f (a,b)

private theorem nullResponse_goursat (nu : ℂ) (f : ℝ × ℝ → ℂ) (hf : Continuous f)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    nullResponse nu f p q = (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, f (a,b))+
      ∫ c in (0:ℝ)..p, ∫ d in (0:ℝ)..q, nullPotential nu c d*nullResponse nu f c d := by
  let g (z : (ℝ × ℝ) × (ℝ × ℝ)) :=
    nullPotential nu z.2.1 z.2.2*nullKernel nu z.2.1 z.2.2 z.1.1 z.1.2*f z.1
  have hg : Continuous g :=
    ((nullPotential_continuous nu).comp continuous_snd).mul
      ((nullKernel_continuous nu).comp (continuous_snd.prodMk continuous_fst)) |>.mul
        (hf.comp continuous_fst)
  have he : (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, nullKernel nu p q a b*f (a,b)) =
      (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, f (a,b))+
      ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, ∫ c in a..p, ∫ d in b..q, g ((a,b),(c,d)) := by
    have hpoint {a b : ℝ} (ha : a ≤ p) (hb : b ≤ q) :
        nullKernel nu p q a b*f (a,b) =
          f (a,b)+(∫ c in a..p, ∫ d in b..q, g ((a,b),(c,d))) := by
      rw [nullKernel_goursat nu ha hb]
      dsimp only [g]
      simp_rw [intervalIntegral.integral_mul_const]
      ring
    have hL : (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, nullKernel nu p q a b*f (a,b)) =
        ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q,
          f (a,b)+(∫ c in a..p, ∫ d in b..q, g ((a,b),(c,d))) := by
      apply intervalIntegral.integral_congr
      intro a ha
      have ha' : a ≤ p := (show a ∈ Icc 0 p by simpa [uIcc_of_le hp] using ha).2
      apply intervalIntegral.integral_congr
      intro b hb
      have hb' : b ≤ q := (show b ∈ Icc 0 q by simpa [uIcc_of_le hq] using hb).2
      exact hpoint ha' hb'
    rw [hL]
    have hC : Continuous (fun z : ℝ × ℝ => ∫ c in z.1..p, ∫ d in z.2..q,
        g (z,(c,d))) := by fun_prop
    have hinner (a : ℝ) : (∫ b in (0:ℝ)..q,
        f (a,b)+(∫ c in a..p, ∫ d in b..q, g ((a,b),(c,d)))) =
        (∫ b in (0:ℝ)..q, f (a,b))+
        ∫ b in (0:ℝ)..q, ∫ c in a..p, ∫ d in b..q, g ((a,b),(c,d)) :=
      intervalIntegral.integral_add
        ((hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 q)
        ((hC.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 q)
    simp_rw [hinner]
    apply intervalIntegral.integral_add
    · exact (show Continuous (fun a => ∫ b in (0:ℝ)..q, f (a,b)) by fun_prop).intervalIntegrable 0 p
    · exact (show Continuous (fun a => ∫ b in (0:ℝ)..q, ∫ c in a..p,
        ∫ d in b..q, g ((a,b),(c,d))) by fun_prop).intervalIntegrable 0 p
  have hs := corner_swap g hg hp hq
  unfold nullResponse
  rw [he,hs,mul_add]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro c hc
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro d hd
  dsimp only [g]
  simp_rw [mul_assoc,intervalIntegral.integral_const_mul]
  ring


private def nullToStatic : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
    !![(1/2:ℝ),1/2;1/2,-1/2]).toContinuousLinearMap

private theorem nullToStatic_apply (z : ℝ × ℝ) :
    nullToStatic z = ((z.1+z.2)/2,(z.1-z.2)/2) := by
  change (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
    !![(1/2:ℝ),1/2;1/2,-1/2]) z = _
  rw [Matrix.toLin_finTwoProd_apply]
  ext <;> dsimp <;> ring

private theorem nullToStatic_det : nullToStatic.det = -(1/2:ℝ) := by
  change LinearMap.det (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
    !![(1/2:ℝ),1/2;1/2,-1/2]) = _
  rw [LinearMap.det_toLin,Matrix.det_fin_two]
  norm_num

private theorem nullToStatic_injective : Function.Injective nullToStatic := by
  intro z w h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [nullToStatic_apply] at h₁ h₂
  ext <;> linarith

private def sourceDiamond (p q : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1+z.2 ∈ Icc 0 p ∧ z.1-z.2 ∈ Icc 0 q}

private theorem nullToStatic_image (p q : ℝ) :
    nullToStatic '' (Icc 0 p ×ˢ Icc 0 q) = sourceDiamond p q := by
  ext z
  constructor
  · rintro ⟨w,⟨hp,hq⟩,rfl⟩
    simp only [sourceDiamond,mem_setOf_eq,nullToStatic_apply,mem_Icc]
    constructor <;> constructor <;> linarith [hp.1,hp.2,hq.1,hq.2]
  · intro hz
    refine ⟨(z.1+z.2,z.1-z.2),hz,?_⟩
    rw [nullToStatic_apply]
    ext <;> dsimp <;> ring

private theorem diamond_integral (g : ℝ × ℝ → ℂ) (hg : Continuous g)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∫ z in sourceDiamond p q, g z) = (1/2:ℂ)*
      ∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, g ((a+b)/2,(a-b)/2) := by
  rw [← nullToStatic_image]
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure (ℝ × ℝ)) (s := Icc (0:ℝ) p ×ˢ Icc (0:ℝ) q)
    (measurableSet_Icc.prod measurableSet_Icc)
    (fun z hz => nullToStatic.hasFDerivAt.hasFDerivWithinAt)
    nullToStatic_injective.injOn g
  rw [hchange]
  simp only [nullToStatic_det,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
    Complex.real_smul,nullToStatic_apply,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  rw [integral_const_mul]
  congr 1
  rw [Measure.volume_eq_prod,setIntegral_prod]
  · simp_rw [integral_Icc_eq_integral_Ioc]
    rw [intervalIntegral.integral_of_le hp]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro a ha
    exact (intervalIntegral.integral_of_le hq).symm
  · rw [← Measure.volume_eq_prod]
    simpa only [Function.comp_def,nullToStatic_apply] using
      (hg.comp nullToStatic.continuous).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)

private def retardedDiamond (T x : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc 0 T ∧ |x-z.2| ≤ T-z.1}

private theorem retardedDiamond_compact (T x : ℝ) : IsCompact (retardedDiamond T x) := by
  have hc : IsClosed (retardedDiamond T x) :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_const.sub continuous_snd).abs (continuous_const.sub continuous_fst))
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
    (s := Icc 0 T ×ˢ Icc (x-T) (x+T))
  intro z hz
  obtain ⟨hzt,hzy⟩ := hz
  obtain ⟨hl,hr⟩ := abs_le.mp hzy
  exact ⟨hzt,⟨by linarith [hzt.1],by linarith [hzt.1]⟩⟩

private theorem retardedDiamond_integral (g : ℝ × ℝ → ℂ) (hg : Continuous g)
    {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    (∫ z in retardedDiamond T x, g z) =
      ∫ σ in (0:ℝ)..T, ∫ y in x-(T-σ)..x+(T-σ), g (σ,y) := by
  have hC := retardedDiamond_compact T x
  have hi : Integrable ((retardedDiamond T x).indicator g) (volume : Measure (ℝ × ℝ)) :=
    (integrable_indicator_iff hC.measurableSet).mpr (hg.continuousOn.integrableOn_compact hC)
  rw [← integral_indicator hC.measurableSet,Measure.volume_eq_prod,
    integral_prod _ (by simpa only [← Measure.volume_eq_prod] using hi),
    intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro σ
  dsimp only
  by_cases hσ : σ ∈ Icc 0 T
  · rw [indicator_of_mem hσ]
    have he : (fun y => (retardedDiamond T x).indicator g (σ,y)) =
        (Icc (x-(T-σ)) (x+(T-σ))).indicator (fun y => g (σ,y)) := by
      funext y
      have hy : |x-y| ≤ T-σ ↔ y ∈ Icc (x-(T-σ)) (x+(T-σ)) := by
        rw [abs_le,mem_Icc]
        constructor <;> rintro ⟨hl,hr⟩ <;> constructor <;> linarith
      simp only [Set.indicator_apply,retardedDiamond,mem_setOf_eq,hσ,
        true_and,hy]
    rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith [hσ.2])]
  · rw [indicator_of_notMem hσ]
    have he : (fun y => (retardedDiamond T x).indicator g (σ,y)) = fun _ => (0:ℂ) := by
      funext y
      simp only [Set.indicator_apply,retardedDiamond,mem_setOf_eq,hσ,
        false_and,ite_false]
    rw [he,integral_zero]

private theorem sourceDiamond_iff (p q : ℝ) (z : ℝ × ℝ) :
    z ∈ sourceDiamond p q ↔ z ∈ retardedDiamond ((p+q)/2) ((p-q)/2) ∧ |z.2| ≤ z.1 := by
  simp only [sourceDiamond,retardedDiamond,mem_setOf_eq,mem_Icc,abs_le]
  constructor
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,⟨?_,?_⟩⟩ <;> linarith
  · rintro ⟨⟨⟨h1,h2⟩,⟨h3,h4⟩⟩,⟨h5,h6⟩⟩
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

private theorem sourceDiamond_integral (g : ℝ × ℝ → ℂ)
    (hz : ∀ τ y, 0 ≤ τ → τ < |y| → g (τ,y) = 0) (p q : ℝ) :
    (∫ z in retardedDiamond ((p+q)/2) ((p-q)/2), g z) =
      ∫ z in sourceDiamond p q, g z := by
  have hD : MeasurableSet (sourceDiamond p q) :=
    (measurableSet_Icc.preimage (continuous_fst.add continuous_snd).measurable).inter
      (measurableSet_Icc.preimage (continuous_fst.sub continuous_snd).measurable)
  rw [← integral_indicator (retardedDiamond_compact _ _).measurableSet,
    ← integral_indicator hD]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  by_cases hc : z ∈ retardedDiamond ((p+q)/2) ((p-q)/2)
  · by_cases hs : |z.2| ≤ z.1
    · have hd := (sourceDiamond_iff p q z).mpr ⟨hc,hs⟩
      rw [indicator_of_mem hc,indicator_of_mem hd]
    · have hg : g z = 0 := hz z.1 z.2 hc.1.1 (lt_of_not_ge hs)
      have hd : z ∉ sourceDiamond p q := fun h => hs ((sourceDiamond_iff p q z).mp h).2
      rw [indicator_of_mem hc,indicator_of_notMem hd]
      exact hg
  · have hd : z ∉ sourceDiamond p q := fun h => hc ((sourceDiamond_iff p q z).mp h).1
    rw [indicator_of_notMem hc,indicator_of_notMem hd]

private theorem retarded_null_change (g : ℝ × ℝ → ℂ) (hg : Continuous g)
    (hz : ∀ τ y, 0 ≤ τ → τ < |y| → g (τ,y) = 0)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (1/2:ℂ)*(∫ σ in (0:ℝ)..((p+q)/2),
      ∫ y in (p-q)/2-((p+q)/2-σ)..(p-q)/2+((p+q)/2-σ), g (σ,y)) =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, g ((a+b)/2,(a-b)/2) := by
  rw [← retardedDiamond_integral g hg (by linarith : 0 ≤ (p+q)/2),
    sourceDiamond_integral g hz,diamond_integral g hg hp hq]
  ring


private theorem actualSource_continuous (s amplitude : ℂ) :
    Continuous (fun z : ℝ × ℝ => oddSource s amplitude z.1 z.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  convert! h₁.sub h₂ using 1

private theorem actualSource_zero_outside (s amplitude : ℂ) {τ y : ℝ}
    (_hτ : 0 ≤ τ) (hy : τ < |y|) : oddSource s amplitude τ y = 0 := by
  by_cases hn : y ≤ 0
  · simp only [oddSource,min_eq_left hn,min_eq_right (neg_nonneg.mpr hn),source_boundary,sub_zero]
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonpos hn] at hy
    linarith
  · have hp : 0 ≤ y := le_of_not_ge hn
    simp only [oddSource,min_eq_right hp,min_eq_left (neg_nonpos.mpr hp),source_boundary,zero_sub]
    apply neg_eq_zero.mpr
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonneg hp] at hy
    linarith

private def nullSource (s amplitude : ℂ) (z : ℝ × ℝ) : ℂ :=
  oddSource s amplitude ((z.1+z.2)/2) ((z.1-z.2)/2)

private theorem nullSource_continuous (s amplitude : ℂ) : Continuous (nullSource s amplitude) := by
  have hc := (actualSource_continuous s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  convert! hc using 1

private theorem radialResponse_null (nu s amplitude : ℂ) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    radialResponse nu s amplitude ((p+q)/2) ((p-q)/2) =
      nullResponse nu (nullSource s amplitude) p q := by
  let g (z : ℝ × ℝ) := nullKernel nu p q (z.1+z.2) (z.1-z.2)*oddSource s amplitude z.1 z.2
  have hk := (nullKernel_continuous nu).comp
    (show Continuous (fun z : ℝ × ℝ => ((p,q),(z.1+z.2,z.1-z.2))) by fun_prop)
  have hg : Continuous g := hk.mul (actualSource_continuous s amplitude)
  have hz : ∀ τ y, 0 ≤ τ → τ < |y| → g (τ,y) = 0 := by
    intro τ y hτ hy
    dsimp only [g]
    rw [actualSource_zero_outside s amplitude hτ hy,mul_zero]
  have hT : 0 ≤ (p+q)/2 := by linarith
  rw [radialResponse_retarded,max_eq_left hT]
  calc
    _ = (1/2:ℂ)*∫ σ in (0:ℝ)..((p+q)/2),
        ∫ y in (p-q)/2-((p+q)/2-σ)..(p-q)/2+((p+q)/2-σ), g (σ,y) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro σ hσ
      dsimp only
      have hσ' : σ ∈ Icc 0 ((p+q)/2) := by simpa [uIcc_of_le hT] using hσ
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only [g]
      have hy' : y ∈ Icc ((p-q)/2-((p+q)/2-σ)) ((p-q)/2+((p+q)/2-σ)) := by
        simpa [uIcc_of_le (show (p-q)/2-((p+q)/2-σ) ≤
          (p-q)/2+((p+q)/2-σ) by linarith [hσ'.2])] using hy
      rw [nullKernel_eq nu (by linarith [hy'.2] : σ+y ≤ p)
        (by linarith [hy'.1] : σ-y ≤ q)]
      rw [show (p+q-(σ+y)-(σ-y))/2 = (p+q)/2-σ by ring,
        show (σ+y-(σ-y))/2 = y by ring]
    _ = (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q, g ((a+b)/2,(a-b)/2) :=
      retarded_null_change g hg hz hp hq
    _ = _ := by
      unfold nullResponse nullSource
      congr 1
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro b hb
      dsimp only [g]
      rw [show (a+b)/2+(a-b)/2 = a by ring,
        show (a+b)/2-(a-b)/2 = b by ring]

/-- The original causal source integral satisfies the forced characteristic equation,
with its exact source normalization and physical potential. -/
theorem radialResponse_goursat (nu s amplitude : ℂ) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    radialResponse nu s amplitude ((p+q)/2) ((p-q)/2) =
      (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..q,
        oddSource s amplitude ((a+b)/2) ((a-b)/2))+
      ∫ c in (0:ℝ)..p, ∫ d in (0:ℝ)..q,
        nu*(nu+1)/(4*(Real.cosh ((c-d)/2):ℂ)^2)*
          radialResponse nu s amplitude ((c+d)/2) ((c-d)/2) := by
  rw [radialResponse_null nu s amplitude hp hq,
    nullResponse_goursat nu (nullSource s amplitude) (nullSource_continuous s amplitude) hp hq]
  congr 1
  apply intervalIntegral.integral_congr
  intro c hc
  have hc' : 0 ≤ c := (show c ∈ Icc 0 p by simpa [uIcc_of_le hp] using hc).1
  apply intervalIntegral.integral_congr
  intro d hd
  have hd' : 0 ≤ d := (show d ∈ Icc 0 q by simpa [uIcc_of_le hq] using hd).1
  dsimp only [nullPotential]
  rw [radialResponse_null nu s amplitude hc' hd']



private def nullEffective (nu s amplitude : ℂ) (z : ℝ × ℝ) : ℂ :=
  (1/4:ℂ)*nullSource s amplitude z+
    nullPotential nu z.1 z.2*radialResponse nu s amplitude ((z.1+z.2)/2) ((z.1-z.2)/2)

private theorem nullEffective_continuous (nu s amplitude : ℂ) :
    Continuous (nullEffective nu s amplitude) := by
  have hu := (radialResponse_continuous nu s amplitude).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  exact (continuous_const.mul (nullSource_continuous s amplitude)).add
    ((nullPotential_continuous nu).mul hu)

private theorem radialResponse_primitive (nu s amplitude : ℂ) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    radialResponse nu s amplitude ((p+q)/2) ((p-q)/2) =
      ∫ c in (0:ℝ)..p, ∫ d in (0:ℝ)..q, nullEffective nu s amplitude (c,d) := by
  rw [radialResponse_goursat nu s amplitude hp hq]
  have hF := nullSource_continuous s amplitude
  have hV := (nullPotential_continuous nu).mul
    ((radialResponse_continuous nu s amplitude).comp
      (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop))
  have hi (c : ℝ) : (∫ d in (0:ℝ)..q, nullEffective nu s amplitude (c,d)) =
      (1/4:ℂ)*(∫ d in (0:ℝ)..q, nullSource s amplitude (c,d))+
      ∫ d in (0:ℝ)..q, nullPotential nu c d*
        radialResponse nu s amplitude ((c+d)/2) ((c-d)/2) := by
    dsimp only [nullEffective]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
    · exact (continuous_const.mul (hF.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 q
    · exact (hV.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 q
  simp_rw [hi]
  rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
  · rfl
  · exact (show Continuous (fun c => (1/4:ℂ)*∫ d in (0:ℝ)..q, nullSource s amplitude (c,d))
      by fun_prop).intervalIntegrable 0 p
  · exact (integral_continuous (fun c d =>
      nullPotential nu c d*radialResponse nu s amplitude ((c+d)/2) ((c-d)/2))
      (by convert! hV using 1) (fun _ => 0) (fun _ => q)
      continuous_const continuous_const).intervalIntegrable 0 p

private theorem radialResponse_null_first (nu s amplitude : ℂ) {p q : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) :
    HasDerivAt (fun c => radialResponse nu s amplitude ((c+q)/2) ((c-q)/2))
      (∫ d in (0:ℝ)..q, nullEffective nu s amplitude (p,d)) p := by
  have hE := nullEffective_continuous nu s amplitude
  have hi : Continuous (fun c => ∫ d in (0:ℝ)..q, nullEffective nu s amplitude (c,d)) := by fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 p)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hp] with c hc
  exact radialResponse_primitive nu s amplitude (le_of_lt hc) hq

/-- The actual forced response obeys the mixed null-coordinate wave equation.
The source term and potential are both retained, for every complex channel parameter. -/
theorem radialResponse_null_wave (nu s amplitude : ℂ) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) :
    deriv (fun d => deriv (fun c =>
      radialResponse nu s amplitude ((c+d)/2) ((c-d)/2)) p) q =
      (1/4:ℂ)*oddSource s amplitude ((p+q)/2) ((p-q)/2)+
      nu*(nu+1)/(4*(Real.cosh ((p-q)/2):ℂ)^2)*
        radialResponse nu s amplitude ((p+q)/2) ((p-q)/2) := by
  have hi := (nullEffective_continuous nu s amplitude).comp
    (show Continuous (fun d : ℝ => (p,d)) by fun_prop)
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 q)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  have he : (fun d => deriv (fun c =>
      radialResponse nu s amplitude ((c+d)/2) ((c-d)/2)) p) =ᶠ[𝓝 q]
      (fun d => ∫ b in (0:ℝ)..d, nullEffective nu s amplitude (p,b)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hq] with d hd
    exact (radialResponse_null_first nu s amplitude hp (le_of_lt hd)).deriv
  exact (hd.congr_of_eventuallyEq he).deriv



private def staticEffective (nu s amplitude : ℂ) (z : ℝ × ℝ) : ℂ :=
  oddSource s amplitude z.1 z.2+
    nu*(nu+1)/(Real.cosh z.2:ℂ)^2*radialResponse nu s amplitude z.1 z.2

private theorem staticEffective_continuous (nu s amplitude : ℂ) :
    Continuous (staticEffective nu s amplitude) := by
  have hv : Continuous (fun z : ℝ × ℝ => nu*(nu+1)/(Real.cosh z.2:ℂ)^2) := by
    apply Continuous.div continuous_const
    · fun_prop
    · intro z
      exact pow_ne_zero 2 (by exact_mod_cast (Real.cosh_pos z.2).ne')
  exact (actualSource_continuous s amplitude).add (hv.mul (radialResponse_continuous nu s amplitude))

private theorem staticEffective_zero_outside (nu s amplitude : ℂ) {τ y : ℝ}
    (hτ : 0 ≤ τ) (hy : τ < |y|) : staticEffective nu s amplitude (τ,y) = 0 := by
  have hu := radialResponse_zero_outside nu s amplitude τ y (by simpa [max_eq_left hτ] using hy)
  simp only [staticEffective,actualSource_zero_outside s amplitude hτ hy,hu,mul_zero,add_zero]

private theorem staticEffective_null (nu s amplitude : ℂ) (p q : ℝ) :
    staticEffective nu s amplitude ((p+q)/2,(p-q)/2) =
      4*nullEffective nu s amplitude (p,q) := by
  dsimp only [staticEffective,nullEffective,nullSource,nullPotential]
  ring

/-- The native response satisfies the exact retarded free-wave Duhamel equation
for its original forcing plus the full variable potential, on the entire spatial line. -/
theorem radialResponse_freeDuhamel (nu s amplitude : ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) :
    radialResponse nu s amplitude τ x = (1/2:ℂ)*∫ σ in (0:ℝ)..τ,
      ∫ y in x-(τ-σ)..x+(τ-σ),
        oddSource s amplitude σ y+
          nu*(nu+1)/(Real.cosh y:ℂ)^2*radialResponse nu s amplitude σ y := by
  change _ = (1/2:ℂ)*∫ σ in (0:ℝ)..τ,
    ∫ y in x-(τ-σ)..x+(τ-σ), staticEffective nu s amplitude (σ,y)
  by_cases hx : |x| ≤ τ
  · have hp : 0 ≤ τ+x := by have := (abs_le.mp hx).1; linarith
    have hq : 0 ≤ τ-x := by have := (abs_le.mp hx).2; linarith
    have hu := radialResponse_primitive nu s amplitude hp hq
    have hc := retarded_null_change (staticEffective nu s amplitude)
      (staticEffective_continuous nu s amplitude)
      (fun σ y hσ hy => staticEffective_zero_outside nu s amplitude hσ hy) hp hq
    rw [show (τ+x+(τ-x))/2 = τ by ring,show (τ+x-(τ-x))/2 = x by ring] at hu hc
    rw [hu,hc]
    simp_rw [staticEffective_null,intervalIntegral.integral_const_mul]
    ring
  · have hx' : τ < |x| := lt_of_not_ge hx
    rw [radialResponse_zero_outside nu s amplitude τ x (by simpa [max_eq_left hτ] using hx')]
    have hi : (∫ σ in (0:ℝ)..τ,
        ∫ y in x-(τ-σ)..x+(τ-σ), staticEffective nu s amplitude (σ,y)) = 0 := by
      refine (intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_).trans (by simp)
      intro σ hσ
      dsimp only
      have hσ' : σ ∈ Icc 0 τ := by simpa [uIcc_of_le hτ] using hσ
      refine (intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_).trans (by simp)
      intro y hy
      dsimp only
      have hy' : y ∈ Icc (x-(τ-σ)) (x+(τ-σ)) := by
        simpa [uIcc_of_le (show x-(τ-σ) ≤ x+(τ-σ) by linarith [hσ'.2])] using hy
      have hc : |x-y| ≤ τ-σ := abs_le.mpr ⟨by linarith [hy'.2],by linarith [hy'.1]⟩
      have ht := abs_sub_le x y 0
      simp only [sub_zero] at ht
      exact staticEffective_zero_outside nu s amplitude hσ'.1 (by linarith)
    rw [hi,mul_zero]


/-- The literal radial source integral in the original null rectangle, with its exact
Jacobian and physical Riemann kernel at every source point. -/
theorem radialResponse_null_native (nu s amplitude : ℂ) {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 ≤ r) :
    radialResponse nu s amplitude ((p+r)/2) ((p-r)/2) =
      (1/4:ℂ)*∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
        riemannKernel nu ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)*
          oddSource s amplitude ((a+b)/2) ((a-b)/2) := by
  rw [radialResponse_null nu s amplitude hp hr]
  unfold nullResponse nullSource
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  have ha' : a ≤ p := (show a ∈ Icc 0 p by simpa [uIcc_of_le hp] using ha).2
  have hb' : b ≤ r := (show b ∈ Icc 0 r by simpa [uIcc_of_le hr] using hb).2
  dsimp only
  rw [nullKernel_eq nu ha' hb']

end
end RHTower.D4BMNativeResponse
