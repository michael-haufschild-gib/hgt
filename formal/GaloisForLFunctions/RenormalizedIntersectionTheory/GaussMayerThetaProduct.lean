import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerThetaRay

/-! The actual Gaussian-ray correlation has an exact weight-one functional equation
after subtraction of its two endpoint terms. Its continued Mellin transform
is the ordinary absolutely convergent correlation integral on the central strip. -/

open Complex Set Filter MeasureTheory HurwitzZeta Asymptotics
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.LatticeSectionTheory
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerThetaProduct
open MayerThetaRay

/-- The actual Gaussian-ray correlation at rectangular aspect ratio `a`. -/
def thetaProduct (a t : ℝ) : ℂ := thetaRay t*thetaRay (a^2*t)

/-- Removing both constant terms makes the correlation a weight-one functional-equation pair. -/
def renormalizedProduct (a t : ℝ) : ℂ :=
  thetaProduct a t-1/4-(1/(4*(a : ℂ)))*(t : ℂ)^(-1 : ℂ)

private theorem ray_real {t : ℝ} (ht : 0 < t) :
    thetaRay t=((thetaSum t-1-(t^(1/2 : ℝ))⁻¹ : ℝ) : ℂ)/2 := by
  rw [thetaRay,show (-1/2 : ℂ)= -(1/2 : ℂ) by ring,Complex.cpow_neg]
  have hp : (t : ℂ)^(1/2 : ℂ)=((t^(1/2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]
    norm_num
  rw [hp]
  push_cast
  rfl

/-- The reciprocal-volume subtraction preserves the weight-one-half theta symmetry. -/
theorem thetaRay_inv {t : ℝ} (ht : 0 < t) :
    thetaRay (1/t)=((t^(1/2 : ℝ) : ℝ) : ℂ)*thetaRay t := by
  have hp : t^(1/2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hf := thetaSum_inv ht
  have htinv : 0 < 1/t := one_div_pos.mpr ht
  rw [ray_real htinv,ray_real ht]
  rw [one_div,Real.inv_rpow ht.le,inv_inv]
  have he : thetaSum t⁻¹=t^(1/2 : ℝ)*thetaSum t := by
    rw [hf]
    field_simp
  rw [he]
  push_cast
  have hpC : ((t^(1/2 : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  field_simp [hpC]
  ring


/-- Reciprocal aspect ratio and reciprocal heat time interchange the two theta factors. -/
theorem thetaProduct_inv {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    thetaProduct a (1/t)=((t/a : ℝ) : ℂ)*thetaProduct (1/a) t := by
  have hat : 0 < (1/a)^2*t := mul_pos (sq_pos_of_pos (one_div_pos.mpr ha)) ht
  have he : a^2*(1/t)=1/((1/a)^2*t) := by field_simp
  have hp : t^(1/2 : ℝ)*((1/a)^2*t)^(1/2 : ℝ)=t/a := by
    rw [← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (one_div_pos.mpr ha).le]
    calc
      Real.sqrt t*(1/a*Real.sqrt t)=(1/a)*(Real.sqrt t)^2 := by ring
      _ = t/a := by rw [Real.sq_sqrt ht.le]; ring
  rw [thetaProduct,thetaProduct,thetaRay_inv ht,he,thetaRay_inv hat]
  calc
    _ = (((t^(1/2 : ℝ)*((1/a)^2*t)^(1/2 : ℝ) : ℝ) : ℂ))*
        (thetaRay t*thetaRay ((1/a)^2*t)) := by push_cast; ring
    _ = _ := by rw [hp]

/-- Subtracting the two endpoint terms gives an exact weight-one functional equation. -/
theorem renormalizedProduct_inv {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    renormalizedProduct a (1/t)=((t/a : ℝ) : ℂ)*renormalizedProduct (1/a) t := by
  rw [renormalizedProduct,renormalizedProduct,thetaProduct_inv ha ht]
  simp only [Complex.cpow_neg_one,Complex.ofReal_div,one_div,Complex.ofReal_inv,inv_inv]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp [haC,htC]
  ring


private theorem continuousOn_thetaRay : ContinuousOn thetaRay (Ioi 0) := by
  refine continuousOn_of_forall_continuousAt fun t ht => ?_
  have htheta : ContinuousAt (fun t : ℝ => (thetaSum t : ℂ)) t :=
    continuous_ofReal.continuousAt.comp
      (continuousOn_thetaSum.continuousAt (isOpen_Ioi.mem_nhds ht))
  exact ((htheta.sub continuousAt_const).sub
    (continuousAt_ofReal_cpow_const t (-1/2 : ℂ) (Or.inr ht.ne'))).div_const 2

private theorem continuousOn_thetaProduct {a : ℝ} (ha : 0 < a) :
    ContinuousOn (thetaProduct a) (Ioi 0) := by
  exact continuousOn_thetaRay.mul (continuousOn_thetaRay.comp
    (continuous_const.mul continuous_id).continuousOn
    (fun t ht => mul_pos (sq_pos_of_pos ha) ht))

private theorem continuousOn_renormalizedProduct {a : ℝ} (ha : 0 < a) :
    ContinuousOn (renormalizedProduct a) (Ioi 0) := by
  refine (continuousOn_thetaProduct ha |>.sub continuousOn_const).sub ?_
  refine continuousOn_const.mul (continuousOn_of_forall_continuousAt fun t ht => ?_)
  exact continuousAt_ofReal_cpow_const t (-1 : ℂ) (Or.inr ht.ne')

private theorem isBigO_scaled_theta {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (fun t : ℝ => (thetaSum (a^2*t) : ℂ)-1) =O[atTop] (fun t : ℝ => t^r) := by
  have hcomp : (fun t : ℝ => (thetaSum (a^2*t) : ℂ)-1) =O[atTop]
      (fun t : ℝ => (rectTheta a t : ℂ)-1) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hat : 0 < a^2*t := mul_pos (sq_pos_of_pos ha) ht
    have h1 := one_le_thetaSum ht
    have h2 := one_le_thetaSum hat
    have h3 := one_le_rectTheta ha.ne' ht
    rw [one_mul,← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_sub,
      Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr h2),Real.norm_of_nonneg (sub_nonneg.mpr h3)]
    unfold rectTheta
    nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (zero_le_one.trans h2)]
  exact hcomp.trans (isBigO_rectTheta_sub_one ha.ne' r)

private theorem thetaRay_scaled {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    thetaRay (a^2*t)=((thetaSum (a^2*t) : ℂ)-1-
      (a : ℂ)⁻¹*(t : ℂ)^(-1/2 : ℂ))/2 := by
  have hat : 0 < a^2*t := mul_pos (sq_pos_of_pos ha) ht
  have hp : (a^2*t)^(1/2 : ℝ)=a*t^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq ha.le]
  have htP : (t : ℂ)^(-1/2 : ℂ)=((t^(1/2 : ℝ) : ℝ) : ℂ)⁻¹ := by
    rw [show (-1/2 : ℂ)= -(1/2 : ℂ) by ring,Complex.cpow_neg,
      Complex.ofReal_cpow ht.le]
    norm_num
  rw [ray_real hat,hp,htP]
  push_cast
  rw [mul_inv]

/-- Expansion into five absolutely convergent theta defects in the source half-plane. -/
theorem thetaProduct_source_expansion {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    4*(thetaProduct a t-(1/(4*(a : ℂ)))*(t : ℂ)^(-1 : ℂ))=
      ((rectTheta a t : ℂ)-1)-((thetaSum t : ℂ)-1)-((thetaSum (a^2*t) : ℂ)-1)-
      (a : ℂ)⁻¹*(t : ℂ)^(-1/2 : ℂ)*((thetaSum t : ℂ)-1)-
      (t : ℂ)^(-1/2 : ℂ)*((thetaSum (a^2*t) : ℂ)-1) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp : (t : ℂ)^(-1/2 : ℂ)*(t : ℂ)^(-1/2 : ℂ)=(t : ℂ)^(-1 : ℂ) := by
    rw [← Complex.cpow_add _ _ ht0]
    congr 1
    ring
  rw [thetaProduct,thetaRay_scaled ha ht,thetaRay,rectTheta,Complex.ofReal_mul,← hp]
  ring

#print axioms thetaRay_inv
#print axioms thetaProduct_inv
#print axioms renormalizedProduct_inv
#print axioms thetaProduct_source_expansion


private theorem halfPower_bounded :
    (fun t : ℝ => (t : ℂ)^(-1/2 : ℂ)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht)]
  simp only [show (-1/2 : ℂ).re=(-1/2 : ℝ) by norm_num,norm_one,mul_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)

private theorem renormalizedProduct_rapid {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (fun t : ℝ => renormalizedProduct a t-(-1/4)) =O[atTop] (fun t : ℝ => t^r) := by
  have htheta : (fun t : ℝ => (thetaSum t : ℂ)-1) =O[atTop] (fun t : ℝ => t^r) := by
    simpa only [one_pow,one_mul] using isBigO_scaled_theta (a := 1) zero_lt_one r
  have hscaled := isBigO_scaled_theta ha r
  have hweighted : (fun t : ℝ => (t : ℂ)^(-1/2 : ℂ)*((thetaSum t : ℂ)-1))
      =O[atTop] (fun t : ℝ => t^r) := by
    simpa only [one_mul] using halfPower_bounded.mul htheta
  have hweightedScaled : (fun t : ℝ => (t : ℂ)^(-1/2 : ℂ)*((thetaSum (a^2*t) : ℂ)-1))
      =O[atTop] (fun t : ℝ => t^r) := by
    simpa only [one_mul] using halfPower_bounded.mul hscaled
  have h := ((((isBigO_rectTheta_sub_one ha.ne' r).sub htheta).sub hscaled).sub
    (hweighted.const_mul_left (a : ℂ)⁻¹)).sub hweightedScaled
  refine (h.const_mul_left (1/4 : ℂ)).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have he := thetaProduct_source_expansion ha ht
  unfold renormalizedProduct
  linear_combination -(1/4 : ℂ)*he

/-- The actual theta correlation, with both endpoint terms removed, supplies a weight-one
functional-equation pair. All decay and local-integrability fields are proved from theta. -/
def productFEPair (a : ℝ) (ha : 0 < a) : WeakFEPair ℂ where
  f := renormalizedProduct a
  g := renormalizedProduct (1/a)
  k := 1
  ε := ((1/a : ℝ) : ℂ)
  f₀ := -1/4
  g₀ := -1/4
  hf_int := (continuousOn_renormalizedProduct ha).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_renormalizedProduct (one_div_pos.mpr ha)).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := Complex.ofReal_ne_zero.mpr (one_div_pos.mpr ha).ne'
  h_feq t ht := by
    rw [renormalizedProduct_inv ha ht,Real.rpow_one]
    simp only [smul_eq_mul,Complex.ofReal_div,Complex.ofReal_one]
    ring
  hf_top := renormalizedProduct_rapid ha
  hg_top := renormalizedProduct_rapid (one_div_pos.mpr ha)

#print axioms productFEPair

private def head (t : ℝ) : ℂ := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t

private def tail (t : ℝ) : ℂ := (t : ℂ)^(-1 : ℂ)*head t⁻¹

private theorem tail_hasMellin {u : ℂ} (hu : u.re < 1) :
    HasMellin tail u (1/(1-u)) := by
  have hh : 0 < (-u+1).re := by simp; linarith only [hu]
  have h : MellinConvergent (fun t : ℝ => (t : ℂ)^(1 : ℂ) • head t) (-u) := by
    rw [MellinConvergent.cpow_smul]
    exact (hasMellin_one_Ioc hh).1
  have hi := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => (t : ℂ)^(1 : ℂ) • head t) (s := u) (a := -1) (by norm_num)).mpr
    (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,div_neg,div_one] using h)
  constructor
  · unfold tail
    simpa only [Complex.cpow_neg_one,Complex.ofReal_inv,
      Real.rpow_neg_one,Complex.cpow_one,smul_eq_mul] using! hi
  · have he := mellin_comp_inv (fun t : ℝ => (t : ℂ)^(1 : ℂ) • head t) u
    have hhM : HasMellin head (-u+1) (1/(-u+1)) := hasMellin_one_Ioc hh
    rw [mellin_cpow_smul,hhM.2] at he
    unfold tail
    simpa only [Complex.cpow_neg_one,Complex.ofReal_inv,Complex.cpow_one,
      smul_eq_mul,show -u+1=1-u by ring] using! he

private theorem thetaProduct_eq_modified {a t : ℝ} (ha : 0 < a)
    (ht : 0 < t) (ht1 : t ≠ 1) :
    thetaProduct a t=(productFEPair a ha).f_modif t+
      (1/4 : ℂ)*head t+(1/(4*(a : ℂ)))*tail t := by
  rcases lt_or_gt_of_ne ht1 with hs | hl
  · have hsmall : t ∈ Ioo (0 : ℝ) 1 := ⟨ht,hs⟩
    have hhead : t ∈ Ioc (0 : ℝ) 1 := ⟨ht,hs.le⟩
    have hlarge : t ∉ Ioi (1 : ℝ) := not_lt.mpr hs.le
    have hi : 1 < t⁻¹ := by
      have hdiv : (1 : ℝ) < 1/t := (lt_div_iff₀ ht).mpr (by simpa only [one_mul] using hs)
      simpa only [one_div] using hdiv
    have hnot : t⁻¹ ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.mpr hi) h.2
    simp only [WeakFEPair.f_modif,productFEPair,Pi.add_apply,
      Set.indicator_of_mem hsmall,Set.indicator_of_notMem hlarge,zero_add,
      renormalizedProduct,head,tail,Set.indicator_of_mem hhead,
      Set.indicator_of_notMem hnot,mul_zero,mul_one,add_zero,
      Real.rpow_neg_one,Complex.cpow_neg_one,Complex.ofReal_inv,
      Complex.ofReal_div,Complex.ofReal_one,smul_eq_mul]
    ring
  · have hsmall : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt.mpr hl.le) h.2
    have hhead : t ∉ Ioc (0 : ℝ) 1 := fun h => (not_le.mpr hl) h.2
    have hlarge : t ∈ Ioi (1 : ℝ) := hl
    have hinv : t⁻¹ ∈ Ioc (0 : ℝ) 1 := ⟨inv_pos.mpr ht,by
      have hdiv : 1/t < (1 : ℝ) := (div_lt_one ht).mpr hl
      simpa only [one_div] using hdiv.le⟩
    simp only [WeakFEPair.f_modif,productFEPair,Pi.add_apply,
      Set.indicator_of_notMem hsmall,Set.indicator_of_mem hlarge,add_zero,
      renormalizedProduct,head,tail,Set.indicator_of_notMem hhead,
      Set.indicator_of_mem hinv,mul_zero,mul_one,add_zero]
    ring

/-- On the central strip, the continued transform is the ordinary absolutely convergent
Mellin integral of the actual theta correlation. -/
theorem thetaProduct_hasMellin {a : ℝ} (ha : 0 < a) {u : ℂ}
    (hu : 0 < u.re) (hu1 : u.re < 1) :
    HasMellin (thetaProduct a) u ((productFEPair a ha).Λ u) := by
  have hF : HasMellin (productFEPair a ha).f_modif u ((productFEPair a ha).Λ₀ u) :=
    ⟨((productFEPair a ha).isStrongFEPair_toStrongFEPair.hasMellin u).1,rfl⟩
  have hh : HasMellin head u (1/u) := hasMellin_one_Ioc hu
  have ht := tail_hasMellin hu1
  have hh4 := hasMellin_const_smul hh.1 (1/4 : ℂ)
  have ht4 := hasMellin_const_smul ht.1 (1/(4*(a : ℂ)))
  have hs1 := hasMellin_add hF.1 hh4.1
  have hm := hasMellin_add hs1.1 ht4.1
  rw [hs1.2,hF.2,hh4.2,ht4.2,hh.2,ht.2] at hm
  have hval : (productFEPair a ha).Λ₀ u+(1/4 : ℂ) • (1/u)+
      (1/(4*(a : ℂ))) • (1/(1-u))=(productFEPair a ha).Λ u := by
    rw [WeakFEPair.Λ]
    change _=(productFEPair a ha).Λ₀ u-(1/u) • (-1/4 : ℂ)-
      (((1/a : ℝ) : ℂ)/(1-u)) • (-1/4 : ℂ)
    simp only [smul_eq_mul,Complex.ofReal_div,Complex.ofReal_one]
    ring
  have hne : ∀ᵐ t : ℝ ∂volume,t ≠ 1 := by simp [ae_iff]
  have hae : thetaProduct a =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (productFEPair a ha).f_modif t+(1/4 : ℂ) • head t+
        (1/(4*(a : ℂ))) • tail t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae hne] with t ht ht1
    simpa only [smul_eq_mul] using thetaProduct_eq_modified ha ht ht1
  constructor
  · apply MeasureTheory.Integrable.congr hm.1
    filter_upwards [hae] with t ht
    rw [ht]
  · calc
      mellin (thetaProduct a) u=mellin
          (fun t => (productFEPair a ha).f_modif t+(1/4 : ℂ) • head t+
            (1/(4*(a : ℂ))) • tail t) u := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with t ht
        rw [ht]
      _ = _ := hm.2.trans hval

#print axioms thetaProduct_hasMellin

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerThetaProduct
