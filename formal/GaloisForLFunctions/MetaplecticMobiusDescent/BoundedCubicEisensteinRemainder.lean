/-
Uniform Eisenstein remainder bounds adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCompactHeightProfiles

/-!
# The Eisenstein series minus its incoming seed is bounded

In a reduced cusp chart, transformed height times integral row-coordinate
norm is bounded whenever the first row entry is nonzero. A coprime row
with zero first entry has a unit second entry. Removing the incoming
height profile therefore gives a uniform four-dimensional lattice majorant.
For `Re s>4` it is summable, so the actual quotient remainder belongs to L².
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma norm_ringComplex_unit (u : Oˣ) : ‖ringComplex (u : O)‖=1 := by
  have hu := one_le_normSq_embedding (u : O) u.ne_zero
  have hv := one_le_normSq_embedding (↑(u⁻¹) : O) (u⁻¹).ne_zero
  have hprod : Complex.normSq (ringComplex (u : O))*
      Complex.normSq (ringComplex (↑(u⁻¹) : O))=1 := by
    rw [←Complex.normSq_mul,←map_mul,←Units.val_mul,mul_inv_cancel,Units.val_one,map_one,Complex.normSq_one]
  have he : Complex.normSq (ringComplex (u : O))=1 := by
    nlinarith only [hu,hv,hprod,
      mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
  rw [Complex.normSq_eq_norm_sq] at he
  nlinarith only [he,norm_nonneg (ringComplex (u : O))]

lemma rowCoordinates_zero : rowCoordinates (0 : Fin 2 → O)=0 := by
  apply norm_le_zero_iff.mp
  have h := coordinates_norm_bound (0 : Fin 2 → O)
  have he : (fun i : Fin 2 => ringComplex ((0 : Fin 2 → O) i))=0 := by
    funext i
    exact map_zero _
  rw [he,norm_zero,mul_zero] at h
  exact h

lemma rowCoordinates_norm_pos {u : Fin 2 → O} (hu : u≠0) :
    0<‖rowCoordinates u‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact hu (rowCoordinates_injective (h.trans rowCoordinates_zero.symm))

lemma rowCoordinates_le_horizontal (u : Fin 2 → O) (z : ℂ) (hz : ‖z‖≤1) :
    ‖rowCoordinates u‖≤2*(‖ringComplex (u 0)*z+ringComplex (u 1)‖+
      ‖ringComplex (u 0)‖) := by
  apply (coordinates_norm_bound u).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [Fin.zero_eta]
    linarith [norm_nonneg (ringComplex (u 0)*z+ringComplex (u 1))]
  · have h : ‖ringComplex (u 1)‖≤
        ‖ringComplex (u 0)*z+ringComplex (u 1)‖+‖ringComplex (u 0)*z‖ := by
      simpa only [add_sub_cancel_left] using
        norm_sub_le (ringComplex (u 0)*z+ringComplex (u 1)) (ringComplex (u 0)*z)
    rw [norm_mul] at h
    have hm := mul_le_mul_of_nonneg_left hz (norm_nonneg (ringComplex (u 0)))
    rw [mul_one] at hm
    exact h.trans (add_le_add_right hm _)

lemma height_times_coordinate_bound (A c v N : ℝ)
    (_hA : 0≤A) (hc : 1≤c) (hv : 1/2≤v) (hN : N≤2*(A+c)) :
    N*v≤5*(A^2+c^2*v^2) := by
  have hv0 : 0≤v := by linarith
  have hcv : v≤c*v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hv0
  have hcv0 : 1/2≤c*v := hv.trans hcv
  have hv2 : v^2≤(c*v)^2 := pow_le_pow_left₀ hv0 hcv 2
  have hcross : 2*v*A≤A^2+c^2*v^2 := by nlinarith only [sq_nonneg (A-v),hv2]
  have hlin : 2*c*v≤4*(c*v)^2 := by nlinarith only [hcv0,sq_nonneg (c*v-1/2)]
  have hNv := mul_le_mul_of_nonneg_right hN hv0
  nlinarith only [hNv,hcross,hlin,sq_nonneg A]

lemma rowHeight_times_coordinates (u : Fin 2 → O) (hu : u 0≠0)
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    (v/(‖ringComplex (u 0)*z+ringComplex (u 1)‖^2+
       ‖ringComplex (u 0)‖^2*v^2))*‖rowCoordinates u‖≤5 := by
  have hc : 1≤‖ringComplex (u 0)‖ := by
    have hh := one_le_normSq_embedding (u 0) hu
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith only [hh,norm_nonneg (ringComplex (u 0))]
  have hden : 0<‖ringComplex (u 0)*z+ringComplex (u 1)‖^2+
      ‖ringComplex (u 0)‖^2*v^2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm v] using
    height_times_coordinate_bound _ _ _ _ (norm_nonneg _) hc hv
      (rowCoordinates_le_horizontal u z hz)

lemma positive_rpow_of_product_bound (h N C σ : ℝ)
    (hh : 0≤h) (hN : 0<N) (hC : 0≤C) (hσ : 0≤σ) (hb : h*N≤C) :
    h^σ≤C^σ*N^(-σ) := by
  have hdiv : h≤C/N := (le_div_iff₀ hN).mpr hb
  have hr := Real.rpow_le_rpow hh hdiv hσ
  rw [Real.div_rpow hC hN.le,div_eq_mul_inv] at hr
  simpa only [Real.rpow_neg hN.le] using hr

def cuspRemainderProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v-cuspSeedProfile a b s v

lemma cuspRemainderProfile_norm_le (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ‖cuspRemainderProfile a b s v‖≤v^s.re := by
  have hnon : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hle : 1-cuspTransition a b v≤1 := by
    have := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤cuspTransition a b v at this
    linarith
  have he : cuspRemainderProfile a b s v=
      ((1-cuspTransition a b v:ℝ):ℂ)*positiveHeightPower s v := by
    simp only [cuspRemainderProfile,cuspSeedProfile,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  rw [he,norm_mul,Complex.norm_of_nonneg hnon,positiveHeightPower_eq_cpow s v hv,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hv.le _) hle

lemma cuspRemainderProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b≤v) : cuspRemainderProfile a b s v=0 := by
  rw [cuspRemainderProfile,cuspSeedProfile_incoming a b s v hab hbv hv,
    positiveHeightPower_eq_cpow s v hv,sub_self]

lemma cuspRemainderProfile_norm_le_bound (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hb : 0≤b) (hv : 0<v) (hs : 0≤ s.re) :
    ‖cuspRemainderProfile a b s v‖≤b^s.re := by
  by_cases h : b≤v
  · rw [cuspRemainderProfile_zero a b s v hab hv h,norm_zero]
    exact Real.rpow_nonneg hb _
  · exact (cuspRemainderProfile_norm_le a b s v hv).trans
      (Real.rpow_le_rpow hv.le (le_of_not_ge h) hs)

lemma integral_row_embedding_ne_zero {u : Fin 2 → O} (hu : u≠0) :
    (ringComplex ∘ u)≠0 := by
  intro h
  apply hu
  funext i
  apply ringComplex_injective
  simpa only [Function.comp_apply,Pi.zero_apply,map_zero] using congrFun h i

lemma coprime_row_ne_zero {u : Fin 2 → O} (h : IsCoprime (u 0) (u 1)) : u≠0 := by
  intro hz
  have hh : (0 : O)=1 := by
    simpa only [hz,Pi.zero_apply,isCoprime_zero_left,isUnit_zero_iff] using h
  exact zero_ne_one hh

theorem cuspRemainderProfile_row_bound (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤ s.re)
    (u : Fin 2 → O) (hcop : IsCoprime (u 0) (u 1))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    ‖cuspRemainderProfile a b s (transformedHeight z v (ringComplex ∘ u))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates u‖^(-s.re) := by
  have hu := coprime_row_ne_zero hcop
  have hN := rowCoordinates_norm_pos hu
  have hv0 : 0<v := by linarith
  have hh : 0<transformedHeight z v (ringComplex ∘ u) :=
    div_pos hv0 (heightDenominator_pos z v hv0 _ (integral_row_embedding_ne_zero hu))
  have hC : 0≤ max 5 (2*b) := (by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)
  by_cases hc : u 0=0
  · have hunit : IsUnit (u 1) := by simpa only [hc,isCoprime_zero_left] using hcop
    obtain ⟨d,hd⟩ := hunit
    have hdnorm : ‖ringComplex (u 1)‖=1 := by
      rw [←hd]
      exact norm_ringComplex_unit d
    have hn : ‖rowCoordinates u‖≤2 := by
      apply (coordinates_norm_bound u).trans
      have hm : ‖fun i => ringComplex (u i)‖≤1 := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro i
        fin_cases i
        · change ‖ringComplex (u 0)‖≤1
          simp only [hc,map_zero,norm_zero,zero_le_one]
        · exact hdnorm.le
      nlinarith only [hm]
    apply (cuspRemainderProfile_norm_le_bound a b s _ hab hb hh hs).trans
    exact positive_rpow_of_product_bound b _ _ _ hb hN hC hs
      (by nlinarith only [mul_le_mul_of_nonneg_left hn hb,le_max_right (5 : ℝ) (2*b)])
  · apply (cuspRemainderProfile_norm_le a b s _ hh).trans
    apply positive_rpow_of_product_bound _ _ _ _ hh.le hN hC hs
    exact (rowHeight_times_coordinates u hc z hz v hv).trans (le_max_left _ _)

def translatedCuspRow (M : SL(2,O)) (r : CuspCosets) : Fin 2 → O :=
  Matrix.vecMul (cosetRow r) (M : Matrix (Fin 2) (Fin 2) O)

lemma translatedCuspRow_injective (M : SL(2,O)) : Function.Injective (translatedCuspRow M) := by
  intro r t h
  apply cosetRow_injective
  have hh := congrArg (fun u : Fin 2 → O => Matrix.vecMul u
    ((M⁻¹ : SL(2,O)) : Matrix (Fin 2) (Fin 2) O)) h
  simpa only [translatedCuspRow,Matrix.vecMul_vecMul,←Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one] using hh

lemma integral_bottom_coprime (M : SL(2,O)) : IsCoprime (M 1 0) (M 1 1) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by
    simpa only [Matrix.det_fin_two] using M.property
  refine ⟨-M 0 1,M 0 0,?_⟩
  linear_combination hd

lemma translatedCuspRow_coprime (M : SL(2,O)) (r : CuspCosets) :
    IsCoprime (translatedCuspRow M r 0) (translatedCuspRow M r 1) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change IsCoprime (translatedCuspRow M (cosetOf N) 0) (translatedCuspRow M (cosetOf N) 1)
    simpa only [translatedCuspRow,cosetRow_cosetOf,row,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Matrix.vecMul,dotProduct] using integral_bottom_coprime ((N : SL(2,O))*M)

lemma cosetHeight_integral_chart (M : SL(2,O)) (r : CuspCosets)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    cosetHeight r (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (ringComplex ∘ translatedCuspRow M r) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf N) (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (ringComplex ∘ translatedCuspRow M (cosetOf N))
    rw [cosetHeight_cosetOf,←integralComplexMatrix_levelThree,
      ←mul_smul,←map_mul,hyperbolicHeight_action_upperPoint]
    have hentry (A : SL(2,O)) (i j : Fin 2) :
        integralComplexMatrix A i j=ringComplex (A i j) := rfl
    simp only [hentry,transformedHeight,heightDenominator,
      Function.comp_apply,translatedCuspRow,cosetRow_cosetOf,row,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Matrix.vecMul,dotProduct]

lemma translated_remainder_majorant (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤ s.re)
    (M : SL(2,O)) (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v)
    (hv0 : 0<v) (r : CuspCosets) :
    ‖(cosetCharacter r)⁻¹*cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates (translatedCuspRow M r)‖^(-s.re) := by
  rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul,cosetHeight_integral_chart]
  exact cuspRemainderProfile_row_bound a b s hab hb hs _
    (translatedCuspRow_coprime M r) z hz v hv

lemma cuspCutoffTerm_eq_seedProfile (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (r : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm 1 (cuspSeedProfile a b s) r w=
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
  unfold cuspCutoffTerm
  split_ifs with h
  · rfl
  · rw [cuspSeedProfile_zero a b s _ hab ((le_of_not_gt h).trans ha),mul_zero]

lemma cusp_seed_profile_summable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => (cosetCharacter r)⁻¹*
      cuspSeedProfile a b s (cosetHeight r w)) :=
  (cuspCutoffTerm_summable 1 le_rfl _ w).congr
    (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)

theorem eisenstein_sub_seed_eq_series (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w-smoothCuspSeed a b s w=
      ∑'r : CuspCosets,(cosetCharacter r)⁻¹*
        cuspRemainderProfile a b s (cosetHeight r w) := by
  have hE := (height_series_summable_norm s hs w).of_norm
  have hS := cusp_seed_profile_summable a b ha hab s w
  have heq : smoothCuspSeed a b s w=∑'r : CuspCosets,
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
    unfold smoothCuspSeed cuspCutoffCorrection
    exact tsum_congr (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)
  rw [hyperbolicEisenstein_eq_height_series,heq,←hE.tsum_sub hS]
  apply tsum_congr
  intro r
  rw [cuspRemainderProfile,positiveHeightPower_eq_cpow s _ (cosetHeight_pos r w)]
  ring

def eisensteinRemainderBound (b : ℝ) (s : ℂ) : ℝ :=
  (max 5 (2*b))^s.re * ∑'n : (Fin 2×Fin 2)→ℤ,‖n‖^(-s.re)

lemma eisensteinRemainderBound_nonneg (b : ℝ) (s : ℂ) :
    0≤eisensteinRemainderBound b s :=
  mul_nonneg (Real.rpow_nonneg ((by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)) _)
    (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _))

theorem eisenstein_sub_seed_chart_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,O))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    ‖hyperbolicEisenstein s (integralComplexMatrix M • upperPoint z v hv0)-
      smoothCuspSeed a b s (integralComplexMatrix M • upperPoint z v hv0)‖≤
      eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℂ := fun r => (cosetCharacter r)⁻¹*cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,‖R r‖≤G (f r) :=
    translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0
  have hr : Summable (fun r => ‖R r‖) :=
    (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [eisenstein_sub_seed_eq_series a b ha hab s (by linarith)]
  change ‖∑'r,R r‖≤eisensteinRemainderBound b s
  apply (norm_tsum_le_tsum_norm hr).trans
  have hsum : (∑'r,‖R r‖)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem eisenstein_sub_seed_bounded (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    ‖hyperbolicEisenstein s w-smoothCuspSeed a b s w‖≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith only [hz,norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith only [hh,hh0,hfloor]
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact eisenstein_sub_seed_chart_bound a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainderProfile_measurable (a b : ℝ) (s : ℂ) :
    Measurable (cuspRemainderProfile a b s) := by
  unfold cuspRemainderProfile cuspSeedProfile positiveHeightPower logRatioPower cuspTransition
  fun_prop

lemma eisenstein_sub_seed_measurable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    Measurable (fun w => hyperbolicEisenstein s w-smoothCuspSeed a b s w) := by
  simp_rw [eisenstein_sub_seed_eq_series a b ha hab s hs]
  apply Measurable.tsum
  intro r
  exact measurable_const.mul ((cuspRemainderProfile_measurable a b s).comp
    (cosetHeight_continuous r).measurable)

theorem kernel_eisenstein_sub_seed_memLp (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    MemLp (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hmeas : Measurable (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) :=
    measurable_from_quotient.mpr (eisenstein_sub_seed_measurable a b ha hab s (by linarith))
  apply MemLp.of_bound hmeas.aestronglyMeasurable (eisensteinRemainderBound b s)
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact eisenstein_sub_seed_bounded a b ha hab s hs w

#print axioms cuspRemainderProfile_row_bound
#print axioms eisenstein_sub_seed_bounded
#print axioms kernel_eisenstein_sub_seed_memLp
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
