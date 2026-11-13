/-
Euler coordinates of the probe adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.GramIdealMass

/-!
# Euler coordinates of the probe

The Euler coordinates `ProbeEuler.coordV`, `coordD`, `coordW`, `coordR` and the unramified
closed correction; the radial Fourier Mellin transform is the reflected source transform times
its gamma factor; second-region bounds.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ cubic_units_finite

def lowActualIdealPolynomial {ι : Type*} [Fintype ι]
    (L : ι→Finset Id) (w : ι→Id→ℂ) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  ∑p : ∀i,L i,(∏i,w i (p i).val)*InverseMoment.markedCompletedT Ψ W X
    (fun A=>∏i,if (p i).val∣A then (1:ℂ) else 0)

theorem lowSelectedInverseRow_actual_ideal {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=> Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (z : O) :
    lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t σ z=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        lowActualIdealPolynomial
          (fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
          (fun i I=> lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryIdealGenerator I))
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X := by
  rw [lowSelectedInverseRow_correction]
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  simp_rw [lowSelectedWeight_eq_product]
  have hm (b : LowSelectedTuple (fun i=> canonicalSlotSupport (T i)) J) :
      (fun A : Id=> if lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0) := by
    funext A
    exact lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b) A
  simp_rw [hm,←physical_markedCompletedT_absorb_true_period η S hS hbad σ χ]
  convert low_actual_ideal_polynomial η S hS hbad (fun i : SelectedSlot J=> T i.val)
    (fun i=> hT i.val) (fun i=> hout i.val) (fun i=> W i.val) (fun i=> Y i.val) t
    (fun p=> InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
      (fun A=>∏i : SelectedSlot J,if p i∣A then (1:ℂ) else 0)) using 1
  · congr 1
    ext p
    simp
  · rfl

theorem lowSelectedInverseRow_actual_reflected_energy {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=> Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=> canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
    lowCorrectionEnergy*∑χ : RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
      ‖lowActualIdealPolynomial
        (fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
        (fun i I=> lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryIdealGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (cubicIdealGenerator (1:Id)) (u.val*cubicIdealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) X‖^2 := by
  simp_rw [lowSelectedInverseRow_actual_ideal η S hS hbad T hT hout hdis J W Y X t σ]
  apply (fixed_correction_energy R ProbeCompleted.correctionCoeff _).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (lowReflectionMask η S hS) (fun Ψ=> lowActualIdealPolynomial
      (fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
      (fun i I=> lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryIdealGenerator I)) Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical

lemma lowUnselectedProduct_norm_upper_nominal {K : ℕ} (ell : Fin K→ℝ)
    (b Z : ℝ) (hZ : 0< Z) (slots : Fin K→Finset Eisenstein.O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))
    (J : Finset (Fin K)) (p : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(p i).val)≤(max 1 b)^K*Z^(lowUnselectedLength ell J) := by
  have hc : J.card≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,max 1 b*Z^(ell i.val) := Finset.prod_le_prod
      (fun _ _=> by unfold elementNorm;positivity)
      (fun i _=>(hslots i.val _ (p i).property).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    _=(max 1 b)^J.card*Z^(lowUnselectedLength ell J) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ,Finset.sum_coe_sort]
      rfl
    _≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) hc) (by positivity)

theorem eventually_low_selected_caps {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (b ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧ ∀J : Finset (Fin K),
      (∏i : SelectedSlot J,max 1 (b*Z^(ell i.val)))≤ Z^(lowSelectedLength ell J+ε/2) := by
  have hp : 0<ε/2 := by linarith
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hp).eventually (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro J
  apply (lowSelectedCaps_product ell hell J Z b hZ.le).trans
  calc
    _≤ Z^(ε/2)*Z^(lowSelectedLength ell J) := mul_le_mul_of_nonneg_right hc (by positivity)
    _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];congr 1;ring

def lowCentralShift (Z T ell0 : ℝ) : ℝ := Real.logb Z T-1-ell0

lemma lowCentralShift_scale (Z T ell0 : ℝ) (hZ : 1< Z) (hT : 0< T) :
    Z^(1+ell0+lowCentralShift Z T ell0)=T := by
  rw [lowCentralShift,show 1+ell0+(Real.logb Z T-1-ell0)=Real.logb Z T by ring]
  exact Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hT

lemma lowCentralShift_bound (Z T ell ε : ℝ) (hZ : 1< Z) (hT : 0< T) (hε : 0≤ε)
    (hlo : Z^(1+ell-ε/2)≤ T) (hhi : T≤ Z^(1+ell+ε/2)) :
    |lowCentralShift Z T (ell+ε/2)|≤ε := by
  have he := lowCentralShift_scale Z T (ell+ε/2) hZ hT
  rw [←he,Real.rpow_le_rpow_left_iff hZ] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma lowCentral_ratio_bounds (Z T ell ε : ℝ) (hZ : 0< Z)
    (hlo : Z^(-ε/2)≤ T/Z^(1+ell)) (hhi : T/Z^(1+ell)≤ Z^(ε/2)) :
    Z^(1+ell-ε/2)≤ T ∧ T≤ Z^(1+ell+ε/2) := by
  constructor
  · have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hlo
    convert hh using 1 <;> first
    | rfl
    | rw [←Real.rpow_add hZ]; congr 1; ring
  · have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hZ (1+ell))).mp hhi
    convert hh using 1 <;> first
    | rfl
    | rw [←Real.rpow_add hZ]; congr 1; ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical

lemma low_inverse_power_cancel (Z d α : ℝ) (hZ : 0< Z) :
    Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0< q) (hC : 0≤ C) (_hB : 0≤ B) (hZ : 0< Z) (hL : 0< L) (hH : 1≤ H)
    (hE : 0≤ E) (hEL : E≤ C*H^n*Z^(5/6-2*d+α)) (hLB : L≤ B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(5/6:ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(5/6:ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(5/6-2*d+α))/(q*Z^(5/6:ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(5/6-2*d+α))*L^2/(q*Z^(5/6:ℝ)) := by field_simp
      _≤(C*H^n*Z^(5/6-2*d+α))*(B*Z^d)^2/(q*Z^(5/6:ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_square : ∃C : ℝ,0< C ∧
    ∀(T : Finset HeckeIdealSeries.PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-2:ℝ))≤ C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=> I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-2:ℝ))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I ^ (-2:ℝ) := by
    rw [Finset.sum_image (fun P _ Q _ h=> hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=> elementNorm a.val^(-2:ℝ))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

lemma lowUnselectedWeight_norm_identity {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖*elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ))=
      ∏i : J,elementNorm (a i).val^(-2:ℝ)*‖W i.val (elementNorm (a i).val/P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  calc
    _=(elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ))*elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ)))*
        ∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by ring
    _=elementNorm (∏i : J,(a i).val)^(-2:ℝ)*∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by
      rw [←Real.rpow_add hL]
      norm_num
    _=_ := by
      rw [elementNorm_finset_prod,Finset.prod_mul_distrib,Real.finsetProd_rpow Finset.univ
        (fun i : J=> elementNorm (a i).val) (fun i _=> by unfold elementNorm;positivity)]

theorem lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤ M) :
    ∃C : ℝ,0< C ∧ ∀(T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤ M)→
      (∑a : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P a‖*
          elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ)))≤ C := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_square
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=> canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-2:ℝ)*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod (fun i _=> Finset.sum_nonneg (fun a _=> mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-2:ℝ)*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-2:ℝ))*M := (Finset.sum_mul ..).symm
        _≤ C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod (fun _ _=> by positivity) (fun _ _=> le_max_right _ _)
    _≤ _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma canonicalSlot_count (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (H : ℝ) (hH : 1≤ H) (hnorm : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤ H) :
    ((canonicalSlotSupport T).card:ℝ)≤128*H := by
  have hh := EisensteinLatticeCount.finite_ideal_count_real (lowPrimeIdealList T) H hH
    (fun I hI=>(lowPrimeIdealList_prime T I hI).ne_zero) (lowPrimeIdealList_norm T H hnorm)
  have he := Fintype.card_congr (canonicalSlotEquiv T hT)
  simp only [Fintype.card_coe] at he
  rw [lowPrimeIdealList,Finset.card_image_of_injective _ Subtype.val_injective,he] at hh
  exact hh

lemma canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤1/6) (b Z : ℝ) (hZ : 1≤ Z)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(1/6:ℝ) := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod (fun i _=> Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma slotProduct_norm_ge_one {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    1≤ elementNorm (slotProduct p J) := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr (slotProduct_nonzero p hp J)))

lemma compensationSubsetWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) (Y : Fin K→ℝ)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    ‖compensationSubsetWeight η W Y p J‖≤1 := by
  rw [compensationSubsetWeight,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) _).trans _
  · rw [compensationSubsetCoefficient,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (slotProduct_norm_pos p hp J).le _),norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos (slotProduct_norm_ge_one p hp J) (by norm_num))).trans (ProbeRow.targetMonoid_norm_le_one η _)
  · rw [norm_prod]
    exact Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun i _=> hW i _)

lemma compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hZ : 1≤ Z) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=> Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=> Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=> W i.val)
      (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(17/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(23/48:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^(5/6:ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun (i : SelectedSlot J) _=> hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=> hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤ elementNorm C.generator*Z^(5/6:ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(1/6:ℝ)*Z^(5/6:ℝ)) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter
namespace ProbeRaySlots
open HeckeFamily ProbePhysical
local notation "Id" => Ideal Eisenstein.O

lemma annular_power_separation (a b r s : ℝ) (ha : 0< a) (hrs : r< s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r< a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0< s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b< a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0< Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring

theorem power_pools_eventually_disjoint {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0< a i) (hab : ∀i,a i≤ b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀i j, i≠j→Disjoint (pool C S (a i) (b i) (Z^(ell i)))
      (pool C S (a j) (b j) (Z^(ell j))) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun Z hn=>(hn hij).elim)
  have hne : ell i≠ell j := fun h=> hij (hell h)
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · filter_upwards [annular_power_separation (a j) (b i) (ell i) (ell j) (ha j) hlt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith
  · filter_upwards [annular_power_separation (a i) (b j) (ell j) (ell i) (ha i) hgt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith

theorem power_pool_tuples_eventually_injective {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0< a i) (hab : ∀i,a i≤ b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀P:(∀i,pool C S (a i) (b i) (Z^(ell i))),
      Function.Injective (fun i=>(P i).val) := by
  filter_upwards [power_pools_eventually_disjoint C S a b ell ha hab hell] with Z hZ P
  intro i j heq
  by_contra hn
  have hq : (P i).val=(P j).val := heq
  exact Finset.disjoint_left.mp (hZ i j hn) (P i).property (by rw [hq];exact (P j).property)
end ProbeRaySlots
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace Probe
noncomputable section

def principalScalar {ι : Type*} (slots : Finset ι) (Z ℓ : ℝ) (S : ι → ℝ) : ℝ :=
  (-1) ^ slots.card * Z ^ (-ℓ / 6) * ∏ i ∈ slots, S i

theorem principalScalar_ne_zero {ι : Type*} (slots : Finset ι)
    {Z ℓ : ℝ} {S : ι → ℝ} (hZ : 0 < Z)
    (hS : ∀ i ∈ slots, 0 < S i) : principalScalar slots Z ℓ S ≠ 0 := by
  unfold principalScalar
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ne_of_gt (Real.rpow_pos_of_pos hZ _))
  · exact ne_of_gt (Finset.prod_pos hS)

def normalizedProbe (I A : ℝ → ℂ) (c : ℂ) (Z : ℝ) : ℂ := I Z / (c * A Z)

theorem normalizedProbe_error (I A f : ℝ → ℂ) {c : ℂ} {Z : ℝ}
    (hc : c ≠ 0) (hA : A Z ≠ 0) :
    normalizedProbe I A c Z - f Z = (I Z - (c * A Z) * f Z) / (c * A Z) := by
  unfold normalizedProbe
  field_simp

theorem norm_div_bound {I B : ℂ} {Z C D a ε : ℝ} (hZ : 0 < Z)
    (hI : ‖I‖ ≤ C * Z ^ a) (hB : ‖B⁻¹‖ ≤ D * Z ^ ε) :
    ‖I / B‖ ≤ (C * D) * Z ^ (a + ε) := by
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add hZ]
  calc
    ‖I‖ * ‖B⁻¹‖ ≤ (C * Z ^ a) * (D * Z ^ ε) :=
      mul_le_mul hI hB (norm_nonneg _) ((norm_nonneg _).trans hI)
    _ = C * D * (Z ^ a * Z ^ ε) := by ring

theorem common_normalization_bounds (I A f : ℝ → ℂ) {c : ℂ}
    {Z C_low C_high D a b ε : ℝ} (hZ : 0 < Z)
    (hc : c ≠ 0) (hA : A Z ≠ 0)
    (hrecip : ‖(c * A Z)⁻¹‖ ≤ D * Z ^ ε)
    (hlow : ‖I Z‖ ≤ C_low * Z ^ a)
    (hhigh : ‖I Z - (c * A Z) * f Z‖ ≤ C_high * Z ^ b) :
    ‖normalizedProbe I A c Z‖ ≤ (C_low * D) * Z ^ (a + ε) ∧
    ‖normalizedProbe I A c Z - f Z‖ ≤ (C_high * D) * Z ^ (b + ε) := by
  constructor
  · exact norm_div_bound hZ hlow hrecip
  · rw [normalizedProbe_error I A f hc hA]
    exact norm_div_bound hZ hhigh hrecip

end
end Probe

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace ProbeRayNormalization
open HeckeFamily ProbePhysical ProbeRaySlots
local notation "Id" => Ideal Eisenstein.O

theorem log_power_absorption (c ell d : ℝ) (hc : 0< c) (hell : 0< ell) (hd : 0< d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤ c*(Z^ell)^(1/6:ℝ)/Real.log (Z^ell) := by
  have hh := (isLittleO_log_rpow_atTop hd).bound (div_pos hc hell)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  have hZ0 : 0< Z := by linarith
  have hlog : 0< Real.log Z := Real.log_pos hZ1
  have hzd : 0< Z^d := Real.rpow_pos_of_pos hZ0 _
  have hb : ell*Real.log Z≤ c*Z^d := by
    have hb' : Real.log Z≤(c/ell)*Z^d := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hzd] using hZ
    calc
      _ ≤ ell*((c/ell)*Z^d) := mul_le_mul_of_nonneg_left hb' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hZ0,←Real.rpow_mul hZ0.le]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    Z^(ell/6-d)*(ell*Real.log Z) ≤ Z^(ell/6-d)*(c*Z^d) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZ0.le _)
    _ = c*Z^(ell*(1/6:ℝ)) := by
      rw [mul_left_comm,←Real.rpow_add hZ0]
      congr 1
      ring_nf

theorem principalScalar_inverse_of_slot_bounds {ι : Type*} (J : Finset ι)
    (ell mass : ι→ℝ) (Z d eps : ℝ) (hZ : 1≤ Z) (_hd : 0≤ d)
    (hbudget : d*J.card≤ eps) (hm : ∀i∈J,Z^(ell i/6-d)≤ mass i) :
    |(Probe.principalScalar J Z (∑i∈J,ell i) mass)⁻¹|≤ Z^eps := by
  have hZ0 : 0< Z := by linarith
  have hm0 : ∀i∈J,0≤ mass i := fun i hi=>(Real.rpow_nonneg hZ0.le _).trans (hm i hi)
  have hprod : Z^(∑i∈J,(ell i/6-d))≤∏i∈J,mass i := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_le_prod (fun i _=> Real.rpow_nonneg hZ0.le _) hm
  have hn : |Probe.principalScalar J Z (∑i∈J,ell i) mass|=
      Z^(-(∑i∈J,ell i)/6)*(∏i∈J,mass i) := by
    unfold Probe.principalScalar
    rw [abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hZ0 _),abs_of_nonneg (Finset.prod_nonneg hm0)]
  have hpow : Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d))=Z^(-d*J.card) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    rw [Finset.sum_sub_distrib,←Finset.sum_div,Finset.sum_const,nsmul_eq_mul]
    ring
  have hl : Z^(-eps)≤|Probe.principalScalar J Z (∑i∈J,ell i) mass| := by
    calc
      _ ≤ Z^(-d*J.card) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      _ = Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d)) := hpow.symm
      _ ≤ _ := by rw [hn];exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hZ0.le _)
  rw [abs_inv]
  have hi := (inv_le_inv₀ ((Real.rpow_pos_of_pos hZ0 (-eps)).trans_le hl)
    (Real.rpow_pos_of_pos hZ0 (-eps))).mpr hl
  simpa only [Real.rpow_neg hZ0.le,inv_inv] using hi

variable (M : Id) [NeZero M]
local instance : Finite (Eisenstein.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (Eisenstein.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
include hH

theorem ray_slot_subpower_lower (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0< a) (hab : a≤ b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤ W y) (hWne : W≠0) (ell d : ℝ) (hell : 0< ell) (hd : 0< d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b (Z^ell),
        W ((Ideal.absNorm P.val:ℝ)/(Z^ell))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := ray_pool_mass_eventually_lower_bound M H hH S W a b ha hab hsupp hW hc hp hW0 hWne
  filter_upwards [(tendsto_rpow_atTop hell).eventually hbound,log_power_absorption c ell d hc0 hell hd]
    with Z hZ hlog
  exact hlog.trans hZ

theorem ray_principalScalar_inverse_subpower {ι : Type*} (J : Finset ι)
    (S : Finset Id) (W : ι→ℝ→ℝ) (a b ell : ι→ℝ)
    (ha : ∀i∈J,0< a i) (hab : ∀i∈J,a i≤ b i)
    (hsupp : ∀i∈J,Function.support (W i)⊆Set.Ioo (a i) (b i))
    (hW : ∀i∈J,ContDiff ℝ ∞ (W i)) (hc : ∀i∈J,HasCompactSupport (W i))
    (hp : ∀i∈J,tsupport (W i)⊆Set.Ioi 0)
    (hW0 : ∀i∈J,∀y,0≤ W i y) (hWne : ∀i∈J,W i≠0) (hell : ∀i∈J,0< ell i)
    (eps : ℝ) (heps : 0< eps) :
    ∀ᶠZ : ℝ in atTop,
      |(Probe.principalScalar J Z (∑i∈J,ell i) (fun i=>
        ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
          W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ))))⁻¹|≤ Z^eps := by
  let d : ℝ := eps/(J.card+1)
  have hd : 0< d := div_pos heps (by positivity)
  have hb : d*J.card≤ eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)< J.card+1)]
    nlinarith
  have hm : ∀ᶠZ : ℝ in atTop,∀i∈J,Z^(ell i/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
        W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    exact ray_slot_subpower_lower M H hH S (W i) (a i) (b i) (ha i hi) (hab i hi)
      (hsupp i hi) (hW i hi) (hc i hi) (hp i hi) (hW0 i hi) (hWne i hi) (ell i) d (hell i hi) hd
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with Z hmass hZ
  exact principalScalar_inverse_of_slot_bounds J ell _ Z d eps hZ hd.le hb hmass

end ProbeRayNormalization
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform RealInnerProductSpace Topology
namespace ProbeRadialMellin

def laplace (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, f r * Complex.exp (-(t*r : ℝ))

lemma mellin_real (f : ℝ → ℂ) (s : ℝ) :
    mellin f (s : ℂ) = ∫ r : ℝ in Ioi 0, (r^(s-1) : ℝ) • f r := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma mellinConvergent_real (f : ℝ → ℂ) (s : ℝ) :
    MellinConvergent f (s : ℂ) ↔
      IntegrableOn (fun r : ℝ => (r^(s-1) : ℝ) • f r) (Ioi 0) := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma gamma_scaled_integrable {s r : ℝ} (hs : 0< s) (hr : 0< r) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  have hg : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s : ℂ) := by
    rw [mellinConvergent_real]
    simpa only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, mul_comm] using!
      (Real.GammaIntegral_convergent hs).ofReal (𝕜 := ℂ)
  have hh := (MellinConvergent.comp_mul_left (f := fun t : ℝ => (Real.exp (-t) : ℂ))
    (s := (s : ℂ)) hr).mpr hg
  rw [mellinConvergent_real] at hh
  simpa only [RCLike.smul_re, RCLike.ofReal_re] using! hh.re

lemma gamma_scaled_integral {s r : ℝ} (hs : 0< s) (hr : 0< r) :
    (∫ t : ℝ in Ioi 0, t^(s-1)*Real.exp (-(r*t))) =
      r^(-s)*Real.Gamma s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_neg hr.le]

lemma laplace_mellin_integrable (f : ℝ → ℂ) (s : ℂ) (hs : 0< s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    Integrable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    exact hf.comp_fst.mul (by fun_prop)
  have hn (r t : ℝ) (ht : 0< t) :
      ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖ =
        ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t))) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_exp]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re]
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply ((gamma_scaled_integrable hs hr).const_mul ‖f r‖).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hn r t ht).le
  · have hw : IntegrableOn (fun r : ℝ => r^(-s.re)*‖f r‖) (Ioi 0) := by
      apply hconv.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.sub_re, Complex.one_re]
      congr 2
      ring
    apply (hw.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hi : (fun t : ℝ => ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hn r t ht
    rw [integral_congr_ae hi]
    rw [integral_const_mul, gamma_scaled_integral hs hr]
    ring

lemma mellin_laplace (f : ℝ → ℂ) (s : ℂ) (hs : 0< s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    mellin (laplace f) s = Complex.Gamma s * mellin f (1-s) := by
  have hi := laplace_mellin_integrable f s hs hf hconv
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ r : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) := by
      unfold mellin laplace
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [mul_comm r t]
      ring
    _ = ∫ r : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) :=
      integral_integral_swap hi.swap
    _ = ∫ r : ℝ in Ioi 0, f r*((r:ℂ)^(-s)*Complex.Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [integral_const_mul]
      have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
      simp only [Complex.ofReal_mul] at *
      rw [hh, one_div, inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
    _ = _ := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [show 1-s-1 = -s by ring, smul_eq_mul]
      ring

open SchwartzPlanePoisson

def paperConstant : ℝ := 2*Real.pi/Real.sqrt 3

lemma paperConstant_pos : 0< paperConstant := by
  unfold paperConstant
  positivity

lemma paperConstant_sq : paperConstant^2 = 4*Real.pi^2/3 := by
  unfold paperConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma paperE_norm (z : ℂ) : ‖paperE z‖=1 := by
  exact tracePhase_norm _

lemma paper_fourier_pairing (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ u : ℂ, paperFourier f u * g u) = ∫ z : ℂ, f z * paperFourier g z := by
  have hi : Integrable (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))*f p.2*g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))) := by
        change Continuous (fun p : ℂ × ℂ =>
          tracePhase (-(p.2*p.1) / ringComplex traceLambda))
        exact tracePhase_continuous.comp (by fun_prop)
      exact (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
        hg.aestronglyMeasurable.comp_fst
    · exact Eventually.of_forall fun p => by
        simp only [norm_mul, paperE_norm, one_mul]
        exact le_of_eq (mul_comm _ _)
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (hi.const_mul ((2/Real.sqrt 3:ℝ):ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [mul_comm z u]; ring

lemma paper_gaussian_fourier (t : ℝ) (ht : 0< t) (u : ℂ) :
    paperFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) u =
      (paperConstant/t:ℝ)*Complex.exp (-(paperConstant^2*‖u‖^2/t:ℝ)) := by
  rw [paperFourier_eq_standard,
    fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2:ℂ)≠0), Complex.cpow_one]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, paperFrequency_norm_sq, paperConstant_sq]
  push_cast
  have he : -(Real.pi:ℂ)^2*((4/3:ℝ)*‖u‖^2:ℝ)/(t:ℂ) =
      -((4*Real.pi^2/3*‖u‖^2/t:ℝ):ℂ) := by push_cast; ring
  push_cast at he
  rw [he]
  unfold paperConstant
  push_cast
  ring

lemma radial_continuous (W : SchwartzMap ℝ ℂ) : Continuous (paperRadialFourier W) := by
  rw [paperRadialFourier_eq_ray]
  exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt

lemma radial_isBigO_top (W : SchwartzMap ℝ ℂ) (A : ℕ) :
    paperRadialFourier W =O[atTop] (fun r : ℝ => r^(-(A:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W A 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hh := hb 0 (by omega) r hr
  simp only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hh
  have hp : r^A * ‖paperRadialFourier W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le (by linarith : r≤1+r) A)
      (norm_nonneg _)).trans hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa [mul_comm] using hp)

lemma radial_isBigO_zero (W : SchwartzMap ℝ ℂ) :
    paperRadialFourier W =O[𝓝[>] 0] (fun r : ℝ => r^(-(0:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W 0 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa [LocalLogFourier.eulerDeriv] using hb 0 (by omega) r hr

theorem radial_mellin_convergent (W : SchwartzMap ℝ ℂ) (z : ℂ) (hz : 0< z.re) :
    MellinConvergent (paperRadialFourier W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz

theorem radial_mellin_differentiable (W : SchwartzMap ℝ ℂ) :
    DifferentiableOn ℂ (mellin (paperRadialFourier W)) {z | 0< z.re} := by
  intro z hz
  obtain ⟨A,hA⟩ := exists_nat_gt z.re
  exact (mellin_differentiableAt_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz).differentiableWithinAt

lemma radial_laplace_duality (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0< t) :
    laplace (paperRadialFourier W) t =
      (paperConstant/t:ℝ)*laplace W (paperConstant^2/t) := by
  have hf : Integrable (fun z : ℂ => W (‖z‖^2)) := (radialTestCLM W).integrable
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) 0 (0:ℂ)
  have h := paper_fourier_pairing _ _ hf hg
  have hleft : (∫ u : ℂ, paperFourier (fun z : ℂ => W (‖z‖^2)) u *
      Complex.exp (-(t:ℂ)*‖u‖^2)) = (Real.pi:ℂ)*laplace (paperRadialFourier W) t := by
    simp_rw [paperFourier_radial]
    rw [laplace, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [Complex.ofReal_mul]
  have hright : (∫ z : ℂ, W (‖z‖^2)*paperFourier
      (fun u : ℂ => Complex.exp (-(t:ℂ)*‖u‖^2)) z) =
      (Real.pi:ℂ)*((paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) := by
    simp_rw [paper_gaussian_fourier t ht]
    rw [laplace, ← integral_const_mul, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      have he : paperConstant^2*‖u‖^2/t = paperConstant^2/t*‖u‖^2 := by ring
      rw [he]
      ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

lemma mellin_reciprocal_laplace (W : ℝ → ℂ) (z : ℂ) :
    mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) =
      (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*mellin (laplace W) z := by
  have hfun : (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) =
      (fun t : ℝ => (paperConstant:ℂ) • ((t:ℂ)^(-1:ℂ) •
        laplace W (paperConstant^2*t⁻¹))) := by
    funext t
    simp [Complex.cpow_neg_one, div_eq_mul_inv, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_const_smul, mellin_cpow_smul]
  rw [show 1-z+(-1) = -z by ring]
  have hh := mellin_comp_inv (fun t : ℝ => laplace W (paperConstant^2*t)) (-z)
  rw [neg_neg] at hh
  rw [hh, mellin_comp_mul_left _ _ (sq_pos_of_pos paperConstant_pos)]
  simp only [smul_eq_mul]
  ring

theorem radial_mellin_gamma (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0< z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*Complex.Gamma z /
        Complex.Gamma (1-z))*mellin W (1-z) := by
  have hc := CubicEisenstein.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (1-z)
  have hL := mellin_laplace (paperRadialFourier W) (1-z)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    ((radial_continuous W).aestronglyMeasurable)
    (by simpa only [sub_sub_cancel] using radial_mellin_convergent W z hz)
  have hR := mellin_laplace W z hz W.continuous.aestronglyMeasurable hc
  have he : mellin (laplace (paperRadialFourier W)) (1-z) =
      mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [radial_laplace_duality W t ht]
  rw [hL, sub_sub_cancel, mellin_reciprocal_laplace, hR] at he
  have hg : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)
  apply (mul_left_cancel₀ hg)
  rw [he]
  field_simp

lemma paper_prefactor (z : ℂ) :
    (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z) =
      (paperConstant:ℂ)^(1-2*z) := by
  have hn : (paperConstant:ℂ)≠0 := Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'
  have hh := Complex.cpow_nat_mul' (x := (paperConstant:ℂ)) (n := 2)
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_pos])
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_nonneg]) (-z)
  push_cast
  rw [← hh, show 1-2*z = 1+2*(-z) by ring, Complex.cpow_add _ _ hn,
    Complex.cpow_one]
  norm_num

/-- The radial Fourier Mellin transform is the reflected source Mellin transform times its gamma factor. -/
theorem radial_mellin_identity (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0< z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  rw [radial_mellin_gamma W a b ha hW z hz hz1, paper_prefactor]

lemma positive_source_mellin (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) : 0<(mellin W (s:ℂ)).re ∧ (mellin W (s:ℂ)).im=0 := by
  have hc := CubicEisenstein.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (s:ℂ)
  have hr : ∀r, W r = ((W r).re:ℂ) := by
    intro r
    apply Complex.ext <;> simp [hreal]
  have he : mellin W (s:ℂ) =
      (((∫ r : ℝ in Ioi 0, r^(s-1)*(W r).re):ℝ):ℂ) := by
    rw [mellin_real, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    rw [hr r, Complex.real_smul, Complex.ofReal_mul]
    simp
  rw [he]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  have hi : IntegrableOn (fun r : ℝ => r^(s-1)*(W r).re) (Ioi 0) := by
    have hh := ((mellinConvergent_real W s).mp hc).re
    simpa only [RCLike.smul_re] using! hh
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).mpr
  · have hset : Function.support (fun r : ℝ => r^(s-1)*(W r).re) ∩ Ioi 0 =
        Function.support (fun r : ℝ => (W r).re) := by
      ext r
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · intro hh
        exact fun h => hh.1 (by rw [h, mul_zero])
      · intro hh
        have hw : W r≠0 := fun h => hh (by rw [h]; rfl)
        have hp := ha.trans_le (hW hw).1
        exact ⟨mul_ne_zero (Real.rpow_pos_of_pos hp _).ne' hh, hp⟩
    rw [hset]
    apply ((Complex.continuous_re.comp W.continuous).isOpen_support).measure_pos volume
    by_contra h
    apply hne
    ext r
    have hh : (W r).re=0 := by
      by_contra hn
      exact h ⟨r,hn⟩
    change W r = 0
    rw [hr r, hh, Complex.ofReal_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (hnonneg r)

theorem radial_mellin_positive (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) (hs : 0< s) (hs1 : s<1) :
    0<(mellin (paperRadialFourier W) (s:ℂ)).re ∧
      (mellin (paperRadialFourier W) (s:ℂ)).im=0 := by
  obtain ⟨hp, hz⟩ := positive_source_mellin W a b ha hW hreal hnonneg hne (1-s)
  have hh : mellin W (1-(s:ℂ)) = ((mellin W ((1-s:ℝ):ℂ)).re:ℂ) := by
    rw [show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl]
    exact Complex.ext (by simp) (by simpa using hz)
  rw [radial_mellin_identity W a b ha hW (s:ℂ) hs hs1, hh]
  have hpow : (paperConstant:ℂ)^(1-2*(s:ℂ)) = ((paperConstant^(1-2*s):ℝ):ℂ) := by
    rw [show 1-2*(s:ℂ)=((1-2*s:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow paperConstant_pos.le]
  rw [hpow, show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.ofReal_im, and_true]
  exact mul_pos (div_pos (mul_pos (Real.rpow_pos_of_pos paperConstant_pos _)
    (Real.Gamma_pos_of_pos hs)) (Real.Gamma_pos_of_pos (by linarith))) hp

theorem radial_mellin_one_sixth_pos (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    0<(mellin (paperRadialFourier W) (1/6)).re ∧
      (mellin (paperRadialFourier W) (1/6)).im=0 := by
  simpa using radial_mellin_positive W a b ha hW hreal hnonneg hne (1/6)
    (by norm_num) (by norm_num)

theorem radial_mellin_identity_right (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0< z.re) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  let D : Set ℂ := {z | 0< z.re}
  let G : ℂ → ℂ := fun z =>
    ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
      mellin W (1-z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) D :=
    (radial_mellin_differentiable W).analyticOnNhd hop
  have hG : DifferentiableOn ℂ G D := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (paperConstant:ℂ)^(1-2*z)) w :=
      (differentiableAt_const _ |>.sub (differentiableAt_id.const_mul 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'))
    have h2 := CubicEisenstein.Gamma_differentiableAt_of_re_pos w hw
    have h3 := (Complex.differentiable_one_div_Gamma (1-w)).comp w
      (differentiableAt_const _ |>.sub differentiableAt_id)
    have h4 := (CubicEisenstein.compact_source_mellin_differentiable W a b ha hW
      (W.smooth ⊤) (1-w)).comp w (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! (((h1.mul h2).mul h3).mul h4).differentiableWithinAt
  have hev : mellin (paperRadialFourier W) =ᶠ[𝓝 (1/2:ℂ)] G := by
    have hstrip : IsOpen {w:ℂ | 0< w.re ∧ w.re<1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with w hw
    exact radial_mellin_identity W a b ha hW w hw.1 hw.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hz

lemma gamma_quotient_strip (lo hi : ℝ) (hlo : 0< lo) :
    ∃ (n : ℕ) (C : ℝ), 0< C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖Complex.Gamma ((σ:ℂ)+t*Complex.I) / Complex.Gamma (1-((σ:ℂ)+t*Complex.I))‖ ≤
        C*(1+|t|)^n := by
  obtain ⟨A,hA⟩ := exists_nat_gt hi
  obtain ⟨C,hC,hb⟩ := CubicEisenstein.Gamma_pair_strip_bound 1 (by norm_num) A
  refine ⟨2*A+2,C/lo,div_pos hC hlo,?_⟩
  intro σ hσ t
  have hσ0 : 0<σ := hlo.trans_le hσ.1
  have hz : (σ:ℂ)+t*Complex.I≠0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
    linarith
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  norm_num only [Complex.ofReal_one] at hh
  rw [add_comm (1:ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : lo≤‖(σ:ℂ)+t*Complex.I‖ := by
    apply hσ.1.trans
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ:ℂ)+t*Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

theorem radial_mellin_strip_decay (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0< lo) (N : ℕ) :
    ∃ C : ℝ, 0< C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      (1+|t|)^N * ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C := by
  obtain ⟨n,Cg,hCg,hg⟩ := gamma_quotient_strip lo hi hlo
  obtain ⟨Cw,hCw,hw⟩ := CubicEisenstein.compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1-hi) (1-lo) (n+N)
  have hc : Continuous (fun σ : ℝ => paperConstant^(1-2*σ)) :=
    (Real.continuous_const_rpow paperConstant_pos.ne').comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc lo hi))
  let Cp := |B|+1
  have hCp : 0< Cp := by dsimp [Cp]; positivity
  refine ⟨Cp*Cg*Cw,by positivity,?_⟩
  intro σ hσ t
  have hp : ‖(paperConstant:ℂ)^(1-2*((σ:ℂ)+t*Complex.I))‖≤ Cp := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos paperConstant_pos]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      show (2:ℂ).re=2 by rfl, show (2:ℂ).im=0 by rfl, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact (hB (mem_image_of_mem _ hσ)).trans (by change B≤|B|+1; linarith [le_abs_self B])
  have hwb := hw (1-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1-σ:ℝ):ℂ)+(-t:ℝ)*Complex.I = 1-((σ:ℂ)+t*Complex.I) by
    push_cast; ring] at hwb
  rw [radial_mellin_identity_right W a b ha hW _ (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact hlo.trans_le hσ.1), mul_div_assoc, norm_mul, norm_mul]
  calc
    _ ≤ (1+|t|)^N*(Cp*(Cg*(1+|t|)^n)*
        ‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = (Cp*Cg)*((1+|t|)^(n+N)*‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwb (by positivity)

theorem radial_mellin_analytic (W : SchwartzMap ℝ ℂ) :
    AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) {z | 0< z.re} :=
  (radial_mellin_differentiable W).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem radial_mellin_strip_rapid (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0< lo) (N : ℕ) :
    ∃ C : ℝ, 0< C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C/(1+|t|)^N := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW lo hi hlo N
  refine ⟨C,hC,fun σ hσ t => (le_div_iff₀ (by positivity)).mpr ?_⟩
  simpa only [mul_comm] using hb σ hσ t

theorem radial_mellin_vertical_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0<σ) :
    Complex.VerticalIntegrable (mellin (paperRadialFourier W)) σ := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW σ σ hσ 2
  have hc : Continuous (fun t : ℝ => mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (radial_mellin_analytic W _ (by simpa using hσ)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using CubicEisenstein.weighted_two_to_cauchy
      (norm_nonneg _) t (hb σ ⟨le_rfl,le_rfl⟩ t)

theorem radial_mellin_inverse_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0< x) :
    Integrable (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*
      mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
  have hi := radial_mellin_vertical_integrable W a b ha hW σ hσ
  apply (hi.norm.const_mul (x^(-σ))).mono'
  · have hm := hi.aestronglyMeasurable
    have hc : Continuous (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))) :=
      (by fun_prop : Continuous (fun t : ℝ => -((σ:ℂ)+t*Complex.I))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact hc.aestronglyMeasurable.mul hm
  · exact Eventually.of_forall fun t => by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

theorem radial_mellin_inversion (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0< x) :
    mellinInv σ (mellin (paperRadialFourier W)) x = paperRadialFourier W x :=
  mellinInv_mellin_eq σ (paperRadialFourier W) hx
    (radial_mellin_convergent W σ hσ)
    (radial_mellin_vertical_integrable W a b ha hW σ hσ)
    (radial_continuous W).continuousAt

theorem radial_mellin_one_sixth_ne_zero (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    mellin (paperRadialFourier W) (1/6) ≠ 0 := by
  intro h
  have hp := (radial_mellin_one_sixth_pos W a b ha hW hreal hnonneg hne).1
  rw [h] at hp
  exact (lt_irrefl 0) hp

end ProbeRadialMellin

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace PrincipalMellinResidues
open ProbePhysical

lemma inverse_vertical_continuous (c : ℝ) (hc : c≠0) :
    Continuous (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t h
  have he := congrArg Complex.re h
  simp at he
  exact hc he

lemma inverse_vertical_truncated (c T : ℝ) (hc : c≠0) :
    (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) = (2*Real.arctan (T/c):ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) volume (-T) T :=
    (inverse_vertical_continuous c hc).intervalIntegrable (-T) T
  apply Complex.ext
  · have hh := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).re at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).re) =
        (fun t : ℝ => c/(c^2+t^2)) := by
      funext t
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [he, integral_div_sq_add_sq]
    simp only [neg_div, Real.arctan_neg, Complex.ofReal_re]
    ring
  · have hh := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).im at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).im) =
        (fun t : ℝ => -(t/(c^2+t^2))) := by
      funext t
      simp [Complex.inv_im, Complex.normSq_apply, pow_two, neg_div]
    rw [he, intervalIntegral.integral_neg]
    have hodd := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => t/(c^2+t^2)) (a := -T) (b := T)
    simp only [neg_sq, neg_div, intervalIntegral.integral_neg, neg_neg] at hodd
    simp only [Complex.ofReal_im]
    linarith

lemma inverse_vertical_limit_pos (c : ℝ) (hc : 0< c) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (Real.pi:ℂ)) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne']
  have ht := Real.tendsto_arctan_atTop.comp (Filter.tendsto_id.atTop_div_const hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_vertical_limit_neg (c : ℝ) (hc : c<0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (-(Real.pi:ℂ))) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne]
  have ht := Real.tendsto_arctan_atBot.comp (Filter.tendsto_id.atTop_div_const_of_neg hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_horizontal_limit (a b p : ℝ) (ε : ℝ) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ T : ℝ in atTop, ‖∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹‖ ≤ T⁻¹ * |b-a| from ?_) ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_inv]
    apply inv_anti₀ hT
    have h := Complex.abs_im_le_norm ((x:ℂ)+(ε*T)*I-p)
    simpa [abs_mul, hε, abs_of_pos hT] using h
  · simpa using (tendsto_inv_atTop_zero.mul_const |b-a|)

lemma dslope_eq_sub_pole {A F : ℂ → ℂ} {p z : ℂ} (hz : z≠p)
    (hF : F z = A z / (z-p)) :
    dslope A p z = F z - A p * (z-p)⁻¹ := by
  rw [dslope_of_ne A hz, slope, hF]
  simp only [smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

lemma dslope_vertical_truncated (A F : ℂ → ℂ) (p x T : ℝ) (hx : x≠p)
    (hF : ∀ z : ℂ, z.re = x → F z = A z / (z-p))
    (hi : Integrable (fun t : ℝ => F ((x:ℂ)+t*I))) :
    (∫ t : ℝ in -T..T, dslope A (p:ℂ) ((x:ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((x:ℂ)+t*I)) -
        A p * (∫ t : ℝ in -T..T, (((x-p:ℝ):ℂ)+t*I)⁻¹) := by
  have he (t : ℝ) : dslope A (p:ℂ) ((x:ℂ)+t*I) =
      F ((x:ℂ)+t*I) - A p * ((((x-p:ℝ):ℂ)+t*I)⁻¹) := by
    have hn : (x:ℂ)+t*I ≠ p := by
      intro h
      exact hx (by simpa using congrArg Complex.re h)
    have h := dslope_eq_sub_pole hn (hF _ (by simp))
    convert h using 1; push_cast; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi.intervalIntegrable
    (((inverse_vertical_continuous (x-p) (sub_ne_zero.mpr hx)).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

lemma rectangle_limits (G : ℂ → ℂ) {a b : ℝ} (hab : a≤ b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a≤ z.re ∧ z.re≤ b})
    {Va Vb : ℂ}
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) atTop (𝓝 Va))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) atTop (𝓝 Vb))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    Va = Vb := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) -
      (∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a:ℂ)+(-T)*I) ((b:ℂ)+T*I) (hG.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      simpa [uIcc_of_le hab] using hz.1
  have hlim := ((hbot.sub htop).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : (0:ℂ)-0+I*Vb-I*Va=0 := tendsto_nhds_unique hlim
    (by simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)))
  exact (mul_left_cancel₀ I_ne_zero (show I*Vb=I*Va by simpa using sub_eq_zero.mp hz)).symm

lemma horizontal_quotient_continuousOn (A : ℂ → ℂ) {a b p y : ℝ}
    (hab : a≤ b) (hy : y≠0)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤ z.re ∧ z.re≤ b}) :
    ContinuousOn (fun x : ℝ => A ((x:ℂ)+y*I) / ((x:ℂ)+y*I-p)) (uIcc a b) := by
  apply ContinuousOn.div
  · apply hA.continuousOn.comp (by fun_prop)
    intro x hx
    simpa [uIcc_of_le hab] using hx
  · fun_prop
  · intro x hx h
    have hh := congrArg Complex.im h
    exact hy (by simpa using hh)

lemma dslope_horizontal_limit (A F : ℂ → ℂ) {a b p : ℝ} (hab : a≤ b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤ z.re ∧ z.re≤ b})
    (hF : ∀ z : ℂ, a≤ z.re → z.re≤ b → z≠p → F z = A z/(z-p))
    (ε : ℝ) (hε : |ε|=1)
    (hlim : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, dslope A p ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
  have hl := hlim.sub ((inverse_horizontal_limit a b p ε hε).const_mul (A p))
  simp only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hy : ε*T≠0 := mul_ne_zero (by intro h; simp [h] at hε) hT.ne'
  have hn (x : ℝ) : (x:ℂ)+(ε*T)*I≠p := by
    intro h
    exact hy (by simpa using congrArg Complex.im h)
  have he (x : ℝ) (hx : x∈uIcc a b) := hF ((x:ℂ)+(ε*T)*I)
    (by have := (uIcc_of_le hab ▸ hx).1; simpa using this)
    (by have := (uIcc_of_le hab ▸ hx).2; simpa using this) (hn x)
  have hfi : IntervalIntegrable (fun x : ℝ => F ((x:ℂ)+(ε*T)*I)) volume a b := by
    apply ((horizontal_quotient_continuousOn A (p:=p) hab hy hA).congr ?_).intervalIntegrable
    intro x hx
    simpa using he x hx
  have hki : IntervalIntegrable (fun x : ℝ => ((x:ℂ)+(ε*T)*I-p)⁻¹) volume a b := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    exact hn x (sub_eq_zero.mp h)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hfi (hki.const_mul _)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (dslope_eq_sub_pole (hn x) (he x hx)).symm

/-- Moving a vertical contour across one simple pole adds its residue. -/
theorem verticalIntegral_simple_pole (A F : ℂ → ℂ) {a b p : ℝ}
    (hap : a< p) (hpb : p< b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤ z.re ∧ z.re≤ b})
    (hF : ∀ z : ℂ, a≤ z.re → z.re≤ b → z≠p → F z = A z/(z-p))
    (ha : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    verticalIntegral b F = verticalIntegral a F + A p := by
  have hab := hap.le.trans hpb.le
  have hnb : {z : ℂ | a≤ z.re ∧ z.re≤ b} ∈ 𝓝 (p:ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a<(p:ℂ).re ∧ (p:ℂ).re< b from ⟨hap,hpb⟩))
    intro z hz
    exact ⟨hz.1.le,hz.2.le⟩
  have hG := (Complex.differentiableOn_dslope hnb).mpr hA
  have haF := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbF := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have haG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((a:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((a:ℂ)+t*I)) - A p * (-(Real.pi:ℂ)))) := by
    simp_rw [dslope_vertical_truncated A F p a _ hap.ne
      (fun z hz => hF z (by simp [hz]) (by simpa [hz] using hab)
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hap.ne this)) ha]
    exact haF.sub ((inverse_vertical_limit_neg (a-p) (sub_neg.mpr hap)).const_mul (A p))
  have hbG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((b:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((b:ℂ)+t*I)) - A p * (Real.pi:ℂ))) := by
    simp_rw [dslope_vertical_truncated A F p b _ hpb.ne'
      (fun z hz => hF z (by simpa [hz] using hab) (by simp [hz])
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hpb.ne' this)) hb]
    exact hbF.sub ((inverse_vertical_limit_pos (b-p) (sub_pos.mpr hpb)).const_mul (A p))
  have hbotG := dslope_horizontal_limit A F hab hA hF (-1) (by norm_num)
    (by simpa using hbot)
  have htopG := dslope_horizontal_limit A F hab hA hF 1 (by norm_num)
    (by simpa using htop)
  have he := rectangle_limits (dslope A p) hab hG haG hbG
    (by simpa using hbotG) (by simpa using htopG)
  have he' : (∫ t : ℝ, F ((b:ℂ)+t*I)) =
      (∫ t : ℝ, F ((a:ℂ)+t*I)) + 2*(Real.pi:ℂ)*A p := by
    linear_combination -he
  unfold verticalIntegral
  rw [he']
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [mul_comm]

structure BoundaryControl (F : ℂ → ℂ) (a b : ℝ) : Prop where
  left : Integrable (fun t : ℝ => F ((a:ℂ)+t*I))
  right : Integrable (fun t : ℝ => F ((b:ℂ)+t*I))
  lower : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0)
  upper : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)

open HeckeFamily

theorem verticalIntegral_hecke (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0< a) (ha1 : a<1) (h1b : 1< b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤ z.re ∧ z.re≤ b})
    (hB : BoundaryControl (fun z => K z * LFunction χ z) a b) :
    verticalIntegral b (fun z => K z * LFunction χ z) =
      verticalIntegral a (fun z => K z * LFunction χ z) +
        K 1 * HeckeReciprocal.regularizedL χ 1 := by
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ z)
    (fun z => K z * LFunction χ z) ha1 h1b
    (hK.mul (HeckeOrigin.poleRemoved_entire χ).differentiableOn) ?_
    hB.left hB.right hB.lower hB.upper
  · simpa [HeckeOrigin.poleRemoved_one] using h
  · intro z hza hzb hzp
    have hz0 : z≠0 := by intro h; subst z; simp at hza; linarith
    have hz1 : z≠1 := by simpa using hzp
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    norm_num
    field_simp

theorem verticalIntegral_hecke_six (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0< a) (hap : a<1/6) (hpb : 1/6< b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤ z.re ∧ z.re≤ b})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) a b) :
    verticalIntegral b (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral a (fun z => K z * LFunction χ (6*z)) +
        K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 := by
  have hhol : Differentiable ℂ (fun z => HeckeOrigin.poleRemoved χ (6*z)) :=
    (HeckeOrigin.poleRemoved_entire χ).comp (differentiable_id.const_mul 6)
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ (6*z) / 6)
    (fun z => K z * LFunction χ (6*z)) hap hpb
    ((hK.mul hhol.differentiableOn).div_const 6) ?_
    hB.left hB.right hB.lower hB.upper
  · norm_num [HeckeOrigin.poleRemoved_one] at h ⊢
    exact h
  · intro z hza hzb hzp
    have hz0 : 6*z≠0 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      have : z.re=0 := by linarith
      linarith
    have hz1 : 6*z≠1 := by
      intro h
      apply hzp
      push_cast
      linear_combination h / 6
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    have hden : z-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hzp)
    push_cast
    field_simp

theorem source_w_shift (χ : Character) (K : ℂ → ℂ → ℂ) (z : ℂ) {cw : ℝ}
    (hcw : 1< cw)
    (hK : DifferentiableOn ℂ (fun w => K w z)
      {w : ℂ | 19/20≤ w.re ∧ w.re≤ cw})
    (hB : BoundaryControl (fun w => K w z * LFunction χ w) (19/20) cw) :
    verticalIntegral cw (fun w => K w z * LFunction χ w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction χ w) +
      K 1 z * HeckeReciprocal.regularizedL χ 1 :=
  verticalIntegral_hecke χ (fun w => K w z) (by norm_num) (by norm_num) hcw hK hB

theorem source_residue_z_shift (χ : Character) (K : ℂ → ℂ) {e : ℝ} (he : 0< e)
    (hK : DifferentiableOn ℂ K {z : ℂ | 33/200≤ z.re ∧ z.re≤1/6+e})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) (33/200) (1/6+e)) :
    verticalIntegral (1/6+e) (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral (33/200) (fun z => K z * LFunction χ (6*z)) +
      K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 :=
  verticalIntegral_hecke_six χ K (by norm_num) (by norm_num) (by linarith) hK hB

lemma verticalIntegral_add (a : ℝ) (F G : ℂ → ℂ)
    (hF : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hG : Integrable (fun t : ℝ => G ((a:ℂ)+t*I))) :
    verticalIntegral a (fun z => F z + G z) = verticalIntegral a F + verticalIntegral a G := by
  unfold verticalIntegral
  rw [integral_add hF hG, mul_add]

lemma verticalIntegral_mul_const (a : ℝ) (F : ℂ → ℂ) (c : ℂ) :
    verticalIntegral a (fun z => F z * c) = verticalIntegral a F * c := by
  unfold verticalIntegral
  rw [integral_mul_const]
  ring

/-- Successive contour shifts separate the two remainders and the double residue. -/
theorem source_ordered_double_shift (χ : Character) (K : ℂ → ℂ → ℂ)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e)
    (hwK : ∀ z : ℂ, z.re=1/6+e → DifferentiableOn ℂ (fun w => K w z)
      {w : ℂ | 19/20≤ w.re ∧ w.re≤ cw})
    (hwB : ∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w) (19/20) cw)
    (hzK : DifferentiableOn ℂ (fun z => K 1 z)
      {z : ℂ | 33/200≤ z.re ∧ z.re≤1/6+e})
    (hzB : BoundaryControl (fun z => K 1 z * LFunction χ (6*z)) (33/200) (1/6+e))
    (houter : Integrable (fun t : ℝ => verticalIntegral (19/20)
      (fun w => K w ((1/6+e:ℝ)+t*I) *
        LFunction χ (6*((1/6+e:ℝ)+t*I)) * LFunction χ w))) :
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) +
    HeckeReciprocal.regularizedL χ 1 *
      verticalIntegral (33/200) (fun z => K 1 z * LFunction χ (6*z)) +
    (HeckeReciprocal.regularizedL χ 1)^2 / 6 * K 1 (1/6) := by
  have hw (z : ℂ) (hz : z.re=1/6+e) := verticalIntegral_hecke χ
    (fun w => K w z * LFunction χ (6*z)) (by norm_num : (0:ℝ)<19/20)
    (by norm_num : (19/20:ℝ)<1) hcw ((hwK z hz).mul_const _) (hwB z hz)
  have hpoint : verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z * LFunction χ (6*z) * LFunction χ w) +
        (K 1 z * LFunction χ (6*z)) * HeckeReciprocal.regularizedL χ 1) := by
    unfold verticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    exact hw _ (by simp)
  rw [hpoint, verticalIntegral_add _ _ _ houter (hzB.right.mul_const _),
    verticalIntegral_mul_const, source_residue_z_shift χ (fun z => K 1 z) he hzK hzB]
  ring

abbrev fixedPrincipal (M : Ideal O) [NeZero M] : Character :=
  HeckeRayFamily.character M 1

def fixedPrincipalResidue (M : Ideal O) [NeZero M] : ℂ :=
  HeckeReciprocal.regularizedL (fixedPrincipal M) 1

theorem fixedPrincipalResidue_ne_zero (M : Ideal O) [NeZero M] :
    fixedPrincipalResidue M ≠ 0 := by
  rw [fixedPrincipalResidue, ← HeckeOrigin.poleRemoved_one]
  exact HeckeRayFamily.principal_pole_ne_zero M

def sourceMultiplier (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta : Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(s+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((s+z-1)^2) *
    mellin (SchwartzPlanePoisson.paperRadialFourier W0) z * mellin W1 w /
      LFunction eta s * H w z * B w z

theorem sourceMultiplier_integrand (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta principal : Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) (w z : ℂ) :
    sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction principal (6*z) * LFunction principal w =
    (X:ℂ)^(1/2-z) * (Z:ℂ)^(s+z-1) * (Y:ℂ)^(w-1) *
      Complex.exp ((s+z-1)^2) *
      mellin (SchwartzPlanePoisson.paperRadialFourier W0) z * mellin W1 w *
      LFunction principal (6*z) * LFunction principal w /
      LFunction eta s * H w z * B w z := by
  unfold sourceMultiplier
  ring

def sourceResidueConstant (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal O) [NeZero M] : ℂ :=
  mellin W1 1 * mellin (SchwartzPlanePoisson.paperRadialFourier W0) (1/6) *
    fixedPrincipalResidue M ^ 2 / 6

theorem source_double_residue (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal O) [NeZero M]
    (X Y Z : ℝ) (eta : Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) :
    fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 X Y Z eta s H B 1 (1/6) =
    sourceResidueConstant W0 W1 M *
      ((X:ℂ)^(1/3:ℂ) * (Z:ℂ)^(s-5/6) * Complex.exp ((s-5/6)^2) /
        LFunction eta s * H 1 (1/6) * B 1 (1/6)) := by
  unfold sourceResidueConstant sourceMultiplier
  rw [show (1/2:ℂ)-1/6=1/3 by norm_num,
    show s+(1/6:ℂ)-1=s-5/6 by ring]
  simp only [sub_self, Complex.cpow_zero, mul_one]
  ring

theorem source_axes_separated (t : ℝ) {cw e : ℝ} (hcw : 1< cw) (he : 0< e) :
    (1/20:ℝ) ≤ ‖((19/20:ℂ)+t*I)-1‖ ∧
    (1/100:ℝ) ≤ ‖6*((33/200:ℂ)+t*I)-1‖ ∧
    6*e ≤ ‖6*(((1/6+e:ℝ):ℂ)+t*I)-1‖ ∧
    cw-1 ≤ ‖((cw:ℂ)+t*I)-1‖ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Complex.abs_re_le_norm (((19/20:ℂ)+t*I)-1)
    norm_num at h ⊢
    exact h
  · have h := Complex.abs_re_le_norm (6*((33/200:ℂ)+t*I)-1)
    norm_num at h ⊢
    exact h
  · have h := Complex.abs_re_le_norm (6*(((1/6+e:ℝ):ℂ)+t*I)-1)
    have hr : (6*(((1/6+e:ℝ):ℂ)+t*I)-1).re=6*e := by simp; ring
    rw [hr, abs_of_pos (by positivity)] at h
    exact h
  · have h := Complex.abs_re_le_norm (((cw:ℂ)+t*I)-1)
    simpa [abs_of_pos (sub_pos.mpr hcw)] using h

end PrincipalMellinResidues

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace ProbeLocal
noncomputable section

def localFactor (V W Pstar : ℂ) : ℂ := 1 / (1 - V) + W / (1 - W) + Pstar

def localCorrection (V W D Pstar : ℂ) : ℂ :=
  localFactor V W Pstar * ((1 - V) * (1 - W)) / (1 - D)

def continuedCorrection (V W D Pstar : ℂ) : ℂ :=
  (1 - V * W + (1 - V) * (1 - W) * Pstar) / (1 - D)

theorem continuedCorrection_eq_raw (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar = localCorrection V W D Pstar := by
  unfold continuedCorrection localCorrection localFactor
  field_simp
  ring

def compensatedReplacement (V W D Pstar B q : ℂ) : ℂ :=
  ((B - q) * (1 - V) * (1 - W) * Pstar - q * (1 - V * W)) / (1 - D)

theorem correction_defect (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    localCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold localCorrection localFactor
  field_simp
  ring

theorem compensatedReplacement_eq_raw (V W D Pstar B q : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hP : localFactor V W Pstar ≠ 0) :
    compensatedReplacement V W D Pstar B q =
      localCorrection V W D Pstar * (B * Pstar / localFactor V W Pstar - q) := by
  unfold localCorrection compensatedReplacement
  field_simp
  unfold localFactor
  field_simp
  ring

theorem compensatedReplacement_ramified (V Pstar B q : ℂ) (hV : 1 - V ≠ 0) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * localCorrection V 0 0 Pstar := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  ring

theorem normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        localCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

theorem continued_normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continued_ramified_compensation (V Pstar B q : ℂ) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * continuedCorrection V 0 0 Pstar := by
  simp only [compensatedReplacement, continuedCorrection, mul_zero, sub_zero,
    mul_one, div_one]
  ring

end
end ProbeLocal

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)

def markedTableSeries (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ∑' r : ℕ, R ^ r *
    ((∑' m : ℕ, (R * (1 - qInv) * V ^ m - K * V ^ (m + a))) + J)

theorem marked_table_resummation (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by
  have hgeo := hasSum_geometric_of_norm_lt_one hV
  have hfirst := hgeo.mul_left (R * (1 - qInv))
  have hsecond : HasSum (fun m : ℕ => K * V ^ (m + a))
      (K * V ^ a * (1 - V)⁻¹) := by
    convert hgeo.mul_left (K * V ^ a) using 1 <;> first
    | rfl
    | funext m; rw [pow_add]; ring
  have hin := (hfirst.sub hsecond).tsum_eq
  unfold markedTableSeries
  rw [hin, tsum_mul_right, tsum_geometric_of_norm_lt_one hR]
  unfold markedFactor
  simp only [div_eq_mul_inv]
  ring

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeLocal

lemma one_sub_ne_zero_of_norm_le_half (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  norm_num at ha

lemma inv_one_sub_norm_le_two (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith

theorem unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by
  rw [ProbeEuler.unramified_marked_error R V qInv K W D
    (one_sub_ne_zero_of_norm_le_half R hR) (one_sub_ne_zero_of_norm_le_half V hV),
    div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  have hnum : ‖R*((1-qInv)+(1-V)*(W-D))-K*V‖ ≤
      ‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖ := by
    calc
      _ ≤ ‖R*((1-qInv)+(1-V)*(W-D))‖ + ‖K*V‖ := norm_sub_le _ _
      _ = ‖R‖ * ‖(1-qInv)+(1-V)*(W-D)‖ + ‖K‖*‖V‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖R‖ * (‖1-qInv‖ + ‖1-V‖*‖W-D‖) + ‖K‖*‖V‖ := by
        gcongr
        simpa only [norm_mul] using norm_add_le (1-qInv) ((1-V)*(W-D))
      _ ≤ ‖R‖ * (2 + (1+‖V‖)*(‖W‖+‖D‖)) + ‖K‖*‖V‖ := by
        gcongr
        · calc ‖1-qInv‖ ≤ ‖(1:ℂ)‖+‖qInv‖ := norm_sub_le _ _
               _ ≤ 2 := by simp only [norm_one]; linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) V
        · exact norm_sub_le W D
  have hv := inv_one_sub_norm_le_two V hV
  have hr := inv_one_sub_norm_le_two R hR
  calc
    _ ≤ (‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖) * (2*2) := by
      gcongr
    _ ≤ 12 * ‖R‖ * (1+‖W‖) + 4*‖K‖*‖V‖ := by
      have he : 2 + (1+‖V‖)*(‖W‖+‖D‖) ≤ 3*(1+‖W‖) := by
        have : (1+‖V‖)*(‖W‖+‖D‖) ≤ (3/2:ℝ)*(‖W‖+1/2) := by gcongr ; linarith
        nlinarith [norm_nonneg W]
      nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg R)]

theorem continuedCorrection_defect_bound (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring

end ProbeLocal
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss
local notation "O" => Eisenstein.O

def coordV (Q : ℝ) (z : ℂ) : ℂ := (Q : ℂ) ^ (-6*z)
def coordR (Q : ℝ) (A x z : ℂ) : ℂ := A * (Q : ℂ) ^ (4-6*x-6*z)
def coordW (Q : ℝ) (v w : ℂ) : ℂ := v * (Q : ℂ) ^ (-w)
def coordD (Q : ℝ) (eta v x : ℂ) : ℂ := eta * star v * (Q : ℂ) ^ (-x)
def coordK (Q : ℝ) (eta x w : ℂ) : ℂ := eta * (Q-1) * (Q : ℂ) ^ (-x-w)

def unramifiedClosed (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  ProbeLocal.continuedCorrection V W D (markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1)

def actualAPhase (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (CompletedGauss.angularFactor p) ^ 6 * HeckeFamily.elementCoeff eta p ^ 6

def actualUnramifiedClosed (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

lemma actualAPhase_norm_le_one (eta : HeckeFamily.Character) (p : O) :
    ‖actualAPhase eta p‖ ≤ 1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CubicEisenstein.norm_angularFactor_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (ProbeRow.targetMonoid_norm_le_one eta p))

lemma coordV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖coordV Q z‖ = Q ^ (-6*z.re) := by
  rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

lemma coordR_norm_le (Q : ℝ) (hQ : 0 < Q) (A x z : ℂ) (hA : ‖A‖ ≤ 1) :
    ‖coordR Q A x z‖ ≤ Q ^ (4-6*x.re-6*z.re) := by
  rw [coordR, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hA

lemma coordW_norm_le (Q : ℝ) (hQ : 0 < Q) (v w : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖coordW Q v w‖ ≤ Q ^ (-w.re) := by
  rw [coordW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hv

lemma coordD_norm_le (Q : ℝ) (hQ : 0 < Q) (eta v x : ℂ)
    (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖coordD Q eta v x‖ ≤ Q ^ (-x.re) := by
  rw [coordD, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hv

lemma coordK_norm_le (Q : ℝ) (hQ : 1 ≤ Q) (eta x w : ℂ) (he : ‖eta‖ ≤ 1) :
    ‖coordK Q eta x w‖ ≤ Q ^ (1-x.re-w.re) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsub : ‖(Q:ℂ)-1‖ = Q-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hQ)]
  rw [coordK, norm_mul, norm_mul, hsub, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have heq : (1-x.re-w.re) = 1 + (-x.re-w.re) := by ring
  rw [heq, Real.rpow_add hQ0, Real.rpow_one]
  simp only [Complex.sub_re, Complex.neg_re]
  gcongr
  calc ‖eta‖*(Q-1) ≤ 1*(Q-1) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hQ)
       _ ≤ Q := by linarith

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

lemma rpow_le_half (Q a : ℝ) (hQ : 4 ≤ Q) (ha : a ≤ -(1/2)) : Q^a ≤ 1/2 := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc
    Q^a ≤ Q^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by rw [← one_div, div_le_iff₀ hs]; nlinarith [Real.sqrt_nonneg Q]

/-- The local correction differs from one by a summable power of the prime norm. -/
theorem unramifiedClosed_second_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(363/200:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(99/100:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(56/25:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(19/20:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7/8:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(33/40:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(19/20:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(363/200:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(363/200:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

end ProbeEuler
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
