/-
Low Gram profiles adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.LowGaussColumns

/-!
# Low Gram profiles

Low Gram profiles, coefficients and zero modes; period prime lists and ideal rows; reflection
masks and the source bound of the low Gram zero mode.
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
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ cubic_units_finite

def lowElementRowPoint (m : O) : Oˣ×Id :=
  (lowRowLabelUnit m,Ideal.span {m})

def lowIdealRowElement (p : Oˣ×Id) : O := p.1.val*cubicIdealGenerator p.2

lemma lowIdealRowElement_point (m : O) : lowIdealRowElement (lowElementRowPoint m)=m :=
  (lowRowLabelUnit_spec m).symm

lemma lowElementRowPoint_injective : Function.Injective lowElementRowPoint :=
  Function.LeftInverse.injective lowIdealRowElement_point

lemma lowIdealRowElement_span (p : Oˣ×Id) : Ideal.span {lowIdealRowElement p}=p.2 := by
  rw [lowIdealRowElement,Ideal.span_singleton_mul_left_unit p.1.isUnit,span_cubicIdealGenerator]

lemma lowElementRowPoint_element (p : Oˣ×Id) (hp : p.2≠0) :
    lowElementRowPoint (lowIdealRowElement p)=p := by
  apply Prod.ext
  · apply Units.ext
    have hh := lowRowLabelUnit_spec (lowIdealRowElement p)
    rw [lowIdealRowElement_span] at hh
    exact (mul_right_cancel₀ (cubicIdealGenerator_ne_zero p.2 hp) hh).symm
  · exact lowIdealRowElement_span p

lemma lowIdealRowElement_norm (p : Oˣ×Id) :
    elementNorm (lowIdealRowElement p)=(Ideal.absNorm p.2:ℝ) := by
  unfold elementNorm
  rw [lowIdealRowElement_span]

def lowIdealRows (R : Finset O) : Finset Id := R.image (fun m=> Ideal.span {m})

lemma lowIdealRows_nonzero (R : Finset O) (hR : ∀m∈R,m≠0) (I : Id) (hI : I∈lowIdealRows R) : I≠0 := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact Ideal.span_singleton_eq_bot.not.mpr (hR m hm)

lemma lowIdealRows_norm_bound (R : Finset O) (Q : ℝ) (hR : ∀m∈R,elementNorm m≤ Q)
    (I : Id) (hI : I∈lowIdealRows R) : (Ideal.absNorm I:ℝ)≤ Q := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact hR m hm

theorem sum_low_element_rows (R : Finset O) (hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,F m)=∑u : Oˣ,∑I∈lowIdealRows R,
      if u.val*cubicIdealGenerator I∈R then F (u.val*cubicIdealGenerator I) else 0 := by
  let P := (Finset.univ×ˢlowIdealRows R).filter (fun p : Oˣ×Id=> lowIdealRowElement p∈R)
  have he : (∑m∈R,F m)=∑p∈P,F (lowIdealRowElement p) := by
    apply Finset.sum_bij (fun m hm=> lowElementRowPoint m)
    · intro m hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact Finset.mem_image.mpr ⟨m,hm,rfl⟩
      · rwa [lowIdealRowElement_point]
    · intro m hm n hn he
      exact lowElementRowPoint_injective he
    · intro p hp
      obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
      refine ⟨lowIdealRowElement p,hpr,?_⟩
      exact lowElementRowPoint_element p (lowIdealRows_nonzero R hR _ (Finset.mem_product.mp hp).2)
    · intro m hm
      rw [lowIdealRowElement_point]
  rw [he]
  dsimp only [P]
  rw [Finset.sum_filter,Finset.sum_product]
  rfl

theorem low_element_energy_le_units (R : Finset O) (_hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,‖F m‖^2)≤∑u : Oˣ,∑I∈lowIdealRows R,‖F (u.val*cubicIdealGenerator I)‖^2 := by
  let P : Finset (Oˣ×Id) := Finset.univ×ˢlowIdealRows R
  have hsub : R.image lowElementRowPoint⊆P := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨m,hm,rfl⟩⟩
  have he : (∑m∈R,‖F m‖^2)=∑p∈R.image lowElementRowPoint,‖F (lowIdealRowElement p)‖^2 := by
    rw [Finset.sum_image (fun m _ n _ h=> lowElementRowPoint_injective h)]
    simp only [lowIdealRowElement_point]
  rw [he]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _=> sq_nonneg ‖F (lowIdealRowElement p)‖)
  simpa only [P,Finset.sum_product,lowIdealRowElement] using hh

lemma low_rowTwist_label_one (Ψ : O→*ℂ) (m : O) (u : Oˣ) (I : Id) :
    CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*cubicIdealGenerator I)=
      CanonicalRowCompletion.rowTwist Ψ m (cubicIdealGenerator (1:Id))
        (((lowRowLabelUnit 1)^4*u).val*cubicIdealGenerator I) := by
  have he : (lowRowLabelUnit (1:O)).val*cubicIdealGenerator (1:Id)=1 := by
    simpa only [Ideal.span_singleton_one,Ideal.one_eq_top] using (lowRowLabelUnit_spec (1:O)).symm
  have harg : m^6*(cubicIdealGenerator (1:Id))^4*
      (((lowRowLabelUnit 1)^4*u).val*cubicIdealGenerator I)=m^6*1^4*(u.val*cubicIdealGenerator I) := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,one_pow]
    calc
      _=m^6*((lowRowLabelUnit (1:O)).val*cubicIdealGenerator (1:Id))^4*(u.val*cubicIdealGenerator I) := by ring
      _=_ := by rw [he];ring
  unfold CanonicalRowCompletion.rowTwist
  rw [harg]

lemma low_units_label_one_sum (F : (O→*ℂ)→ℝ) (Ψ : O→*ℂ) (m : O) (I : Id) :
    (∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*cubicIdealGenerator I)))=
      ∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m (cubicIdealGenerator (1:Id)) (u.val*cubicIdealGenerator I)) := by
  simp_rw [low_rowTwist_label_one]
  exact Equiv.sum_comp (Equiv.mulLeft ((lowRowLabelUnit (1:O))^4))
    (fun u : Oˣ=> F (CanonicalRowCompletion.rowTwist Ψ m (cubicIdealGenerator (1:Id)) (u.val*cubicIdealGenerator I)))

lemma low_element_rowTwist_energy (R : Finset O) (hR : ∀z∈R,z≠0)
    (Ψ : O→*ℂ) (m : O) (F : (O→*ℂ)→ℂ) :
    (∑z∈R,‖F (CanonicalRowCompletion.rowTwist Ψ m 1 z)‖^2)≤
      ∑u : Oˣ,∑I∈lowIdealRows R,
        ‖F (CanonicalRowCompletion.rowTwist Ψ m (cubicIdealGenerator (1:Id)) (u.val*cubicIdealGenerator I))‖^2 := by
  apply (low_element_energy_le_units R hR (fun z=> F (CanonicalRowCompletion.rowTwist Ψ m 1 z))).trans_eq
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun (u : Oˣ) (I : Id)=>
    ‖F (CanonicalRowCompletion.rowTwist Ψ m (cubicIdealGenerator (1:Id)) (u.val*cubicIdealGenerator I))‖^2)]
  apply Finset.sum_congr rfl
  intro I hI
  exact low_units_label_one_sum (fun Ψ=>‖F Ψ‖^2) Ψ m I

lemma lowNumeratorRows_nonzero (a b : ℝ) (ha : 0< a) (hb : 0< b) (Q : ℝ) (hQ : 0< Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : z≠0 := by
  intro he
  have hh := (lowNumeratorRows_mem a b ha hb Q hQ z).mp hz
  rw [he,elementNorm,Ideal.span_singleton_zero,Ideal.absNorm_bot,Nat.cast_zero,zero_div] at hh
  exact hh (lowOuterCutoff_small a b ha 0 (by positivity))

lemma lowNumeratorRows_norm_bound (a b : ℝ) (ha : 0< a) (hb : 0< b) (Q : ℝ) (hQ : 0< Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : elementNorm z≤2*b*Q := by
  have hh := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ z).mp hz)).2
  exact (div_le_iff₀ hQ).mp hh

theorem lowSelectedInverseRow_ideal_energy {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→ Id) (X t : ℝ) (σ : RayFourExpansion.RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow F c η S hS D X t σ z‖^2)≤
      lowCorrectionEnergy*∑χ : RayFourExpansion.RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
        ‖∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator (cubicIdealGenerator (1:Id)) (u.val*cubicIdealGenerator I))
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
          (fun A=> if D k∣A then (1:ℂ) else 0)‖^2 := by
  apply (lowSelectedInverseRow_energy F c η S hS D X t σ R).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (calibrationForSet S hS).generator (fun Ψ=>∑k∈F,c k*InverseMoment.markedCompletedT Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X (fun A=> if D k∣A then (1:ℂ) else 0))

lemma low_unit_card : Fintype.card Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using EisensteinLatticeCount.natCard_units_eq_six

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries
open CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma lowCalibrationGood_dvd (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator) : D.numeratorGood∣C.generator := by
  refine ⟨D.numeratorUnit.val*lambda^D.numeratorLambda*(2:O)^D.numeratorTwo,?_⟩
  have hh := D.numeratorFactor
  simp only [one_pow,one_mul] at hh
  change C.generator=D.numeratorUnit.val*lambda^D.numeratorLambda*(2:O)^D.numeratorTwo*D.numeratorGood at hh
  exact hh.trans (by ring)

theorem lowBaseModulus_coprime (η : HeckeFamily.Character) (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator)
    (hLam : lambda∣C.generator) (h2 : (2:O)∣C.generator)
    (n : O) (hcn : IsCoprime C.generator n) (hη : HeckeFamily.elementCoeff η n≠0) :
    IsCoprime (Ideal.span {n}) (lowBaseModulus η C C.generator D*Ideal.span {(72:O)}) := by
  have heta : IsCoprime (Ideal.span {n}) η.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hη)
  have hcal : IsCoprime (Ideal.span {n}) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hcn.symm
  have hgood : IsCoprime (Ideal.span {n}) (Ideal.span {D.numeratorGood}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (hcn.of_isCoprime_of_dvd_left (lowCalibrationGood_dvd C D)).symm
  have htwo : IsCoprime n (2:O) := (hcn.of_isCoprime_of_dvd_left h2).symm
  have hs := supported_of_coprime_bad C.generator n hLam h2 hcn
  have hnine := (CanonicalRowCompletion.nine_coprime_of_not_lambda_dvd n
    ((_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.supported_span_iff n).mp hs).1).symm
  have hseventy : IsCoprime n (72:O) := by
    convert (htwo.pow_right : IsCoprime n ((2:O)^3)).mul_right hnine using 1 ;norm_num
  have h72 : IsCoprime (Ideal.span {n}) (Ideal.span {(72:O)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hseventy
  have h4 : IsCoprime (Ideal.span {n}) (Ideal.span {(4:O)}) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    convert htwo.pow_right (n:=2) using 1 ;norm_num
  unfold lowBaseModulus calibrationRowModulus
  exact (heta.mul_right (hcal.mul_right
    (((isCoprime_one_right).mul_right hcal).mul_right h72 |>.mul_right hgood))).mul_right h4 |>.mul_right h72

theorem lowSingleSlotWeight_zero_of_period (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (P t : ℝ) (n : O) (hcn : IsCoprime (calibrationForSet S hS).generator n)
    (hperiod : ¬IsCoprime (Ideal.span {n})
      (lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
        (calibrationLowData S hS)*Ideal.span {(72:O)})) :
    lowSingleSlotWeight η W P t n=0 := by
  have heta : HeckeFamily.elementCoeff η n=0 := by
    by_contra hh
    exact hperiod (lowBaseModulus_coprime η _ _ (calibration_generator_bad S hS hbad).1
      (calibration_generator_bad S hS hbad).2 n hcn hh)
  simp [lowSingleSlotWeight,heta]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma sum_tuple_filter_zero {ι α : Type*} [Fintype ι] [DecidableEq α]
    (T : ι→ Finset α) (good : ι→α→ Prop) [∀i,DecidablePred (good i)]
    (c : ι→α→ℂ) (hc : ∀i a,a∈T i→¬good i a→ c i a=0) (F : (ι→α)→ℂ) :
    (∑p : ∀i,T i,(∏i,c i (p i).val)*F (fun i=>(p i).val))=
      ∑p : ∀i,(T i).filter (good i),(∏i,c i (p i).val)*F (fun i=>(p i).val) := by
  let forget : (∀i,(T i).filter (good i))→(∀i,T i) := fun p i=>⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩
  have hinj : Function.Injective forget := by
    intro p q h
    funext i
    exact Subtype.ext (congrArg (fun a=> (a i).val) h)
  let H : (∀i,T i)→ℂ := fun p=>(∏i,c i (p i).val)*F (fun i=>(p i).val)
  have hz (p : ∀i,T i) (hp : p∉Finset.univ.image forget) : H p=0 := by
    by_contra hh
    have hn : ∀i,good i (p i).val := by
      intro i
      by_contra hbad
      have hc0 := hc i (p i).val (p i).property hbad
      have hprod : (∏j,c j (p j).val)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hc0
      exact hh (by dsimp [H];rw [hprod,zero_mul])
    let q : ∀i,(T i).filter (good i) := fun i=>⟨(p i).val,Finset.mem_filter.mpr ⟨(p i).property,hn i⟩⟩
    exact hp (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩)
  have he := Finset.sum_subset (Finset.subset_univ (Finset.univ.image forget))
    (fun p hp hnot=> hz p hnot)
  change (∑p,H p)=_
  rw [←he,Finset.sum_image (fun p _ q _ h=> hinj h)]

def lowPeriodIdeal (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS)*Ideal.span {(72:O)}

def lowPeriodSlotFilter {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→ Finset O) : ι→ Finset O :=
  fun i=>(T i).filter (fun a=> IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS))

lemma lowPeriodSlotFilter_coprime {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→ Finset O) (i : ι) (a : O)
    (ha : a∈lowPeriodSlotFilter η S hS T i) :
    IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS) := (Finset.mem_filter.mp ha).2

lemma canonical_prime_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (P : PrimeIdeal) (hP : _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported P.val) (hout : P.val∉S) :
    IsCoprime (calibrationForSet S hS).generator (primaryIdealGenerator P.val) := by
  apply calibrationForSet_coprime_of_excluded S hS
  intro Q hQ hdiv
  rw [CenteredMomentSourceRow.primary_span_supported P.val hP] at hdiv
  have hpmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have he : P.val=Q := Ideal.IsMaximal.eq_of_le hpmax (hS Q hQ).ne_top (Ideal.dvd_iff_le.mp hdiv)
  exact hout (he.symm ▸ hQ)

lemma canonical_slot_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (T : Finset PrimeIdeal)
    (hT : ∀P∈T,_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported P.val) (hout : ∀P∈T,P.val∉S)
    (a : O) (ha : a∈canonicalSlotSupport T) : IsCoprime (calibrationForSet S hS).generator a := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact canonical_prime_calibration_coprime S hS P (hT P hP) (hout P hP)

theorem low_slot_polynomial_period_filter {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (T : ι→ Finset O)
    (hcop : ∀i a,a∈T i→ IsCoprime (calibrationForSet S hS).generator a)
    (W : ι→ℝ→ℂ) (P : ι→ℝ) (t : ℝ) (F : (ι→ O)→ℂ) :
    (∑p : ∀i,T i,(∏i,lowSingleSlotWeight η (W i) (P i) t (p i).val)*F (fun i=>(p i).val))=
      ∑p : ∀i,lowPeriodSlotFilter η S hS T i,
        (∏i,lowSingleSlotWeight η (W i) (P i) t (p i).val)*F (fun i=>(p i).val) := by
  apply sum_tuple_filter_zero T (fun i a=> IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS))
    (fun i a=> lowSingleSlotWeight η (W i) (P i) t a) _ F
  intro i a ha hnot
  exact lowSingleSlotWeight_zero_of_period η S hS hbad (W i) (P i) t a (hcop i a ha) hnot

def lowPeriodPrimeList (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) : Finset PrimeIdeal :=
  T.filter (fun P=> IsCoprime P.val (lowPeriodIdeal η S hS))

lemma lowPeriodPrimeList_subset (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) :
    lowPeriodPrimeList η S hS T⊆T := Finset.filter_subset _ _

lemma lowPeriodPrimeList_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal)
    (P : PrimeIdeal) (hP : P∈lowPeriodPrimeList η S hS T) :
    IsCoprime P.val (lowPeriodIdeal η S hS) := (Finset.mem_filter.mp hP).2

lemma lowPeriodPrimeList_disjoint {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→ Finset PrimeIdeal)
    (hT : Pairwise (fun i j=> Disjoint (T i) (T j))) :
    Pairwise (fun i j=> Disjoint (lowPeriodPrimeList η S hS (T i)) (lowPeriodPrimeList η S hS (T j))) := by
  intro i j hij
  exact (hT hij).mono (lowPeriodPrimeList_subset η S hS _) (lowPeriodPrimeList_subset η S hS _)

theorem low_canonical_polynomial_period_filter {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (T : ι→ Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→ _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.Supported P.val)
    (hout : ∀i P,P∈T i→ P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→ PrimeIdeal)→ℂ) :
    (∑p : ∀i,T i,(∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryIdealGenerator (p i).val.val))*F (fun i=>(p i).val))=
      ∑p : ∀i,lowPeriodPrimeList η S hS (T i),
        (∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryIdealGenerator (p i).val.val))*F (fun i=>(p i).val) := by
  apply sum_tuple_filter_zero T (fun i P=> IsCoprime P.val (lowPeriodIdeal η S hS))
    (fun i P=> lowSingleSlotWeight η (W i) (Y i) t (primaryIdealGenerator P.val)) _ F
  intro i P hP hnot
  apply lowSingleSlotWeight_zero_of_period η S hS hbad (W i) (Y i) t _
    (canonical_prime_calibration_coprime S hS P (hT i P hP) (hout i P hP))
  change ¬IsCoprime (Ideal.span {primaryIdealGenerator P.val}) (lowPeriodIdeal η S hS)
  rwa [CenteredMomentSourceRow.primary_span_supported P.val (hT i P hP)]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries
open CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss RayFourExpansion SecondPassArithmetic
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma physicalRayPeriodicBase_support (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : physicalRayPeriodicBase η S hS σ χ n≠0) :
    IsCoprime (Ideal.span {n}) (lowPeriodIdeal η S hS) := by
  let C := calibrationForSet S hS
  let D := calibrationLowData S hS
  change ((rayMonoid χ n*HeckeFamily.elementCoeff η n)*
    star (C.residueMonoid n*CanonicalRowCompletion.actualPeriodicRow 1 C.generator
      D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n))*
      _≠0 at hn
  have ha := left_ne_zero_of_mul hn
  have heta := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hres := left_ne_zero_of_mul (star_ne_zero.mp (right_ne_zero_of_mul ha))
  have hc : IsCoprime C.generator n := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    exact ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
      (C.residue.apply_ne_zero_iff.mp hres)).symm
  exact lowBaseModulus_coprime η C D (calibration_generator_bad S hS hbad).1
    (calibration_generator_bad S hS hbad).2 n hc heta

def lowTruePeriodGenerator (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O := cubicIdealGenerator (lowPeriodIdeal η S hS)

lemma lowPeriodIdeal_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS≠0 := by
  unfold lowPeriodIdeal
  apply mul_ne_zero
  · exact lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowTruePeriodGenerator_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowTruePeriodGenerator η S hS≠0 :=
  cubicIdealGenerator_ne_zero _ (lowPeriodIdeal_ne_zero η S hS)

lemma lowTruePeriodGenerator_span (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Ideal.span {lowTruePeriodGenerator η S hS}=lowPeriodIdeal η S hS :=
  span_cubicIdealGenerator _

lemma physicalRayPeriodicBase_zero_true_puncture (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : ¬IsCoprime (lowTruePeriodGenerator η S hS) n) :
    physicalRayPeriodicBase η S hS σ χ n=0 := by
  by_contra hh
  apply hn
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [lowTruePeriodGenerator_span]
  exact (physicalRayPeriodicBase_support η S hS hbad σ χ n hh).symm

theorem physical_row_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) :
    rowTwist (physicalRayPeriodicBase η S hS σ χ)
      ((calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS) f z=
    rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z := by
  exact InverseReflectedPhase.rowTwist_absorb_puncture _ _ _ f z
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2
    (physicalRayPeriodicBase_zero_true_puncture η S hS hbad σ χ)

lemma physical_true_period_residual_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (I F : Id) :
    IsCoprime (lowPeriodIdeal η S hS)
      (rowResidualPart I
        (Ideal.span {(calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS}*F)) := by
  apply InverseReflectedPhase.rowResidualPart_coprime_enlarged_period
  rw [lowTruePeriodGenerator_span]

def lowReflectionPeriod (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS)

lemma lowReflectionPeriod_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionPeriod η S hS≠0 :=
  lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _

lemma lowReflectionPeriod_actual (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (lowReflectionPeriod η S hS) (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

def lowReflectionMask (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O :=
  (calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS

lemma lowReflectionMask_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionMask η S hS≠0 :=
  mul_ne_zero (calibrationForSet S hS).generator_ne_zero (lowTruePeriodGenerator_ne_zero η S hS)

lemma lowReflectionMask_bad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    lambda∣lowReflectionMask η S hS ∧ (2:O)∣lowReflectionMask η S hS := by
  exact ⟨dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).1 _,
    dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).2 _⟩

lemma lowReflectionMask_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS∣Ideal.span {lowReflectionMask η S hS} := by
  rw [lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,lowTruePeriodGenerator_span]
  exact dvd_mul_left _ _

lemma physical_markedCompletedT_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) (W : ℝ→ℂ) (X : ℝ) (mark : Id→ℂ) :
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) f z) W X mark=
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z) W X mark := by
  rw [lowReflectionMask,physical_row_absorb_true_period η S hS hbad σ χ]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries
open CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def lowPrimeIdealList (T : Finset PrimeIdeal) : Finset Id := T.image Subtype.val

def lowPrimeListEquiv (T : Finset PrimeIdeal) : T≃lowPrimeIdealList T :=
  Equiv.ofBijective (fun p=>⟨p.val.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩) (by
    constructor
    · intro p q h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : lowPrimeIdealList T=> x.val) h))
    · intro I
      obtain ⟨P,hP,h⟩ := Finset.mem_image.mp I.property
      exact ⟨⟨P,hP⟩,Subtype.ext h⟩)

@[simp] lemma lowPrimeListEquiv_val (T : Finset PrimeIdeal) (p : T) :
    (lowPrimeListEquiv T p).val=p.val.val := rfl

lemma lowPrimeIdealList_prime (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : Prime I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact P.property

lemma lowPrimeIdealList_supported (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) : Supported I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

lemma lowPrimeIdealList_maximal (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : I.IsMaximal :=
  (Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI)).isMaximal (lowPrimeIdealList_prime T I hI).ne_zero

lemma lowPrimeIdealList_good_odd (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) :
    lambda∉I ∧ ringChar (O⧸I)≠2 := by
  have hs := lowPrimeIdealList_supported T hT I hI
  exact hs.2 I ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI),le_rfl⟩)

lemma lowPrimeIdealList_disjoint {ι : Type*} (T : ι→ Finset PrimeIdeal)
    (hT : Pairwise (fun i j=> Disjoint (T i) (T j))) :
    Pairwise (fun i j=> Disjoint (lowPrimeIdealList (T i)) (lowPrimeIdealList (T j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro I hI hJ
  obtain ⟨P,hP,hPI⟩ := Finset.mem_image.mp hI
  obtain ⟨Q,hQ,hQI⟩ := Finset.mem_image.mp hJ
  have he : P=Q := Subtype.ext (hPI.trans hQI.symm)
  exact Finset.disjoint_left.mp (hT hij) hP (he.symm ▸ hQ)

lemma lowPrimeIdealList_norm (T : Finset PrimeIdeal) (H : ℝ)
    (hT : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤ H) (I : Id) (hI : I∈lowPrimeIdealList T) :
    (Ideal.absNorm I:ℝ)≤ H := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

lemma lowPrimeIdealList_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal)
    (I : Id) (hI : I∈lowPrimeIdealList (lowPeriodPrimeList η S hS T)) :
    IsCoprime I (lowPeriodIdeal η S hS) := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact lowPeriodPrimeList_coprime η S hS T P hP

theorem low_actual_ideal_polynomial {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (T : ι→ Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→ Supported P.val) (hout : ∀i P,P∈T i→ P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→ Id)→ℂ) :
    (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (p i).val)*F (fun i=> Ideal.span {(p i).val}))=
    ∑p : ∀i,lowPrimeIdealList (lowPeriodPrimeList η S hS (T i)),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryIdealGenerator (p i).val))*F (fun i=>(p i).val) := by
  let E := Equiv.piCongrRight (fun i=> canonicalSlotEquiv (T i) (hT i))
  rw [←Equiv.sum_comp E]
  simp only [E,Equiv.piCongrRight_apply,Pi.map_apply,canonicalSlotEquiv_val]
  have hspan (p : ∀i,T i) (i : ι) : Ideal.span {primaryIdealGenerator (p i).val.val}=(p i).val.val :=
    CenteredMomentSourceRow.primary_span_supported _ (hT i _ (p i).property)
  simp_rw [hspan]
  rw [low_canonical_polynomial_period_filter η S hS hbad T hT hout W Y t (fun p=> F (fun i=>(p i).val))]
  exact Equiv.sum_comp (Equiv.piCongrRight (fun i=> lowPrimeListEquiv (lowPeriodPrimeList η S hS (T i))))
    (fun p=>(∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryIdealGenerator (p i).val))*F (fun i=>(p i).val))

lemma low_actual_ideal_weight_bound (η : HeckeFamily.Character) (W : ℝ→ℂ)
    (hW : ∀x,‖W x‖≤1) (Y t : ℝ) (I : Id) :
    ‖lowSingleSlotWeight η W Y t (primaryIdealGenerator I)‖≤1 :=
  (lowSingleSlotWeight_norm η W Y t _).trans (hW _)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def lowGramCoefficient (C : CalibrationData) (σ : RayRing)
    (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then lowArithmeticCoefficient C s else 0

/-- Mellin profile after extracting the square-root Gauss normalization. -/
def lowGramProfile (W1 : ℝ→ℂ) (v r : ℝ) : ℂ :=
  W1 r*(r:ℂ)^(-1+(v:ℂ)*Complex.I)

def lowGramScale (Y : ℝ) : ℂ := (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹

lemma lowGramCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (s : {I : Id // Supported I}) :
    ‖lowGramCoefficient (calibrationForSet S hS) σ s‖≤1 := by
  unfold lowGramCoefficient
  split_ifs
  · exact lowArithmeticCoefficient_source_norm S hS s
  · simp

lemma lowGramProfile_norm (W1 : ℝ→ℂ) (v r : ℝ) (hr : 0< r) :
    ‖lowGramProfile W1 v r‖=‖W1 r‖/r := by
  rw [lowGramProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [Complex.add_re,Complex.neg_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,
    Real.rpow_neg_one,div_eq_mul_inv]

lemma lowGramScale_cpow (Y : ℝ) (hY : 0< Y) : lowGramScale Y=(Y:ℂ)^(-(3/2:ℂ)) := by
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [show -(3/2:ℂ)=(-1)+(-(1/2:ℂ)) by norm_num,Complex.cpow_add _ _ hy,
    Complex.cpow_neg_one,←CenteredMomentDetectorDictionary.sqrt_inverse_cpow Y hY]
  rfl

lemma lowGramScale_mul_star (Y : ℝ) (hY : 0< Y) :
    lowGramScale Y*star (lowGramScale Y)=((Y^3:ℝ):ℂ)⁻¹ := by
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hs : (Real.sqrt Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hY).ne'
  have hsquare : (Real.sqrt Y:ℂ)^2=(Y:ℂ) := by exact_mod_cast Real.sq_sqrt hY.le
  simp only [lowGramScale,map_mul,map_inv₀,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow]
  field_simp
  ring_nf
  rw [hsquare]

theorem lowGaussColumn_unnormalized (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)=
      lowGramScale Y*(lowGramCoefficient C σ s*
        lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y)) := by
  have hq : (0:ℝ)< Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hr : 0<(Ideal.absNorm s.val:ℝ)/Y := div_pos hq hY
  have hrc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsqrt : Real.sqrt (Ideal.absNorm s.val:ℝ)=
      Real.sqrt Y*Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y) := by
    rw [←Real.sqrt_mul hY.le,mul_div_cancel₀ _ hY.ne']
  have hp : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
      (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹=
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-1+(v:ℂ)*Complex.I) := by
    rw [CenteredMomentDetectorDictionary.sqrt_inverse_cpow _ hr,←Complex.cpow_add _ _ hrc]
    congr 1
    ring
  unfold lowGaussColumn lowGramCoefficient
  split_ifs
  · rw [hsqrt,Complex.ofReal_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    calc
      _ = (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹*(lowArithmeticCoefficient C s*W1 ((Ideal.absNorm s.val:ℝ)/Y))*
        ((((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹) := by ring_nf
      _ = _ := by rw [hp];unfold lowGramScale lowGramProfile;ring_nf
  · simp

theorem lowRayAmplitude_unnormalized (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v : ℝ) (m : O) :
    lowRayAmplitude C W1 Y σ m v=lowGramScale Y*
      ∑s∈lowGaussColumns W1 hW1 Y hY,
        lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y)*
          sexticGauss (primaryIdealGenerator s.val) (supported_primaryIdealGenerator_ne_zero s.val s.property) (-m) := by
  rw [lowRayAmplitude_source_columns C W1 hW1 Y hY σ v]
  unfold gaussPolynomial gaussRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he := congrArg Ideal.absNorm ((primaryIdealGenerator_spec s.val (supported_primaryIdealGenerator_ne_zero s.val s.property)).1)
  rw [he]
  calc
    _ = (lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
      sexticGauss (primaryIdealGenerator s.val) (supported_primaryIdealGenerator_ne_zero s.val s.property) (-m) := by ring
    _ = _ := by rw [lowGaussColumn_unnormalized C W1 Y hY σ v s];ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation SchwartzPlanePoisson 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma lowGram_pair_prefactor (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v Q : ℝ) (s t : {I : Id // Supported I}) :
    (lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
      ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)))=
      ((Q/Y^3:ℝ):ℂ)*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
  calc
    _ = (Q:ℂ)*(lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
        star (lowGaussColumn C W1 Y σ v t/(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)) := by
      simp only [Complex.star_def,map_mul,map_inv₀,Complex.conj_ofReal,div_eq_mul_inv,mul_inv_rev]
      ring
    _ = (Q:ℂ)*(lowGramScale Y*star (lowGramScale Y))*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
      rw [lowGaussColumn_unnormalized C W1 Y hY σ v s,lowGaussColumn_unnormalized C W1 Y hY σ v t]
      simp only [star_mul]
      ring
    _ = _ := by rw [lowGramScale_mul_star Y hY];simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]

theorem lowGram_source_poisson (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v : ℝ)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0< Q) :
    gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=> primaryIdealGenerator s.val)
      (fun s=>(supported_span_primaryIdealGenerator_iff s.val).mpr s.property)
      (lowGaussColumn C W1 Y σ v) U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          ∑'h : O,actualCorrelation (primaryIdealGenerator s.val) (primaryIdealGenerator t.val)
            ((supported_span_primaryIdealGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryIdealGenerator_iff t.val).mpr t.property) (-h)*
            paperRadialFourier U (Q*‖ringComplex h‖^2/‖ringComplex (primaryIdealGenerator s.val*primaryIdealGenerator t.val)‖^2) := by
  rw [gaussEnergy_poisson _ _ _ _ U Q hQ]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryIdealGenerator_spec s.val (supported_primaryIdealGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryIdealGenerator_spec t.val (supported_primaryIdealGenerator_ne_zero t.val t.property)).1)
  rw [hes,het,←mul_assoc,lowGram_pair_prefactor C W1 Y hY σ v Q s t,mul_assoc]

theorem lowGram_kernel_scale (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q)
    (s t : {I : Id // Supported I}) (h : O) :
    Q*‖ringComplex h‖^2/‖ringComplex (primaryIdealGenerator s.val*primaryIdealGenerator t.val)‖^2=
      ‖ringComplex h‖^2/((Y^2/Q)*((Ideal.absNorm s.val:ℝ)/Y)*((Ideal.absNorm t.val:ℝ)/Y)) := by
  simp_rw [ringComplex_norm_sq_eq_absNorm_span]
  rw [←Ideal.span_singleton_mul_span_singleton]
  rw [(primaryIdealGenerator_spec s.val (supported_primaryIdealGenerator_ne_zero s.val s.property)).1,
    (primaryIdealGenerator_spec t.val (supported_primaryIdealGenerator_ne_zero t.val t.property)).1,map_mul,Nat.cast_mul]
  field_simp

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open  ProbeRow CanonicalRowCompletion _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def gramPeriodicMonoid (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  ProbeRow.conjugateMonoid C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma gramPeriodicMonoid_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) : ‖gramPeriodicMonoid C B D n‖≤1 := by
  rw [gramPeriodicMonoid,MonoidHom.mul_apply,norm_mul]
  change ‖star (C.residueMonoid n)‖*_≤1
  rw [norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one n)).trans (actualPeriodicRow_norm 1 (fun _=> by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported n)

lemma gramPeriodicMonoid_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (gramPeriodicMonoid C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=> rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change star (C.residueMonoid x)*_=star (C.residueMonoid y)*_
  congr 1
  · apply congrArg star
    apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_right hxy)
  · exact hp x y (Ideal.mul_le_left hxy)

lemma gramPeriodicMonoid_zero (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) (hn : ¬IsCoprime B n) :
    gramPeriodicMonoid C B D n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [if_neg hn]
  change star (C.residueMonoid n)*
    ((((1:O→*ℂ) n*coprimalityMask B n)*
      numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
      movingNumeratorRow D.numeratorGood D.numeratorSupported n)=0
  rw [hm]
  simp

lemma gramPeriodicMonoid_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : lambda∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : lambda^2∣n-1) (hc : IsCoprime B n) :
    gramPeriodicMonoid C B D n=(C.residueMonoid n)⁻¹*idealRowHom C.generator (Ideal.span {n}) := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ ((supported_iff_native _).mp hn)] at he
  have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [if_pos hc]
  simp only [MonoidHom.one_apply,hm,one_mul,one_pow] at he
  change star (C.residueMonoid n)*_=_
  rw [←he]
  congr 1
  let := finiteEisensteinQuotientOfNonzero C.generator_ne_zero
  let : Fintype (O⧸Ideal.span {C.generator}) := Fintype.ofFinite _
  change star (C.residue (Ideal.Quotient.mk _ n))=(C.residue (Ideal.Quotient.mk _ n))⁻¹
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']

theorem lowArithmeticCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (s : {I : Id // Supported I}) :
    lowArithmeticCoefficient (calibrationForSet S hS) s=
      (calibrationForSet S hS).tau⁻¹*
        gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
          (calibrationLowData S hS) (primaryIdealGenerator s.val) := by
  let C := calibrationForSet S hS
  have hn := supported_primaryIdealGenerator_ne_zero s.val s.property
  have he := (primaryIdealGenerator_spec s.val hn).1
  have hp := (primaryIdealGenerator_spec s.val hn).2
  have hsupp := (supported_span_primaryIdealGenerator_iff s.val).mpr s.property
  have hb := calibration_generator_bad S hS hbad
  by_cases hc : IsCoprime C.generator (primaryIdealGenerator s.val)
  · have hguard : ∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact (calibration_coprime_iff_excluded_span S hS _).mp hc
    rw [lowArithmeticCoefficient,if_pos hguard,
      gramPeriodicMonoid_primary C C.generator (calibrationLowData S hS) hb.1 hb.2 _ hsupp hp hc,he]
    ring
  · have hguard : ¬∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact fun h=> hc ((calibration_coprime_iff_excluded_span S hS _).mpr h)
    rw [lowArithmeticCoefficient,if_neg hguard,gramPeriodicMonoid_zero C C.generator (calibrationLowData S hS) _ hc,mul_zero]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff SchwartzMap Topology
open Filter Set CompletedHeight JointLogSeparation
namespace ProbePhysical

def lowGramBaseWindow (W : ℝ→ℂ) (r : ℝ) : ℂ := W r/(r:ℂ)

lemma lowGramBaseWindow_support (W : ℝ→ℂ) :
    Function.support (lowGramBaseWindow W)⊆Function.support W := by
  intro r hr hz
  exact hr (by simp [lowGramBaseWindow,hz])

lemma lowGramBaseWindow_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (lowGramBaseWindow W) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r=0
  · subst r
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ=>(0:ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ha] with x hx
    have hz : W x=0 := by
      by_contra h
      exact (not_le.mpr hx) (hs h).1
    simp [lowGramBaseWindow,hz]
  · unfold lowGramBaseWindow
    simp only [div_eq_mul_inv]
    exact hW.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.fun_inv (Complex.ofReal_ne_zero.mpr hr))

lemma lowGramProfile_twist (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (v r : ℝ) :
    lowGramProfile W v r=normTwistedSource (lowGramBaseWindow W) (v/(2*Real.pi)) r := by
  by_cases hz : W r=0
  · simp [lowGramProfile,normTwistedSource,lowGramBaseWindow,hz]
  have hr : 0< r := ha.trans_le (hs hz).1
  have hrc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : (r:ℂ)^((v:ℂ)*Complex.I)=kernelLogPhase (v/(2*Real.pi)) (Real.log r) := by
    rw [Complex.cpow_def_of_ne_zero hrc,←Complex.ofReal_log hr.le]
    unfold kernelLogPhase
    congr 1
    push_cast
    field_simp
  rw [lowGramProfile,Complex.cpow_add _ _ hrc,Complex.cpow_neg_one,hp]
  unfold normTwistedSource lowGramBaseWindow
  ring

def lowGramSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) : SchwartzMap ℝ ℂ :=
  uniformTwistedSchwartz (lowGramBaseWindow W) a b ha
    ((lowGramBaseWindow_support W).trans hs) (lowGramBaseWindow_smooth W a b ha hs hW) (v/(2*Real.pi))

lemma lowGramSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v r : ℝ) :
    lowGramSchwartz W a b ha hs hW v r=lowGramProfile W v r := by
  rw [lowGramSchwartz,uniformTwistedSchwartz_apply,lowGramProfile_twist W a b ha hs]

theorem lowGramProfile_uniform_degree (a b : ℝ) (ha : 0< a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W⊆Set.Icc a b,∀hW : ContDiff ℝ ∞ W,
      ∃C : ℝ,0< C ∧ ∀v : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (lowGramSchwartz W a b ha hs hW v)≤ C*(1+‖v‖)^n := by
  obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha S
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn (lowGramBaseWindow W) ((lowGramBaseWindow_support W).trans hs)
    (lowGramBaseWindow_smooth W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro v
  apply (hb (v/(2*Real.pi))).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  gcongr
  simp only [norm_div,Real.norm_eq_abs,abs_of_pos (show (0:ℝ)<2*Real.pi by positivity)]
  exact div_le_self (norm_nonneg v) (by linarith [Real.pi_gt_three])

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def gramFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  (Ideal.span {(calibrationForSet S hS).generator}*
    calibrationRowModulus (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS))*
      Ideal.span {(4:O)}

lemma gramFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : gramFixedModulus S hS≠0 := by
  unfold gramFixedModulus
  apply mul_ne_zero
  · exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (calibrationForSet S hS).generator_ne_zero)
      (calibrationRowModulus_ne_zero _ _ (calibrationForSet S hS).generator_ne_zero _)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

def gramCoefficientExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if physicalRay n=σ then (calibrationForSet S hS).tau⁻¹*
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS) n
  else 0

lemma gramCoefficientExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖gramCoefficientExtension S hS σ n‖≤1 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [norm_mul,norm_inv,calibrationForSet_tau_norm,inv_one,one_mul]
    exact gramPeriodicMonoid_norm _ _ _ _
  · simp

lemma gramCoefficientExtension_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O)
    (hn : ¬IsCoprime (calibrationForSet S hS).generator n) : gramCoefficientExtension S hS σ n=0 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [gramPeriodicMonoid_zero _ _ _ _ hn,mul_zero]
  · rfl

theorem lowGramCoefficient_eq_extension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      gramCoefficientExtension S hS σ (primaryIdealGenerator s.val) := by
  unfold lowGramCoefficient gramCoefficientExtension
  change (if physicalRay (primaryIdealGenerator s.val)=σ then _ else 0)=_
  rw [lowArithmeticCoefficient_periodic S hS hbad s]

theorem gramCoefficientExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ x=gramCoefficientExtension S hS σ y := by
  have hr : physicalRay x=physicalRay y := Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  have hm := gramPeriodicMonoid_periodic (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) x y (Ideal.mul_le_right hxy)
  simp only [gramCoefficientExtension,hr,hm]

lemma gramCoefficientExtension_scaled_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (d x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ (d*x)=gramCoefficientExtension S hS σ (d*y) := by
  apply gramCoefficientExtension_periodic
  rw [←mul_sub]
  exact (gramFixedModulus S hS).mul_mem_left d hxy

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace ProbePhysical
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSecondDiagonal SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def lowGramZeroMode (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) : ℂ :=
  (Q:ℂ)*paperRadialFourier U 0*
    secondZeroEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=> primaryIdealGenerator s.val)
      (fun s=>(supported_span_primaryIdealGenerator_iff s.val).mpr s.property) (lowGaussColumn C W1 Y σ v)

lemma lowGramZeroMode_eq_source (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    lowGramZeroMode C W1 hW1 Y hY σ v U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          actualCorrelation (primaryIdealGenerator s.val) (primaryIdealGenerator t.val)
            ((supported_span_primaryIdealGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryIdealGenerator_iff t.val).mpr t.property) 0*paperRadialFourier U 0 := by
  unfold lowGramZeroMode secondZeroEnergy
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryIdealGenerator_spec s.val (supported_primaryIdealGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryIdealGenerator_spec t.val (supported_primaryIdealGenerator_ne_zero t.val t.property)).1)
  rw [hes,het]
  calc
    _ = ((lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
        ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ))))*
        actualCorrelation (primaryIdealGenerator s.val) (primaryIdealGenerator t.val) _ _ 0*paperRadialFourier U 0 := by ring
    _ = _ := by rw [lowGram_pair_prefactor C W1 Y hY σ v Q s t];ring

lemma lowGramZeroMode_bound (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0≤ Q) :
    ‖lowGramZeroMode C W1 hW1 Y hY σ v U Q‖≤
      Q*‖paperRadialFourier U 0‖*∑s∈lowGaussColumns W1 hW1 Y hY,‖lowGaussColumn C W1 Y σ v s‖^2 := by
  rw [lowGramZeroMode,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply secondZeroEnergy_bound
  · intro s
    exact (primaryIdealGenerator_spec s.val (supported_primaryIdealGenerator_ne_zero s.val s.property)).2
  · intro s hs t ht h
    apply Subtype.ext
    have hes := (primaryIdealGenerator_spec s.val (supported_primaryIdealGenerator_ne_zero s.val s.property)).1
    have het := (primaryIdealGenerator_spec t.val (supported_primaryIdealGenerator_ne_zero t.val t.property)).1
    rw [←hes,←het]
    exact congrArg (fun z : O=> Ideal.span {z}) h

theorem lowGramZeroMode_source_bound (a b B : ℝ) (ha : 0< a) (hB : 0≤ B) :
    ∃C : ℝ,0< C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b→(∀x,‖W1 x‖≤ B)→
      ∀Y : ℝ,∀hY : 1≤ Y,∀σ : RayRing,∀v : ℝ,∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0≤ Q→
      ‖lowGramZeroMode (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q‖≤
        C*‖paperRadialFourier U 0‖*Q/Y := by
  obtain ⟨C,hC,hb⟩ := lowGaussColumn_l2_bound a b B ha hB
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hWS hWB Y hY σ v U Q hQ
  apply (lowGramZeroMode_bound (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q hQ).trans
  calc
    _ ≤ Q*‖paperRadialFourier U 0‖*(C/Y) := by
      exact mul_le_mul_of_nonneg_left (hb S hS W1 hW1 hWS hWB Y hY σ v) (by positivity)
    _ = _ := by ring

end ProbePhysical
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
