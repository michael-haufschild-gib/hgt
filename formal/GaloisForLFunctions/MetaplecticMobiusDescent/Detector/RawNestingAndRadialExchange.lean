/-
Raw nesting and radial exchange adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SourceMellinWeights

/-!
# Raw nesting and radial exchange

Indexed compensated high sums, source outer indices and radial Mellin spectral terms; raw
arithmetic and source row series; the compensated physical probe as a sum of row triple
integrals.
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
open MeasureTheory
namespace ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : Countable (Ideal O) := CubicEisenstein.cubicIdealGenerator_injective.countable

abbrev SourceOuter (S : Finset (Ideal O)) := {K : Ideal O // Supported K ∧ ∀P∈S,¬P∣K}
abbrev CompletedPair := Ideal O×Ideal O

def sourceRawGrouping (S : Finset (Ideal O)) :
    SourceRawIndex S ≃ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toFun i := (⟨i.val.2.2,i.property⟩,(i.val.2.1,i.val.1))
  invFun i := ⟨(i.2.2,(i.2.1,i.1.val)),i.1.property⟩
  left_inv _i := rfl
  right_inv _i := rfl

def sourceRawGroupingMeasurable (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    SourceRawIndex S ≃ᵐ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toEquiv := sourceRawGrouping S
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

lemma sourceRawGrouping_preserving (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    MeasurePreserving (sourceRawGroupingMeasurable S) Measure.count
      ((Measure.count:Measure (SourceOuter S)).prod
        ((Measure.count:Measure CompletedPair).prod (Measure.count:Measure NonzeroFrequency))) := by
  rw [count_product,count_product]
  exact count_equiv_preserving _

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : Countable (Ideal O) := CubicEisenstein.cubicIdealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=> trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=> trivial⟩

local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=> trivial⟩

abbrev PhysicalNestedSpace (S : Finset (Ideal O)) := SourceOuter S×(ℝ×(ℝ×(CompletedPair×(ℝ×NonzeroFrequency))))

def physicalRawNesting (S : Finset (Ideal O)) : SourceRawIndex S×HeightSpace ≃ᵐ PhysicalNestedSpace S :=
  ((sourceRawGroupingMeasurable S).prodCongr (MeasurableEquiv.refl HeightSpace)).trans physicalNestingEquiv

lemma physicalRawNesting_preserving (S : Finset (Ideal O)) :
    MeasurePreserving (physicalRawNesting S)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
        ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
  exact (physicalNesting_preserving Measure.count Measure.count Measure.count volume volume volume).comp
    ((sourceRawGrouping_preserving S).prod (MeasurePreserving.id heightMeasure))

def originalNestedOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (p : PhysicalNestedSpace S) : ℂ :=
  originalRawOnLines η S hS D W0 W1 X Y Z
    ⟨(p.2.2.2.2.2,(p.2.2.2.1,p.1.val)),p.1.property⟩ ((p.2.2.1,p.2.2.2.2.1),p.2.1)

theorem originalRaw_integral_eq_nesting (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
    ∑'K : SourceOuter S,∫w : ℝ,∫t : ℝ,∑'IJ : CompletedPair,∫z : ℝ,∑'H : NonzeroFrequency,
      originalNestedOnLines η S hS D W0 W1 X Y Z (K,(w,(t,(IJ,(z,H))))) := by
  have hi := originalRaw_counting_product_integrable η S hS hpS hbad D W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp := physicalRawNesting_preserving S
  have hj := (hp.symm (physicalRawNesting S)).integrable_comp_of_integrable hi
  have he := hp.integral_comp' (originalNestedOnLines η S hS D W0 W1 X Y Z)
  have he' : (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
      ∫p : PhysicalNestedSpace S,originalNestedOnLines η S hS D W0 W1 X Y Z p
        ∂((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
          ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
    exact he
  rw [he']
  apply integral_physical_nesting
  exact hj

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

def sourceOuterEquiv (S : Finset (Ideal O)) : SourceOuter S ≃
    {K : {I : Ideal O // Supported I} // ∀P∈S,¬P∣K.val} where
  toFun K := ⟨⟨K.val,K.property.1⟩,K.property.2⟩
  invFun K := ⟨K.val.val,K.val.property,K.property⟩
  left_inv _K := rfl
  right_inv _K := rfl

lemma sourceOuter_tsum (S : Finset (Ideal O)) (f : {I : Ideal O // Supported I}→ℂ) :
    (∑'K : {I : Ideal O // Supported I},if ∀P∈S,¬P∣K.val then f K else 0)=
      ∑'K : SourceOuter S,f ⟨K.val,K.property.1⟩ := by
  have hs := tsum_subtype {K : {I : Ideal O // Supported I} | ∀P∈S,¬P∣K.val} f
  have he := (sourceOuterEquiv S).tsum_eq (fun K=> f K.val)
  calc
    _ = ∑' K : {I : Ideal O // Supported I},
        Set.indicator {K | ∀ P ∈ S, ¬P ∣ K.val} f K := by
      apply tsum_congr
      intro K
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs <;> rfl
    _ = _ := hs.symm.trans he.symm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace ProbePhysical
open Eisenstein SchwartzPlanePoisson
local notation "O" => Eisenstein.O

lemma radialFourier_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hσ : 0<σ) (hr : 0< r) :
    paperRadialFourier W r=verticalIntegral σ (fun z=>(r:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  have he := ProbeRadialMellin.radial_mellin_inversion W a b ha hW σ r hσ hr
  simpa only [mellinInv,verticalIntegral,Complex.real_smul,smul_eq_mul] using he.symm

lemma radial_sum_exchange {ι : Type*} [Countable ι] (W : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0< a) (hW : Function.support W⊆Set.Icc a b)
    (σ : ℝ) (hσ : 0<σ) (c : ι→ℂ) (r : ι→ℝ) (hr : ∀i,0< r i)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    (∑'i,c i*paperRadialFourier W (r i))=
      verticalIntegral σ (fun z=>∑'i,c i*(r i:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  let F := fun i (t : ℝ)=> c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*
    mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)
  have hF (i) : Integrable (F i) := by
    simpa only [F,mul_assoc] using
      (ProbeRadialMellin.radial_mellin_inverse_integrable W a b ha hW σ (r i) hσ (hr i)).const_mul (c i)
  have hn (i) (t : ℝ) : ‖F i t‖=(‖c i‖*(r i)^(-σ))*
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hr i)]
    simp
  have hsum : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp only [hn,integral_const_mul]
    exact hc.mul_right _
  have he := integral_tsum_of_summable_integral_norm hF hsum
  simp_rw [radialFourier_vertical_inverse W a b ha hW σ _ hσ (hr _)]
  unfold verticalIntegral
  have hi (i) : c i*(↑(1/(2*Real.pi))*(∫t : ℝ,
      (r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)))=
      (↑(1/(2*Real.pi)):ℂ)*(∫t : ℝ,F i t) := by
    simp only [F,mul_assoc,integral_const_mul]
    ring
  simp_rw [hi]
  rw [tsum_mul_left,he]

lemma frequency_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>(elementNorm H.val)^(-σ)) := by
  have he (H : NonzeroFrequency) : ‖frequencyWeight (σ:ℂ) H‖=(elementNorm H.val)^(-σ) := by
    have hH : 0< elementNorm H.val := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr H.property))
    rw [frequencyWeight,Complex.norm_cpow_eq_rpow_re_of_pos hH]
    simp
  simpa only [he,Complex.ofReal_re] using frequencyWeight_summable_norm (σ:ℂ) hσ

theorem actualFrequency_moment_summable (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (K : ℝ) (hK : 0< K) (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>‖actualCongruenceCoefficient C A s hA H.val‖*
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)) := by
  have hd : 0< elementNorm ((C.generator*A)*s) := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
  have hr (H : NonzeroFrequency) :
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)=
        (K/elementNorm ((C.generator*A)*s))^(-σ)*(elementNorm H.val)^(-σ) := by
    rw [show K*elementNorm H.val/elementNorm ((C.generator*A)*s)=
      (K/elementNorm ((C.generator*A)*s))*elementNorm H.val by ring]
    apply Real.mul_rpow (div_pos hK hd).le
    unfold elementNorm
    positivity
  simp only [hr]
  have hb := (frequency_rpow_summable σ hσ).mul_left
    (((Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {C.generator*A}):ℝ))*
      (K/elementNorm ((C.generator*A)*s))^(-σ))
  apply Summable.of_nonneg_of_le (fun H=> mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (div_pos hK hd).le _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _))) _ hb
  intro H
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (actualCongruenceCoefficient_norm_le C A s hA hs H.val)
      (Real.rpow_nonneg (div_pos hK hd).le _)) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace ProbePhysical
open Eisenstein SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma actualCongruenceCoefficient_zero_frequency (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA 0=0 := by
  apply actualCongruenceCoefficient_zero_off_calibration S hS A s hA hs hcop
  intro hc
  have hz := (calibrationForSet_coprime_iff S hS 0).mp hc
  obtain ⟨P,hP⟩ := hSne
  exact hz P hP P.zero_mem

theorem actualFrequency_mellin_nonzero (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0< K) (σ : ℝ) (hσ : 1<σ) :
    (∑'H : NonzeroFrequency,actualCongruenceCoefficient C A s hA H.val*
      paperRadialFourier W (K*elementNorm H.val/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  let : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
  have he := radial_sum_exchange W a b ha hW σ (by linarith)
    (fun H : NonzeroFrequency=> actualCongruenceCoefficient C A s hA H.val)
    (fun H=> K*elementNorm H.val/elementNorm ((C.generator*A)*s)) (by
      intro H
      exact div_pos (mul_pos hK (elementNorm_pos H.val H.property))
        (elementNorm_pos _ (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
    (actualFrequency_moment_summable C A s hA hs K hK σ hσ)
  simpa only [Complex.ofReal_mul,Complex.ofReal_div] using he

theorem actualFrequency_mellin (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s))
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0< K) (σ : ℝ) (hσ : 1<σ) :
    let C := calibrationForSet S hS
    (∑'H : O,actualCongruenceCoefficient C A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  dsimp only
  rw [←actualFrequency_mellin_nonzero (calibrationForSet S hS) A s hA hs W a b ha hW K hK σ hσ]
  symm
  apply (Subtype.val_injective : Function.Injective (fun H : NonzeroFrequency=> H.val)).tsum_eq
    (f:=fun H : O=> actualCongruenceCoefficient (calibrationForSet S hS) A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm (((calibrationForSet S hS).generator*A)*s)))
  intro H hH
  have hn : H≠0 := by
    intro hz
    subst H
    exact hH (by dsimp only; rw [actualCongruenceCoefficient_zero_frequency S hS hSne A s hA hs hcop,zero_mul])
  exact ⟨⟨H,hn⟩,rfl⟩

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
namespace ProbePhysical
open Eisenstein CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O

def transformedSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (K : ℝ) (t : ℂ) (I J : Ideal O) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C (completedIndex I J) s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s))
  else 0

theorem physical_spectral_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0< K) (t : ℂ) (ht : 1< t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C S D s hs W K t p.1 p.2 := by
  rw [physical_spectral_reopen η C S D s hs W hWc K hK t ht]
  apply tsum_congr
  intro p
  unfold transformedSpectralTerm
  by_cases hA : completedIndex p.1 p.2≠0
  · rw [dif_pos hA, physical_row_poisson C (completedIndex p.1 p.2) s hA
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) W hWc hWs K hK]
    ring
  · rw [dif_neg hA, spectralSummand_zero_completedIndex S D p.1 p.2 _ t (not_ne_iff.mp hA), zero_mul]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def radialMellinSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset Id) (D : Id) (s : O) (hs : Supported (Ideal.span {s}))
    (W : SchwartzMap ℝ ℂ) (K σ : ℝ) (t : ℂ) (I J : Id) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C (completedIndex I J) s hA H.val*
          ((K*elementNorm H.val/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)*
            mellin (paperRadialFourier W) z)
  else 0

theorem transformedSpectralTerm_radial_mellin (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (D : Id)
    (s : O) (hs : Supported (Ideal.span {s})) (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W⊆Set.Icc a b)
    (K σ : ℝ) (hK : 0< K) (hσ : 1<σ) (t : ℂ) (I J : Id) :
    transformedSpectralTerm η (calibrationForSet S hS) S D s hs W K t I J=
      radialMellinSpectralTerm η (calibrationForSet S hS) S D s hs W K σ t I J := by
  unfold transformedSpectralTerm radialMellinSpectralTerm
  split_ifs with hA
  · by_cases hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0
    · simp only [hz,zero_mul]
    · rw [actualFrequency_mellin S hS hSne (completedIndex I J) s hA (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs)
        ((spectralSummand_calibration_coprime S hS D I J _ t hz).mul_right hcs)
        W a b ha hW K hK σ hσ]
  · rfl

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
namespace ProbePhysical
open Eisenstein CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

lemma finiteSupport_verticalIntegral {α : Type*} (c : α → ℂ)
    (hc : (Function.support c).Finite) (F : α → ℂ → ℂ) (σ : ℝ)
    (hF : ∀ a, Integrable (fun y : ℝ => F a ((σ:ℂ)+y*Complex.I))) :
    verticalIntegral σ (fun t => ∑' a, c a * F a t) =
      ∑' a, c a * verticalIntegral σ (F a) := by
  have hz (a : α) (ha : a∉hc.toFinset) : c a=0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using ha
  have he (t : ℂ) : (∑' a, c a*F a t) = ∑ a∈hc.toFinset, c a*F a t :=
    tsum_eq_sum (fun a ha => by rw [hz a ha, zero_mul])
  rw [tsum_eq_sum (s := hc.toFinset) (fun a ha => by rw [hz a ha, zero_mul])]
  unfold verticalIntegral
  simp_rw [he]
  rw [integral_finsetSum _ (fun a ha => (hF a).const_mul (c a)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul]
  ring

theorem inner_mellin_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K Z : ℝ) (hK : 0< K) (hZ : 0< Z) :
    (∑' m : O, C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m) * W (elementNorm m/K) *
      verticalIntegral 4 (fun t => (Z:ℂ)^t * Complex.exp (t^2) *
        spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t)) =
    verticalIntegral 4 (fun t => (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      ((Z:ℂ)^t * Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D s hs W K t p.1 p.2) := by
  let c (m : O) := C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
    sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m) * W (elementNorm m/K)
  have hc : (Function.support c).Finite := by
    apply (elementWindow_finite_support W hWc K hK).subset
    intro m hm hz
    exact hm (by simp only [c, hz, mul_zero])
  rw [← finiteSupport_verticalIntegral c hc
    (fun m t => (Z:ℂ)^t * Complex.exp (t^2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t) 4
    (fun m => physicalRow_integrable η C D s hs m Z hZ)]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  norm_num only [Complex.ofReal_ofNat]
  have ht : 1 < ((4:ℂ)+(y:ℂ)*Complex.I).re := by simp
  rw [← physical_spectral_poisson η C C.excluded D s hs W hWc hWs K hK _ ht,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only [c]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => Eisenstein.O

def poissonPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y:ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p∈C.excluded, ¬p∣s.val then
      let a := primaryIdealGenerator s.val
      let has := (supported_span_primaryIdealGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s/Y) * CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q_s*X):ℂ)) *
      verticalIntegral 4 (fun t => (Real.sqrt q_s:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D a has W₀
          (elementNorm C.generator*q_s*X) t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀)
    (hWs : ContDiff ℝ ∞ W₀) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) :
    markedPhysicalProbe η C D W₀ W₁ X Y Z = poissonPhysicalProbe η C D W₀ W₁ X Y Z := by
  unfold markedPhysicalProbe poissonPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    have ha := supported_primaryIdealGenerator_ne_zero s.val s.property
    have has := (supported_span_primaryIdealGenerator_iff s.val).mpr s.property
    have hn : elementNorm (primaryIdealGenerator s.val) = (Ideal.absNorm s.val:ℝ) := by
      unfold elementNorm
      rw [(primaryIdealGenerator_spec s.val ha).1]
    have hb : 0< elementNorm C.generator := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
    have hs : 0<(Ideal.absNorm s.val:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
    have hK : 0< elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := mul_pos (mul_pos hb hs) hX
    simpa only [hn] using inner_mellin_poisson η C D (primaryIdealGenerator s.val) has
      W₀ hWc hWs (elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X) Z hK hZ
  · rfl

theorem physicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀) (hWs : ContDiff ℝ ∞ W₀)
    (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) :
    physicalProbe η C W₀ W₁ X Y Z = poissonPhysicalProbe η C 1 W₀ W₁ X Y Z :=
  markedPhysicalProbe_eq_poisson η C 1 W₀ W₁ hWc hWs X Y Z hX hZ

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => Eisenstein.O

def radialMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ) (X Y Z σ : ℝ) : ℂ :=
  (Y:ℂ)⁻¹*∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryIdealGenerator s.val
      let has := (supported_span_primaryIdealGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      W1 (qs/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ))*
      verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
        ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
          (elementNorm C.generator*qs*X) σ t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_radial_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ)
    (a b : ℝ) (ha : 0< a) (hW : Function.support W0⊆Set.Icc a b)
    (X Y Z σ : ℝ) (hX : 0< X) (hZ : 0< Z) (hσ : 1<σ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      radialMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z σ := by
  have hWc : HasCompactSupport (W0 : ℝ→ℂ) := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW
  rw [markedPhysicalProbe_eq_poisson η (calibrationForSet S hS) D W0 W1 hWc (W0.smooth (⊤:ℕ∞)) X Y Z hX hZ]
  unfold poissonPhysicalProbe radialMellinPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    congr 1
    unfold verticalIntegral
    congr 1
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    congr 1
    apply tsum_congr
    intro p
    have hcs : IsCoprime (calibrationForSet S hS).generator (primaryIdealGenerator s.val) := by
      apply calibrationForSet_coprime_of_excluded S hS
      rw [(primaryIdealGenerator_spec s.val (supported_primaryIdealGenerator_ne_zero s.val s.property)).1]
      simpa only [calibrationForSet_excluded] using hs
    have hK : 0< elementNorm (calibrationForSet S hS).generator*(Ideal.absNorm s.val:ℝ)*X :=
      mul_pos (mul_pos (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero)
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1))) hX
    simpa only [calibrationForSet_excluded] using transformedSpectralTerm_radial_mellin η S hS hSne D
      (primaryIdealGenerator s.val) ((supported_span_primaryIdealGenerator_iff s.val).mpr s.property) hcs
      W0 a b ha hW _ σ hK hσ _ p.1 p.2
  · rfl

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open CompletedGauss

lemma outer_source_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hr : 0< r) :
    W r=verticalIntegral σ (fun w=>(r:ℂ)^(-w)*mellin W w) := by
  simpa only [verticalIntegral,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,
    Complex.ofReal_ofNat] using compactMellin_inversion W a b ha hW (W.smooth (⊤:ℕ∞)) σ r hr

lemma outer_source_scaled_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a)
    (hW : Function.support W⊆Set.Icc a b) (σ N Y : ℝ) (hN : 0< N) (hY : 0< Y) :
    (Y:ℂ)⁻¹*W (N/Y)=
      verticalIntegral σ (fun w=>(Y:ℂ)^(w-1)*(N:ℂ)^(-w)*mellin W w) := by
  rw [outer_source_vertical_inverse W a b ha hW σ (N/Y) (div_pos hN hY)]
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he (w : ℂ) : (Y:ℂ)⁻¹*((N/Y:ℝ):ℂ)^(-w)=(Y:ℂ)^(w-1)*(N:ℂ)^(-w) := by
    rw [positive_div_cpow N Y hN.le hY,div_eq_mul_inv,
      ←Complex.cpow_neg,neg_neg]
    rw [show w-1=(-1)+w by ring,Complex.cpow_add _ _ hy,Complex.cpow_neg_one]
    ring
  unfold verticalIntegral
  simp_rw [←he,mul_assoc,integral_const_mul]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => Eisenstein.O

def nestedMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryIdealGenerator s.val
      let has := (supported_span_primaryIdealGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      verticalIntegral υ (fun w=>(Y:ℂ)^(w-1)*(qs:ℂ)^(-w)*mellin W1 w*
        (CanonicalRowCompletion.idealRowHom C.generator s.val /
          (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ)))*
        verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
          ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
            (elementNorm C.generator*qs*X) ξ t p.1 p.2))
    else 0

lemma verticalIntegral_mul_const (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun s=> F s*c)=verticalIntegral σ F*c := by
  unfold verticalIntegral
  rw [integral_mul_const,mul_assoc]

theorem markedPhysicalProbe_eq_nested_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (hξ : 1<ξ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      nestedMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z ξ υ := by
  rw [markedPhysicalProbe_eq_radial_mellin η S hS hSne D W0 W1 a0 b0 ha0 hW0 X Y Z ξ hX hZ hξ]
  unfold radialMellinPhysicalProbe nestedMellinPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    rw [verticalIntegral_mul_const,verticalIntegral_mul_const,
      ←outer_source_scaled_inverse W1 a1 b1 ha1 hW1 υ (Ideal.absNorm s.val:ℝ) Y
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)) hY]
    ring
  · simp only [mul_zero]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion ProbeCompleted ProbeRow CubicEisenstein
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O

lemma verticalIntegral_const_mul (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun z=> c*F z)=c*verticalIntegral σ F := by
  unfold verticalIntegral
  rw [integral_const_mul]
  ring

def rawRadialOuterFactor (C : CalibrationData) (K : Ideal O)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w : ℂ) : ℂ :=
  (Y:ℂ)^(w-1)*fullIdealWeight w K*mellin W1 w*
    (idealRowHom C.generator K /
      (C.tau*C.residueMonoid (primaryIdealGenerator K)*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)))*
    (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))

lemma rawPhysicalMellinTerm_radial_join (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ : ℝ) (t w : ℂ) :
    verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C S D I J K hK W0 W1 X Y Z H.val t w z)=
    rawRadialOuterFactor C K W1 X Y Z t w*
      radialMellinSpectralTerm η C S D (primaryIdealGenerator K)
        ((supported_span_primaryIdealGenerator_iff K).mpr hK) W0
          (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X) ξ t I J := by
  have hgen := (primaryIdealGenerator_spec K (supported_primaryIdealGenerator_ne_zero K hK)).1
  have hn : elementNorm (primaryIdealGenerator K)=(Ideal.absNorm K:ℝ) := by
    unfold elementNorm
    rw [hgen]
  unfold rawPhysicalMellinTerm physicalMellinCoefficientTerm radialMellinSpectralTerm
  split_ifs with hA
  · dsimp only
    simp only [hn,hgen]
    let c := rawRadialOuterFactor C K W1 X Y Z t w *
      (spectralSummand S D (baseRowCoefficient η C.Xi (primaryIdealGenerator K)
        ((supported_span_primaryIdealGenerator_iff K).mpr hK)) t I J *
        ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ))
    have hp (z : ℂ) (H : NonzeroFrequency) :
        idealRowHom C.generator K /
          (C.tau*C.residueMonoid (primaryIdealGenerator K)*
            (Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)) *
          (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹ *
          spectralSummand S D (baseRowCoefficient η C.Xi (primaryIdealGenerator K)
            ((supported_span_primaryIdealGenerator_iff K).mpr hK)) t I J *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
          actualCongruenceCoefficient C (completedIndex I J) (primaryIdealGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryIdealGenerator K):ℝ):ℂ)^(-z) *
          fullIdealWeight w K*(Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*
          mellin (paperRadialFourier W0) z*mellin W1 w =
        c*(actualCongruenceCoefficient C (completedIndex I J) (primaryIdealGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryIdealGenerator K):ℝ):ℂ)^(-z)*
          mellin (paperRadialFourier W0) z) := by
      dsimp only [c,rawRadialOuterFactor]
      ring
    simp only [Complex.ofReal_mul,Complex.ofReal_div] at hp ⊢
    simp_rw [hp,tsum_mul_left]
    rw [verticalIntegral_const_mul]
    dsimp only [c]
    simp only [Complex.ofReal_mul,Complex.ofReal_div]
    ring_nf
    congr 1
    apply congrArg (verticalIntegral ξ)
    funext z
    apply tsum_congr
    intro H
    congr 1 ; congr 1 ; ring_nf
  · simp only [zero_mul,tsum_zero,verticalIntegral,integral_zero,mul_zero]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow CubicEisenstein
local notation "O" => Eisenstein.O

def rawNestedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'K : SourceOuter C.excluded,verticalIntegral υ (fun w=> verticalIntegral 4 (fun t=>
    ∑'IJ : CompletedPair,verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C C.excluded D IJ.1 IJ.2 K.val K.property.1 W0 W1 X Y Z H.val t w z)))

theorem nestedMellinPhysicalProbe_eq_raw (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) :
    nestedMellinPhysicalProbe η C D W0 W1 X Y Z ξ υ=
      rawNestedPhysicalProbe η C D W0 W1 X Y Z ξ υ := by
  unfold nestedMellinPhysicalProbe rawNestedPhysicalProbe
  rw [sourceOuter_tsum]
  apply tsum_congr
  intro K
  dsimp only
  simp_rw [rawPhysicalMellinTerm_radial_join,tsum_mul_left]
  apply congrArg (verticalIntegral υ)
  funext w
  unfold rawRadialOuterFactor
  simp only [fullIdealWeight,if_neg K.property.1.1]
  unfold verticalIntegral
  simp_rw [mul_assoc,integral_const_mul]
  simp only [Complex.ofReal_natCast]
  ring_nf
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  ring_nf

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : Countable (Ideal O) := CubicEisenstein.cubicIdealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=> trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=> trivial⟩
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=> trivial⟩

def rawPhysicalTotalIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)

theorem rawNestedPhysicalProbe_eq_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    rawNestedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z 2 3=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  unfold rawPhysicalTotalIntegral
  rw [originalRaw_integral_eq_nesting η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  unfold rawNestedPhysicalProbe
  simp only [calibrationForSet_excluded]
  simp only [verticalIntegral,integral_const_mul,tsum_mul_left]
  unfold originalNestedOnLines originalRawOnLines
  simp only [Complex.ofReal_ofNat]
  ring_nf
  congr 1
  let e : SourceOuter S ≃ SourceOuter (calibrationForSet S hS).excluded :=
    Equiv.subtypeEquivRight (fun K=> by rw [calibrationForSet_excluded])
  rw [←e.tsum_eq]
  apply tsum_congr
  intro K
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply tsum_congr
  intro IJ
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  apply tsum_congr
  intro H
  congr 1 ; ring

theorem markedPhysicalProbe_eq_raw_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_nested_mellin η S hS hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 2 3 hX hY hZ (by norm_num),nestedMellinPhysicalProbe_eq_raw]
  exact rawNestedPhysicalProbe_eq_integral η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

def rawArithmeticSeries (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) : ℂ :=
  ∑'p : RawHighIndex,fullHighCoefficient S D η (fun H=> star (C.residueMonoid H.val))
    x w z (rawHighEmbedding p)

lemma rawHighCoefficient_outer_support (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : RawHighIndex)
    (hp : fullHighCoefficient S D η mask x w z (rawHighEmbedding p)≠0) :
    Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2 := by
  have hb : bareIdealHighCoefficient η p.1.val p.2.1.1 p.2.1.2 p.2.2 1≠0 := by
    intro hz
    exact hp (by simp only [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,bareIdealHighSummand,hz,mul_zero,zero_mul])
  have hs : Supported p.2.2 := by
    unfold bareIdealHighCoefficient at hb
    split_ifs at hb with hh
    · exact hh.2.2.2.1
    · exact False.elim (hb rfl)
  refine ⟨hs,?_⟩
  by_contra hn
  exact hp (by simp [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,highIdealMask,hn])

lemma rawArithmeticSeries_eq_sourceRaw (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) :
    rawArithmeticSeries S D η C x w z=
      ∑'i : SourceRawIndex S,fullHighCoefficient S D η (fun H=> star (C.residueMonoid H.val))
        x w z (sourceRawEmbedding S i) := by
  unfold rawArithmeticSeries sourceRawEmbedding
  change _ = ∑'i : {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}, _
  symm
  apply tsum_subtype_eq_of_support_subset (f:=fun p : RawHighIndex=>
    fullHighCoefficient S D η (fun H=> star (C.residueMonoid H.val)) x w z (rawHighEmbedding p))
    (s:={p : RawHighIndex | Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2})
  intro p hp
  exact rawHighCoefficient_outer_support S D η _ x w z p hp

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : Countable (Ideal O) := CubicEisenstein.cubicIdealGenerator_injective.countable
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=> trivial⟩

def rawSourceOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  initialHighOnLines S D η (fun H=> star ((calibrationForSet S hS).residueMonoid H.val))
    3 3 2 (sourceRawEmbedding S i) p *sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

lemma originalRawOnLines_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0< X) (i : SourceRawIndex S) (p : HeightSpace) :
    originalRawOnLines η S hS D W0 W1 X Y Z i p=
      rawSourceOnLines η S hS D W0 W1 X Y Z i (sourceHeightShear.symm p) := by
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ i.property.1
    i.property.2 W0 W1 X Y Z hX i.val.1]
  have he : (4:ℂ)+p.1.1*Complex.I+1-((2:ℂ)+p.1.2*Complex.I)=
      3+((p.1.1-p.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hs : sourceHeightShear.symm p=((p.1.1-p.1.2,p.1.2),p.2) := rfl
  simp only [rawSourceOnLines,initialHighOnLines,he,hs,sourceRawEmbedding,Complex.ofReal_ofNat]
  ring

lemma rawSourceOnLines_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=> rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  have hm (H : NonzeroFrequency) : ‖star ((calibrationForSet S hS).residueMonoid H.val)‖≤1 := by
    simpa only [norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  unfold rawSourceOnLines
  apply initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η (fun H=> star ((calibrationForSet S hS).residueMonoid H.val)) hm 3 3 2
    (by norm_num) (by norm_num) (by norm_num)
    (fun p : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I))
  · exact sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ 3 2 3 (by norm_num)
  · exact sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
      X Y Z hX hY hZ 3 2 3 (by norm_num)

lemma rawPhysicalTotalIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0< X) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : SourceRawIndex S×HeightSpace,rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2
          ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  unfold rawPhysicalTotalIntegral
  congr 1
  let e : SourceRawIndex S×HeightSpace ≃ᵐ SourceRawIndex S×HeightSpace :=
    (MeasurableEquiv.refl (SourceRawIndex S)).prodCongr sourceHeightShear.symm
  have hp : MeasurePreserving e ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) :=
    (MeasurePreserving.id _).prod (sourceHeightShear_preserving.symm sourceHeightShear)
  have he := hp.integral_comp' (fun p : SourceRawIndex S×HeightSpace=>
    rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
  refine Eq.trans ?_ he
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  exact originalRawOnLines_eq_source η S hS hpS hbad D W0 W1 X Y Z hX p.1 p.2

def rawSourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    rawArithmeticSeries S D η (calibrationForSet S hS) ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

lemma rawPhysicalTotalIntegral_eq_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [rawPhysicalTotalIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z hX]
  unfold rawSourceTripleIntegral
  congr 1
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

theorem markedPhysicalProbe_eq_raw_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_integral η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  exact rawPhysicalTotalIntegral_eq_triple η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion Eisenstein HeckeInverseAmplification CenteredExceptionalCount 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem sixthRow_surjective (H : NonzeroFrequency) :
    ∃p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,rowMap p=H.val := by
  let I : Id := Ideal.span {H.val}
  have hI : I≠0 := Ideal.span_singleton_eq_bot.not.mpr H.property
  let J : Id := sixthQuotient I
  have hJ : J≠0 := sixthQuotient_ne_zero I
  let a := cubicIdealGenerator J
  have ha : a≠0 := cubicIdealGenerator_ne_zero J hJ
  have hspan : Ideal.span {a}=J := span_cubicIdealGenerator J
  have hd : a^6∣H.val := by
    apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
    rw [←Ideal.span_singleton_pow,hspan]
    change J^6∣I
    rw [←sixth_normal_form I hI]
    exact dvd_mul_left _ _
  obtain ⟨u,hu⟩ := hd
  have hu0 : u≠0 := by
    intro hz
    rw [hz,mul_zero] at hu
    exact H.property hu
  have hsu : Ideal.span {u}=sixthRemainder I := by
    have hi : Ideal.span {u}*J^6=I := by
      rw [←hspan,Ideal.span_singleton_pow,Ideal.span_singleton_mul_span_singleton]
      exact congrArg (fun b : O=> Ideal.span {b}) (by simpa only [mul_comm] using hu.symm)
    apply mul_right_cancel₀ (pow_ne_zero 6 hJ)
    exact hi.trans (sixth_normal_form I hI).symm
  have hf : SixthFree (Ideal.span {u}) := by
    rw [hsu]
    intro P
    exact sixthRemainder_valuation_lt I P
  refine ⟨(⟨u,hu0,hf⟩,⟨J,hJ⟩),?_⟩
  change u*a^6=H.val
  simpa only [mul_comm] using hu.symm

def sixthFrequencyEquiv : FreeRow×HeckeInverseAmplification.NonzeroIdeal ≃ NonzeroFrequency :=
  Equiv.ofBijective (fun p=>⟨rowMap p,rowMap_ne_zero p⟩) ⟨
    fun p q h=> rowMap_injective (congrArg Subtype.val h),
    fun H=> by obtain ⟨p,hp⟩ := sixthRow_surjective H;exact ⟨p,Subtype.ext hp⟩⟩

lemma sixthFrequencyEquiv_apply (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) :
    (sixthFrequencyEquiv p).val=p.1.val*(cubicIdealGenerator p.2.val)^6 := rfl

theorem tsum_sixth_decomposition (f : NonzeroFrequency→ℂ) :
    (∑'H : NonzeroFrequency,f H)=
      ∑'p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,f (sixthFrequencyEquiv p) :=
  (sixthFrequencyEquiv.tsum_eq f).symm

lemma idealGenerator_sixth_eq_primary (I : Id) (hI : CanonicalQuadraticSieve.Supported I) :
    (cubicIdealGenerator I)^6=(CubicEisenstein.primaryIdealGenerator I)^6 := by
  have he : Ideal.span {cubicIdealGenerator I}=Ideal.span {CubicEisenstein.primaryIdealGenerator I} :=
    (span_cubicIdealGenerator I).trans
      (CubicEisenstein.primaryIdealGenerator_spec I
        (supported_primaryIdealGenerator_ne_zero I hI)).1.symm
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
  have hh := congrArg (fun a : O=> a^6) hu
  simpa only [mul_pow,CanonicalRowCompletion.unit_pow_six,mul_one] using hh

lemma sixthFrequencyEquiv_primary (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal)
    (hP : CanonicalQuadraticSieve.Supported p.2.val) :
    (sixthFrequencyEquiv p).val=p.1.val*(CubicEisenstein.primaryIdealGenerator p.2.val)^6 := by
  rw [sixthFrequencyEquiv_apply,idealGenerator_sixth_eq_primary p.2.val hP]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein  CanonicalQuadraticSieve CubicEisenstein
open HeckeInverseAmplification
local notation "O" => Eisenstein.O

lemma calibration_sixth_ideal_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (L : Ideal O) :
    (calibrationForSet S hS).residueMonoid (cubicIdealGenerator L)^6=
      if ∀P∈S,¬P∣L then 1 else 0 := by
  by_cases hL : ∀P∈S,¬P∣L
  · rw [if_pos hL]
    apply calibrationForSet_residue_sixth
    apply calibrationForSet_coprime_of_excluded
    simpa only [span_cubicIdealGenerator] using hL
  · rw [if_neg hL]
    have hz : (calibrationForSet S hS).residueMonoid (cubicIdealGenerator L)=0 := by
      by_contra hn
      have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp hn
      have hc := (isUnit_quotient_span_iff (calibrationForSet S hS).generator (cubicIdealGenerator L)).mp hu
      have ho := (calibrationForSet_coprime_iff S hS (cubicIdealGenerator L)).mp hc
      apply hL
      intro P hP hd
      apply ho P hP
      apply (Ideal.dvd_iff_le.mp hd)
      have hm : cubicIdealGenerator L∈Ideal.span ({cubicIdealGenerator L}:Set O) := Ideal.subset_span (by simp)
      rw [span_cubicIdealGenerator L] at hm
      exact hm
    rw [hz,zero_pow (by decide : 6≠0)]

lemma calibration_sixth_frequency_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (u : O) (L : Ideal O) :
    star ((calibrationForSet S hS).residueMonoid (u*cubicIdealGenerator L^6))=
      star ((calibrationForSet S hS).residueMonoid u)*(if ∀P∈S,¬P∣L then 1 else 0) := by
  rw [map_mul,map_pow,calibration_sixth_ideal_mask]
  split_ifs <;> simp only [mul_one,mul_zero,star_zero]

lemma sixthFrequencyWeight (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (z : ℂ) :
    frequencyWeight z (sixthFrequencyEquiv p)=
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*fullIdealWeight (6*z) p.2.val := by
  have hu : 0< elementNorm p.1.val := elementNorm_pos _ p.1.property.1
  have hl : 0<(Ideal.absNorm p.2.val:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.2.property)
  have hn : elementNorm (sixthFrequencyEquiv p).val=
      elementNorm p.1.val*(Ideal.absNorm p.2.val:ℝ)^6 := by
    unfold elementNorm
    exact_mod_cast rowMap_norm p
  simp only [frequencyWeight,fullIdealWeight,if_neg p.2.property,hn,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hu.le (pow_nonneg hl.le 6)]
  congr 1
  have he := Complex.cpow_mul_ofReal_nonneg hl.le (6:ℝ) (-z)
  simp only [Real.rpow_ofNat,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_natCast] at he
  simp only [Complex.ofReal_pow,Complex.ofReal_natCast]
  rw [←he]
  congr 1
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalQuadraticSieve ProbeCompleted
open HeckeInverseAmplification  CubicEisenstein
local notation "O" => Eisenstein.O

lemma bareIdealHighCoefficient_sixth (η : HeckeFamily.Character)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (hL : Supported p.2.val)
    (I J K : Ideal O) :
    bareIdealHighCoefficient η (sixthFrequencyEquiv p).val I J K 1=
      bareIdealHighCoefficient η p.1.val I J K p.2.val := by
  rw [sixthFrequencyEquiv_primary p hL]
  unfold bareIdealHighCoefficient
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K
  · simp only [h.1,h.2.1,h.2.2.1,h.2.2.2,hL,CenteredMomentAddedZero.supported_one_ideal,and_self,dif_pos]
    congr 1
    simp only [primaryIdealGenerator_one,one_pow,mul_one]
  · have h1 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun hh=> h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    have h2 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported p.2.val) :=
      fun hh=> h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    rw [dif_neg h1,dif_neg h2]

lemma rawHighCoefficient_sixth (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Ideal O) (η : HeckeFamily.Character) (x w z : ℂ)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (I J K : Ideal O) :
    fullHighCoefficient S D η
      (fun H=> star ((calibrationForSet S hS).residueMonoid H.val)) x w z
      (rawHighEmbedding (sixthFrequencyEquiv p,((I,J),K)))=
    star ((calibrationForSet S hS).residueMonoid p.1.val)*
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*
      markedIdealHighSummand S D η p.1.val x w z I J K p.2.val := by
  have hOne : ∀P∈S,¬P∣(1:Ideal O) := fun P hP=> (hprime P hP).not_dvd_one
  change star ((calibrationForSet S hS).residueMonoid (sixthFrequencyEquiv p).val)*
    frequencyWeight z (sixthFrequencyEquiv p)*
      markedIdealHighSummand S D η (sixthFrequencyEquiv p).val x w z I J K 1=_
  rw [sixthFrequencyWeight]
  rw [sixthFrequencyEquiv_apply,calibration_sixth_frequency_mask]
  by_cases hL : ∀P∈S,¬P∣p.2.val
  · have hs := supported_of_source_exclusions S hbad p.2.val p.2.property hL
    have hb := bareIdealHighCoefficient_sixth η p hs I J K
    rw [sixthFrequencyEquiv_apply] at hb
    simp only [if_pos hL,mul_one,markedIdealHighSummand,highIdealMask,if_pos hOne,
      bareIdealHighSummand,hb]
    have hw1 : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
    rw [hw1]
    ring
  · simp only [if_neg hL,mul_zero,zero_mul,markedIdealHighSummand,highIdealMask]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open CanonicalQuadraticSieve HeckeInverseAmplification ProbeCompleted
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev SixthInnerIndex := HeckeInverseAmplification.NonzeroIdeal×((Id×Id)×Id)

def sixthRawEquiv : FreeRow×SixthInnerIndex ≃ RawHighIndex :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr sixthFrequencyEquiv (Equiv.refl _))

def nonzeroLastEquiv : SixthInnerIndex ≃ {p : (Id×Id)×(Id×Id) // p.2.2≠0} where
  toFun p := ⟨(p.2.1,(p.2.2,p.1.val)),p.1.property⟩
  invFun p := (⟨p.val.2.2,p.property⟩,(p.val.1,p.val.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

lemma markedIdealHighSummand_last_zero (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K : Id) :
    markedIdealHighSummand S D η u x w z I J K 0=0 := by
  have hz : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (0:Id)) :=
    fun h=> h.2.2.2.2.1 rfl
  simp only [markedIdealHighSummand,bareIdealHighSummand,bareIdealHighCoefficient,
    dif_neg hz,zero_mul,mul_zero]

lemma markedIdealHighSeries_eq_sixth_inner (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) :
    markedIdealHighSeries S D η u x w z=
      ∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val := by
  have he := nonzeroLastEquiv.tsum_eq (fun p=>
    markedIdealHighSummand S D η u x w z p.val.1.1 p.val.1.2 p.val.2.1 p.val.2.2)
  change (∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val)=_ at he
  rw [he]
  unfold markedIdealHighSeries
  symm
  apply tsum_subtype_eq_of_support_subset
    (f:=fun p : (Id×Id)×(Id×Id)=> markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (s:={p : (Id×Id)×(Id×Id) | p.2.2≠0})
  intro p hp hz
  apply hp
  change markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2=0
  rw [hz,markedIdealHighSummand_last_zero]

theorem rawArithmeticSeries_eq_sixth_high (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1< z.re) :
    rawArithmeticSeries S D η (calibrationForSet S hS) x w z=
      ∑'u : FreeRow,star ((calibrationForSet S hS).residueMonoid u.val)*
        frequencyWeight z ⟨u.val,u.property.1⟩*markedIdealHighSeries S D η u.val x w z := by
  let mask : NonzeroFrequency→ℂ := fun H=> star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  have hs := (fullHighSummand_summable S D η x w z hx hw hz mask hm).comp_injective
    rawHighEmbedding_injective
  have ht : Summable (fun p : FreeRow×SixthInnerIndex=>
      fullHighCoefficient S D η (fun H=> star ((calibrationForSet S hS).residueMonoid H.val)) x w z
        (rawHighEmbedding (sixthRawEquiv p))) := hs.comp_injective sixthRawEquiv.injective
  unfold rawArithmeticSeries
  rw [←sixthRawEquiv.tsum_eq]
  rw [ht.tsum_prod]
  apply tsum_congr
  intro u
  rw [markedIdealHighSeries_eq_sixth_inner,←tsum_mul_left]
  apply tsum_congr
  intro p
  exact rawHighCoefficient_sixth S hS hprime hbad D η x w z (u,p.1) p.2.1.1 p.2.1.2 p.2.2

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary ProbeCompleted HeckeInverseAmplification CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

def sourceRowSeries (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (C : CalibrationData) (D : Ideal O) (x w z : ℂ) : ℂ :=
  ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
    markedIdealHighSeries S D η u.val x w z

def sourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

lemma rawSourceTripleIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rawSourceTripleIntegral η S hS D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  unfold rawSourceTripleIntegral sourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  congr 1
  unfold sourceRowSeries
  exact rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem markedPhysicalProbe_eq_source_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_triple η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  exact rawSourceTripleIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : Countable (Ideal O) := CubicEisenstein.cubicIdealGenerator_injective.countable
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=> trivial⟩

lemma sourceRows_initial_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (fun p : HeightSpace=>
      sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
      sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  apply hi.integral_prod_right.congr
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp]
  have he := rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
  change rawArithmeticSeries S D η (calibrationForSet S hS) _ _ _=
    sourceRowSeries η S (calibrationForSet S hS) D _ _ _ at he
  rw [←he,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries

lemma sourceMellinWeight_subset (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q R : ℝ)
    (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (hQ : 0< Q) (hR : 0< R)
    (a x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*a*sourceMellinWeight W0 W1 (X/Q) (Y/Q) (Z*R) x w z=
      sourceMellinWeight W0 W1 X Y Z x w z*(Q:ℂ)^(z-w-1)*a*(R:ℂ)^(x+z-1) := by
  rw [sourceMellinWeight_marked W0 W1 (X/Q) (Y/Q) Z R hZ hR x w z]
  calc
    _ = a*(R:ℂ)^(x+z-1)*
        (((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z) := by ring
    _ = _ := by rw [sourceMellinWeight_rescaled W0 W1 X Y Z Q hX hY hQ x w z];ring

lemma tuple_norm_pos {K : ℕ} (p : Fin K→Eisenstein.O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) : 0< elementNorm (∏i∈J,p i) := by
  apply elementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=> hp i)

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

lemma tuple_norm_cpow {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0)
    (J : Finset (Fin K)) (s : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^s=∏i∈J,(elementNorm (p i):ℂ)^s := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,elementNorm_one,Complex.ofReal_one,Complex.one_cpow]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,elementNorm_mul,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (elementNorm_pos _ (hp i)).le (tuple_norm_pos p hp J).le,
      ih,Finset.prod_insert hi]

lemma tuple_target_star {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) :
    star (HeckeFamily.elementCoeff η (∏i∈J,p i))=∏i∈J,star (HeckeFamily.elementCoeff η (p i)) := by
  change star (ProbeRow.targetMonoid η (∏i∈J,p i))=_
  rw [map_prod,star_prod]
  rfl

lemma tuple_source_scalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (x w z : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)=
    (∏i,(elementNorm (p i):ℂ)^(z-1))*
      (∏i∈J,(elementNorm (p i):ℂ)^(-w))*
      (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x) := by
  rw [tuple_norm_cpow p hp J,tuple_norm_cpow p hp (Finset.univ\J),tuple_target_star]
  have he (i : Fin K) : (elementNorm (p i):ℂ)^(z-w-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^(-w) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  have hf (i : Fin K) : (elementNorm (p i):ℂ)^(x+z-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^x := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  simp only [he,hf,Finset.prod_mul_distrib]
  have hc := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i : Fin K=>(elementNorm (p i):ℂ)^(z-1))
  rw [←hc]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open HeckeIdealSeries
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def tupleSourceSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,
    (-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)*
      sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

def tupleSourceTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    tupleSourceSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

theorem compensatedTuple_eq_source_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      tupleSourceTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  let A : Finset (Fin K)→ℂ := fun J=>(-1:ℂ)^J.card*
    ((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))
  let F : Finset (Fin K)→HeightSpace→ℂ := fun J t=>
    sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
      (Z*elementNorm (∏i∈Finset.univ\J,p i))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hF (J : Finset (Fin K)) : Integrable (F J) heightMeasure :=
    sourceRows_initial_integrable η S hS hpS hbad _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))
  have hpoint (J : Finset (Fin K)) (t : HeightSpace) :
      A J*F J t=sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
      ((-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-((3:ℂ)+t.2*Complex.I)-1)*
        star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
        (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(((3:ℂ)+t.1.1*Complex.I)+((2:ℂ)+t.1.2*Complex.I)-1)*
        sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
          ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)) := by
    have he := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
      (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
      (tuple_norm_pos p hp (Finset.univ\J))
      (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i)))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    dsimp only [A,F]
    linear_combination (-1:ℂ)^J.card * he *
      sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
        ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hleft : compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,∫t,A J*F J t ∂heightMeasure := by
    unfold compensatedTuple ProbeCompensation.tupleOperation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only
    rw [markedPhysicalProbe_eq_source_triple η S hS hpS hbad hSne _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))]
    rw [integral_const_mul]
    change A J*(((1/(2*Real.pi):ℝ):ℂ)^3*∫t,F J t ∂heightMeasure)=_
    ring
  rw [hleft,←integral_finsetSum _ (fun J _=>(hF J).const_mul (A J))]
  unfold tupleSourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun J _=> hpoint J t)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries
open HeckeInverseAmplification
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma sourceRowSummand_summable (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (D : Id) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1< z.re) :
    Summable (fun u : FreeRow=> star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S D η u.val x w z) := by
  let e : FreeRow×((Id×Id)×(Id×Id))→FullHighIndex := fun p=>(⟨p.1.val,p.1.property.1⟩,p.2)
  have he : Function.Injective e := by
    intro a b h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun t : FullHighIndex=> t.1.val) h
    · exact congrArg (fun t : FullHighIndex=> t.2) h
  have hs := (fullHighSummand_summable S D η x w z hx hw hz
    (fun H=> star (C.residueMonoid H.val))
    (fun H=> by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val)).comp_injective he
  have ht := hs.prod
  apply ht.congr
  intro u
  dsimp only [Function.comp_def,e]
  exact tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩)
    (f:=fun c : (Id×Id)×(Id×Id)=> markedIdealHighSummand S D η u.val x w z c.1.1 c.1.2 c.2.1 c.2.2)

def tupleIndexedCoefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) (x w : ℂ) : ℂ :=
  (-1:ℂ)^J.card*(∏i∈J,(elementNorm (p i):ℂ)^(-w))*
    (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x)

def indexedCompensatedHigh {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (u : O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
    markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z

lemma tupleSourceSeries_common_scale {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
          sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z := by
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_source_scalar η p hp J x w z
  unfold tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*he*
    sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

theorem tupleSourceSeries_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1< z.re) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
          indexedCompensatedHigh η S p u.val x w z := by
  rw [tupleSourceSeries_common_scale η S C p hp]
  congr 1
  let f : Finset (Fin K)→FreeRow→ℂ := fun J u=> tupleIndexedCoefficient η p J x w*
    (star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u.val x w z)
  have hf (J : Finset (Fin K)) : Summable (f J) :=
    (sourceRowSummand_summable η S C _ x w z hx hw hz).mul_left _
  have hsum := Summable.tsum_finsetSum (s:=(Finset.univ:Finset (Fin K)).powerset)
    (f:=f) (fun J _=> hf J)
  unfold sourceRowSeries
  simp only [←tsum_mul_left]
  change (∑J∈(Finset.univ:Finset (Fin K)).powerset,∑'u,f J u)=_
  rw [←hsum]
  apply tsum_congr
  intro u
  unfold indexedCompensatedHigh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [f]
  ring

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

def tuplePhysicalScalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))

lemma tuple_scaled_coefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (x w z : ℂ) :
    tuplePhysicalScalar η p J*
      sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z=
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      tupleIndexedCoefficient η p J x w := by
  have ha := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
    (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
    (tuple_norm_pos p hp (Finset.univ\J))
    (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))) x w z
  have hb := tuple_source_scalar η p hp J x w z
  unfold tuplePhysicalScalar tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*ha +
    (-1:ℂ)^J.card*sourceMellinWeight W0 W1 X Y Z x w z*hb

lemma compensatedRow_kernel_subsets {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (hp : ∀i,p i≠0) (u : O) (a : ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      (a*indexedCompensatedHigh η S p u x w z)=
    ∑J∈(Finset.univ:Finset (Fin K)).powerset,tuplePhysicalScalar η p J*
      ((a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z)*
        sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
          (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z) := by
  unfold indexedCompensatedHigh
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_scaled_coefficient η p hp J W0 W1 X Y Z hX hY hZ x w z
  linear_combination -a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z*he

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma span_tupleProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    Ideal.span {∏i∈J,p i}=∏i∈J,Ideal.span {p i} := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Ideal.span_singleton_one,Ideal.one_eq_top]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,←Ideal.span_singleton_mul_span_singleton,ih,Finset.prod_insert hi]

theorem indexedCompensatedHigh_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hs : ∀i,Supported (P i).val)
    (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=> primaryIdealGenerator (P i).val) 1 x w z=
      spectralCompensatedHigh S (Finset.univ.image P) η x w z
        (fun Q=> star (HeckeFamily.idealCoeff η Q.val)*(Ideal.absNorm Q.val:ℂ)^x)
        (fun Q=>(Ideal.absNorm Q.val:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedHigh
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (primaryIdealGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : HeckeFamily.elementCoeff η (primaryIdealGenerator (P i).val)=
      HeckeFamily.idealCoeff η (P i).val := targetMonoid_primaryIdealGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    CenteredMomentSourceRow.primary_span_supported _ (hs _)]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open HeckeIdealSeries
open CompletedGauss CanonicalQuadraticSieve ProbeEuler ProbeLocal
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem indexedCompensatedHigh_principal_continued {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    indexedCompensatedHigh η S (fun i=> primaryIdealGenerator (P i).val) 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x*globalClosedCorrection η S x w z)*
      ∏i,compensatedReplacement (coordV (Ideal.absNorm (P i).val) z)
        (coordW (Ideal.absNorm (P i).val) 1 w)
        (coordD (Ideal.absNorm (P i).val) (HeckeFamily.idealCoeff η (P i).val) 1 x)
        (idealMarkedClosed η (P i) x w z)
        (star (HeckeFamily.idealCoeff η (P i).val)*(Ideal.absNorm (P i).val:ℂ)^x)
        ((Ideal.absNorm (P i).val:ℂ)^(-w))/idealClosedCorrection η (P i) x w z := by
  have hs (i : Fin K) : Supported (P i).val := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_principal η S P hP hs]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedHigh_continued S hS (Finset.univ.image P) ht η x w z _ _ hx hw hz,
    Finset.prod_image hP.injOn]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open HeckeIdealSeries
open ProbeMellinBoundary CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def compensatedRowSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  (∏i,(elementNorm (p i):ℂ)^(z-1))*
    ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      indexedCompensatedHigh η S p u.val x w z

def compensatedRowTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    compensatedRowSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

lemma tupleSourceTripleIntegral_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O)
    (hp : ∀i,p i≠0) (X Y Z : ℝ) :
    tupleSourceTripleIntegral η S C W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S C W0 W1 p X Y Z := by
  unfold tupleSourceTripleIntegral compensatedRowTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact tupleSourceSeries_eq_rows η S C p hp
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem compensatedTuple_eq_row_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  rw [compensatedTuple_eq_source_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    p hp X Y Z hX hY hZ,tupleSourceTripleIntegral_eq_rows η S _ W0 W1 p hp]

theorem compensatedPhysicalProbe_eq_row_triples {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (slotPrimes : Fin K→Finset O) (hp : ∀i a,a∈slotPrimes i→a≠0)
    (slotWindow : Fin K→ℝ→ℂ) (slotScale : Fin K→ℝ)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1 slotPrimes slotWindow slotScale X Y Z=
      ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
        (∏i,slotWindow i (elementNorm (p i).val/slotScale i))*
        compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) X Y Z := by
  unfold compensatedPhysicalProbe
  apply Finset.sum_congr rfl
  intro p _
  rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (fun i=>(p i).val) (fun i=> hp i (p i).val (p i).property) X Y Z hX hY hZ]

end ProbePhysical
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
