/-
Compensated rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.RawNestingAndRadialExchange

/-!
# Compensated rows

Row integrals and marked Euler terms, finite physical rows of the high family and local high
factors; principal row integrals and the four families of the marked row series.
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
open MeasureTheory
namespace ProbePhysical
open HeckeIdealSeries
open ProbeMellinBoundary
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def highRowOnLines (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  star (C.residueMonoid u.val)*frequencyWeight ((ξ:ℂ)+t.1.2*Complex.I) u*
    markedIdealHighSeries S D η u.val ((σ:ℂ)+t.1.1*Complex.I)
      ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)

lemma highRowOnLines_eq_tsum (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (u : NonzeroFrequency) (t : HeightSpace) :
    highRowOnLines η S C D σ υ ξ u t=
      ∑'q : (Id×Id)×(Id×Id),initialHighOnLines S D η (fun H=> star (C.residueMonoid H.val))
        σ υ ξ (u,q) t := by
  unfold highRowOnLines markedIdealHighSeries initialHighOnLines fullHighCoefficient
  exact (tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight ((ξ:ℂ)+t.1.2*Complex.I) u)
    (f:=fun q : (Id×Id)×(Id×Id)=> markedIdealHighSummand S D η u.val
      ((σ:ℂ)+t.1.1*Complex.I) ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)
      q.1.1 q.1.2 q.2.1 q.2.2)).symm

lemma initialHighMajorant_row_summable (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ)
    (u : NonzeroFrequency) : Summable (fun q : (Id×Id)×(Id×Id)=> initialHighMajorant σ υ ξ (u,q)) := by
  unfold initialHighMajorant
  exact (highAbsoluteMajorant_summable (σ:ℂ) (υ:ℂ) (ξ:ℂ) hσ hυ hξ).mul_left ‖frequencyWeight (ξ:ℂ) u‖

lemma highRowOnLines_continuous (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ) (u : NonzeroFrequency) :
    Continuous (highRowOnLines η S C D σ υ ξ u) := by
  change Continuous (fun t=> highRowOnLines η S C D σ υ ξ u t)
  simp_rw [highRowOnLines_eq_tsum]
  apply continuous_tsum _ (initialHighMajorant_row_summable σ υ ξ hσ hυ hξ u)
    (fun q t=> initialHighOnLines_norm_le S D η (fun H=> star (C.residueMonoid H.val))
      (fun H=> by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val) σ υ ξ (u,q) t)
  intro q
  exact initialHighOnLines_continuous S D η _ σ υ ξ (u,q)

lemma highRowOnLines_bound (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ) (u : NonzeroFrequency) (t : HeightSpace) :
    ‖highRowOnLines η S C D σ υ ξ u t‖≤
      ‖frequencyWeight (ξ:ℂ) u‖*(∑'q : (Id×Id)×(Id×Id),highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) q) := by
  rw [highRowOnLines_eq_tsum]
  have hm := initialHighMajorant_row_summable σ υ ξ hσ hυ hξ u
  have hb (q : (Id×Id)×(Id×Id)) := initialHighOnLines_norm_le S D η
    (fun H=> star (C.residueMonoid H.val))
    (fun H=> by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val) σ υ ξ (u,q) t
  have hs := Summable.of_nonneg_of_le (fun q=> norm_nonneg _) hb hm
  apply (norm_tsum_le_tsum_norm hs).trans
  have he := hs.tsum_le_tsum hb hm
  simpa only [initialHighMajorant,tsum_mul_left] using he

lemma highRows_counting_product_integrable {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (e : ρ→NonzeroFrequency) (he : Function.Injective e)
    (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ρ×HeightSpace=> highRowOnLines η S C D σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ρ).prod heightMeasure) := by
  let A : ℝ := ∑'q : (Id×Id)×(Id×Id),highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) q
  have hA : 0≤ A := tsum_nonneg (highAbsoluteMajorant_nonneg _ _ _)
  have hb : Integrable (fun r : ρ=>‖frequencyWeight (ξ:ℂ) (e r)‖*A) Measure.count := by
    rw [integrable_count_iff]
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) hA)] using
      ((frequencyWeight_summable_norm (ξ:ℂ) hξ).comp_injective he).mul_right A
  apply (hb.mul_prod hT.norm).mono'
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro r
    exact ((highRowOnLines_continuous η S C D σ υ ξ hσ hυ (by linarith) (e r)).mul hcT).measurable
  · apply Filter.Eventually.of_forall
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (highRowOnLines_bound η S C D σ υ ξ hσ hυ (by linarith) (e p.1) p.2) (norm_nonneg _)

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
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=> trivial⟩

def compensatedRowOnLines {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
    ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
  (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
    (star (C.residueMonoid u.val)*frequencyWeight ((2:ℂ)+t.1.2*Complex.I) u*
      indexedCompensatedHigh η S p u.val ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I))

lemma compensatedRows_counting_product_integrable {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (e : ρ→NonzeroFrequency) (he : Function.Injective e)
    {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (hp : ∀i,p i≠0) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (fun q : ρ×HeightSpace=> compensatedRowOnLines η S C p W0 W1 X Y Z (e q.1) q.2)
      ((Measure.count:Measure ρ).prod heightMeasure) := by
  let F : Finset (Fin K)→ρ×HeightSpace→ℂ := fun J q=> tuplePhysicalScalar η p J*
    (highRowOnLines η S C (Ideal.span {∏i∈Finset.univ\J,p i}) 3 3 2 (e q.1) q.2*
      sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i))
        ((3:ℂ)+q.2.1.1*Complex.I) ((3:ℂ)+q.2.2*Complex.I) ((2:ℂ)+q.2.1.2*Complex.I))
  have hF (J : Finset (Fin K)) : Integrable (F J) ((Measure.count:Measure ρ).prod heightMeasure) := by
    apply Integrable.const_mul
    apply highRows_counting_product_integrable e he η S C _ 3 3 2 (by norm_num) (by norm_num) (by norm_num)
      (fun t : HeightSpace=> sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i))
        (Y/elementNorm (∏i∈J,p i)) (Z*elementNorm (∏i∈Finset.univ\J,p i))
        ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I))
    · exact sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
        _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
        (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J))) 3 2 3 (by norm_num)
    · exact sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
        _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
        (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J))) 3 2 3 (by norm_num)
  have hi := integrable_finsetSum (Finset.univ:Finset (Fin K)).powerset (fun J _=> hF J)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro q
  symm
  exact compensatedRow_kernel_subsets η S p hp (e q.1).val
    (star (C.residueMonoid (e q.1).val)*frequencyWeight ((2:ℂ)+q.2.1.2*Complex.I) (e q.1))
    W0 W1 X Y Z hX hY hZ _ _ _

lemma counting_product_integral_tsum {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (F : ρ×HeightSpace→ℂ)
    (hF : Integrable F ((Measure.count:Measure ρ).prod heightMeasure)) :
    (∫t,∑'r,F (r,t) ∂heightMeasure)=∑'r,∫t,F (r,t) ∂heightMeasure := by
  calc
    _ = ∫t,∫r,F (r,t) ∂(Measure.count:Measure ρ) ∂heightMeasure := by
      apply integral_congr_ae
      filter_upwards [hF.prod_left_ae] with t ht
      exact (integral_count_eq_tsum _ ht).symm
    _ = ∫q,F q ∂((Measure.count:Measure ρ).prod heightMeasure) := (integral_prod_symm F hF).symm
    _ = _ := by rw [integral_prod F hF,integral_count_eq_tsum _ hF.integral_prod_left]

theorem compensatedRowTripleIntegral_eq_tsum {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensatedRowTripleIntegral η S C W0 W1 p X Y Z=
      ∑'u : FreeRow,((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫t,compensatedRowOnLines η S C p W0 W1 X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure := by
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=> Subtype.ext (congrArg (fun u : NonzeroFrequency=> u.val) h)
  have hi := compensatedRows_counting_product_integrable e he η S C p hp W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  unfold compensatedRowTripleIntegral compensatedRowSeries
  rw [tsum_mul_left]
  congr 1
  rw [←counting_product_integral_tsum _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  simp only [compensatedRowOnLines,e,tsum_mul_left,mul_assoc]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeIdealSeries


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=> trivial⟩

def principalFreeRow : FreeRow := ⟨1,one_ne_zero,by
  intro P
  simp [Ideal.span_singleton_one,←Ideal.one_eq_top]⟩

def rowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫t,compensatedRowOnLines η S C p W0 W1 X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure

def principalRowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
      indexedCompensatedHigh η S p 1 ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

lemma rowIntegral_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rowIntegral η S C p W0 W1 X Y Z principalFreeRow=principalRowIntegral η S p W0 W1 X Y Z := by
  simp only [rowIntegral,principalRowIntegral,compensatedRowOnLines,principalFreeRow,
    frequencyWeight,elementNorm_one,map_one,star_one,Complex.ofReal_one,Complex.one_cpow,one_mul]

lemma rowIntegral_summable {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (hp : ∀i,p i≠0) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Summable (rowIntegral η S C p W0 W1 X Y Z) := by
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=> Subtype.ext (congrArg (fun v : NonzeroFrequency=> v.val) h)
  have hi := (compensatedRows_counting_product_integrable e he η S C p hp W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).integral_prod_left
  rw [integrable_count_iff] at hi
  exact hi.of_norm.mul_left _

theorem compensatedRowTripleIntegral_principal_split {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensatedRowTripleIntegral η S C W0 W1 p X Y Z=
      principalRowIntegral η S p W0 W1 X Y Z+
        ∑'u : FreeRow,if u=principalFreeRow then 0 else rowIntegral η S C p W0 W1 X Y Z u := by
  rw [compensatedRowTripleIntegral_eq_tsum η S C p hp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  change (∑'u : FreeRow,rowIntegral η S C p W0 W1 X Y Z u)=_
  rw [(rowIntegral_summable η S C p hp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).tsum_eq_add_tsum_ite principalFreeRow,
    rowIntegral_principal]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeIdealSeries


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

def finitePhysicalRows {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z u


end ProbeHighRowFamily
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeIdealSeries


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeMellinBoundary
open PrincipalMellinResidues ProbeFiniteProductBounds
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma principalTuple_source_integrand {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    sourceMellinWeight W0 W1 X Y Z x w z*
      (∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(z-1))*
      indexedCompensatedHigh η S (fun i=> primaryIdealGenerator (P i).val) 1 x w z=
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) x) w z*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w := by
  have hnorm (i : Fin K) : (elementNorm (primaryIdealGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  rw [indexedCompensatedHigh_principal_continued η S hS P hP hPS x w z hx hw hz]
  unfold sourceMultiplier sourceMellinWeight
  simp only [hnorm,slotMultiplier,Finset.sum_singleton,one_mul,localMultiplier,
    Complex.ofReal_natCast,Finset.prod_mul_distrib]
  ring

theorem principalRowIntegral_eq_sourceMultiplier {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    principalRowIntegral η S (fun i=> primaryIdealGenerator (P i).val) W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((3:ℂ)+t.1.1*Complex.I)
          (globalClosedCorrection η S ((3:ℂ)+t.1.1*Complex.I))
          (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) ((3:ℂ)+t.1.1*Complex.I))
          ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*((2:ℂ)+t.1.2*Complex.I))*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+t.2*Complex.I) ∂heightMeasure := by
  unfold principalRowIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  exact principalTuple_source_integrand η S hS P hP hPS W0 W1 X Y Z
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeIdealSeries


noncomputable section
open scoped Classical SchwartzMap
namespace ProbePhysical
open CompletedGauss CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem compensatedPhysicalProbe_canonical_slots {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 (fun i=> canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        compensatedTuple η C W0 W1 (fun i=> primaryIdealGenerator (P i).val.val) X Y Z :=
  sum_canonical_weighted_tuples T hT W Yp (fun p=> compensatedTuple η C W0 W1 p X Y Z)

theorem finitePhysicalRows_canonical_slots {K : ℕ} (S : Finset Id) (hmax : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(canonicalSlotSupport (T i))),
        (∏i,W i (elementNorm (p i).val/Yp i))*
          ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_canonical_weighted_tuples T hT W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold ProbeHighRowFamily.finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem compensatedPhysicalProbe_eq_canonical_rows {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
      (fun i=> canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑'u : FreeRow,∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hn (P : ∀i,↥(T i)) (i : Fin K) : primaryIdealGenerator (P i).val.val≠0 :=
    supported_primaryIdealGenerator_ne_zero _ (hT i _ (P i).property)
  have hs (P : ∀i,↥(T i)) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [compensatedPhysicalProbe_canonical_slots η _ W0 W1 T hT W Yp]
  calc
    _ = ∑P : (∀i,↥(T i)),∑'u : FreeRow,(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
      rowIntegral η S (calibrationForSet S hS) (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z u := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
          _ (hn P) X Y Z hX hY hZ,
          compensatedRowTripleIntegral_eq_tsum η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
        exact (tsum_mul_left
          (a := ∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))
          (f := fun u : FreeRow => rowIntegral η S (calibrationForSet S hS)
            (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z u)).symm
    _ = _ := (Summable.tsum_finsetSum (fun P _=> hs P)).symm

theorem finitePhysicalRows_original_primary_slots {K : ℕ} (S : Finset Id)
    (hmax : ∀P∈S,P.IsMaximal) (η : HeckeFamily.Character) (R : Finset FreeRow)
    (A : Fin K→Finset O) (hp : ∀i a,a∈A i→Prime (Ideal.span {a}))
    (hs : ∀i a,a∈A i→Supported (Ideal.span {a}))
    (hn : ∀i a,a∈A i→lambda^2∣a-1)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η R
      (fun i=> idealSlotOfPrimary (A i) (hp i)) W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(A i)),(∏i,W i (elementNorm (p i).val/Yp i))*
        ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_original_primary_weighted_tuples A hp hs hn W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold ProbeHighRowFamily.finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeIdealSeries


noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

lemma slotMultiplier_as_tuples {K : ℕ} (η : Character) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
    (b : Fin K→HeckeIdealSeries.PrimeIdeal→ℂ) (s w z : ℂ) :
    slotMultiplier η Finset.univ T b s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        slotMultiplier η Finset.univ (fun i=>{(P i).val}) (fun _ _=>1) s w z := by
  simp only [slotMultiplier,Finset.sum_singleton,one_mul]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (p : T i)=> b i p.val*localMultiplier η p.val s w z)]
  congr 1
  funext i
  exact (Finset.sum_coe_sort (T i) (fun p=> b i p*localMultiplier η p s w z)).symm

def principalPoolKernel {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (b : Fin K→HeckeIdealSeries.PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s) w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w

lemma principalPoolKernel_as_tuples {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (b : Fin K→HeckeIdealSeries.PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    principalPoolKernel η S hS T b W0 W1 X Y Z s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z s w z := by
  unfold principalPoolKernel sourceMultiplier
  rw [slotMultiplier_as_tuples]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  ring

theorem principal_physical_pool_initial {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→HeckeIdealSeries.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z)=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        principalPoolKernel η S hS T b W0 W1 X Y Z
          ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I) ∂heightMeasure := by
  let F (P : ∀i,T i) (t : HeightSpace) :=
    principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)
  have hF (P : ∀i,T i) : Integrable (F P) heightMeasure := by
    apply source_joint_integrable η S hS Finset.univ (fun i=>{(P i).val}) (fun _ _=>1)
      (by intro i hi p hp;simp only [Finset.mem_singleton] at hp;subst p;exact hT i _ (P i).property)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z 3 2 3 3 hX hY hZ
      (by norm_num) (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [principalPoolKernel_as_tuples η S hS T b W0 W1 X Y Z]
  rw [integral_finsetSum Finset.univ (fun P _=>(hF P).const_mul (∏i,b i (P i).val)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [principalRowIntegral_eq_sourceMultiplier η S hS (fun i=>(P i).val) (hdis P)
    (fun i=> hT i _ (P i).property) W0 W1 X Y Z,integral_const_mul]
  dsimp only [F,principalPoolKernel]
  ring

theorem principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→HeckeIdealSeries.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 7/8< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact ProbePrincipalTransport.source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=> hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

lemma finitePhysicalRows_principal {K : ℕ} (S : Finset Id) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η {principalFreeRow} T W Yp W0 W1 X Y Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        principalRowIntegral η S (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z := by
  simp only [ProbeHighRowFamily.finitePhysicalRows,Finset.sum_singleton,rowIntegral_principal]

theorem compensatedPhysicalProbe_principal_pool_split {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i=> canonicalSlotSupport (T i)) W Yp X Y Z=
      ProbeHighRowFamily.finitePhysicalRows S hmax η {principalFreeRow} T W Yp W0 W1 X Y Z+
      ∑'u : HeckeInverseAmplification.FreeRow,if u=principalFreeRow then 0 else
        ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
          rowIntegral η S (calibrationForSet S hmax) (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hSne : S.Nonempty := (by simp [fixedBadPrimes] : fixedBadPrimes.Nonempty).mono hS.bad
  rw [compensatedPhysicalProbe_eq_canonical_rows η S hmax hS.prime hS.bad hSne T hT W Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  have hs (P : ∀i,T i) : Summable (fun u : HeckeInverseAmplification.FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=> primaryIdealGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (fun i=> supported_primaryIdealGenerator_ne_zero _ (hT i _ (P i).property))
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [(summable_sum (s:=Finset.univ) (fun P _=> hs P)).tsum_eq_add_tsum_ite principalFreeRow]
  simp only [ProbeHighRowFamily.finitePhysicalRows,Finset.sum_singleton]

end ProbePrincipalPhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeIdealSeries


noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e≤1/1000)
    (ha : 7/8< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=1/6 → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤ W j x ∧ W j x≤ B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset HeckeIdealSeries.PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤ Z → (∀j,480≤ c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryIdealGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := ProbePrincipalRemainderBounds.source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0< Z := by linarith
  have hb := hbound ell hell W (fun j _=> hW j) (fun j _=> hsupp j) T (fun j _ p hp=> hT j p hp)
    Z hZ (fun j _=> hthreshold j) (fun j _=> hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=> fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)
  apply hn.trans
  have hCe : C≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤ Z^(HeckeZeroSupremum.beta-11/16-17/48000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end ProbePrincipalPhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open HeckeIdealSeries


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal Eisenstein.O

lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤ c) (hA : ‖A-R‖≤ c) (hN : ‖N⁻¹‖≤ v)
    (hR : ‖R/N-F‖≤ d) : ‖A/N-F‖≤ c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (Eisenstein.O ⧸ M)]
    (H : Subgroup (Eisenstein.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hmin : 0< ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0< e) (hehi : e≤1/1000) (hnu : 0< nu)
    (ha : 7/8< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryIdealGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := ProbePrincipalPhysical.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(7/8:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=> hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=> c) (fun _=> d) ell (fun _=> hc) (fun _=> hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0< Z := by linarith
  let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (1/6)
    (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=> Z^(ell j)) (c*Z^ellMin) (Z^(23/48:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=> hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j=> Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(7/8:ℝ))=c^(-(7/8:ℝ))*Z^(-(7/8:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-11/16)*(c*Z^ellMin)^(-(7/8:ℝ))=
      (D*c^(-(7/8:ℝ)))*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin=
      (HeckeZeroSupremum.beta+e-11/16)+(-(7/8:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤ C := by
    dsimp [C]
    have : 0≤ D*c^(-(7/8:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(7/8:ℝ))≤ C := by
    dsimp [C]
    have : 0≤ C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        C*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by gcongr
    _ = _ := by ring
end ProbePrincipalNormalized
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

lemma two_height_bound (t v w : ℝ) :
    (3+|t|)^2*(3+|w|)^2≤81*jointHeight t v w^4 := by
  have ht : 3+|t|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  have hw : 3+|w|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  calc
    _ ≤ (3*jointHeight t v w)^2*(3*jointHeight t v w)^2 := by gcongr
    _ = _ := by ring

theorem source_profile_integral_bound (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) :
    ∃C : ℝ,0< C ∧ ∀σ∈Icc slo shi,∀r∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀A : ℝ,0≤ A → ∀F : HeightSpace→ℝ,
      AEStronglyMeasurable F heightMeasure → (∀p,0≤ F p) →
      (∀p,F p≤ A*(3+|p.1.1|)^2*(3+|p.2|)^2) →
      Integrable (fun p=>‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p) heightMeasure ∧
      (∫p,‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p ∂heightMeasure)
        ≤ C*A*(X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)) := by
  obtain ⟨D,hD,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo 4
  refine ⟨81*D,by positivity,?_⟩
  intro σ hσ r hr υ hυ X Y Z hX hY hZ A hA F hF hF0 hFb
  let E : ℝ := X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)
  have hE : 0≤ E := by dsimp [E];positivity
  let M : HeightSpace→ℝ := fun p=> jointHeight p.1.1 p.1.2 p.2^4*‖onLines W0 W1 σ r υ p‖
  have hMi : Integrable M heightMeasure := (hM σ hσ r hr υ hυ).1
  have hMb : (∫p,M p ∂heightMeasure)≤ D := (hM σ hσ r hr υ hυ).2
  let f : HeightSpace→ℝ := fun p=>‖sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p
  have hfm : AEStronglyMeasurable f heightMeasure :=
    (sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
      σ r υ (hzlo.trans_le hr.1)).norm.aestronglyMeasurable.mul hF
  have hf0 (p : HeightSpace) : 0≤ f p := mul_nonneg (norm_nonneg _) (hF0 p)
  have hfb (p : HeightSpace) : f p≤(E*A*81)*M p := by
    have h1 := (hFb p).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (two_height_bound p.1.1 p.1.2 p.2) hA)
    have hs : ‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖=E*‖onLines W0 W1 σ r υ p‖ := by
      rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ]
      simp [E,onLines]
    dsimp only [f]
    rw [hs]
    calc
      _ ≤ (E*‖onLines W0 W1 σ r υ p‖)*(A*(81*jointHeight p.1.1 p.1.2 p.2^4)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hE (norm_nonneg _))
      _ = _ := by dsimp [M];ring
  have hfi : Integrable f heightMeasure := (hMi.const_mul (E*A*81)).mono' hfm
    (Filter.Eventually.of_forall fun p=> by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 p)];exact hfb p)
  refine ⟨hfi,?_⟩
  calc
    (∫p,f p ∂heightMeasure) ≤ ∫p,(E*A*81)*M p ∂heightMeasure :=
      integral_mono hfi (hMi.const_mul _) hfb
    _ = (E*A*81)*(∫p,M p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ (E*A*81)*D := mul_le_mul_of_nonneg_left hMb (by positivity)
    _ = _ := by ring

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss  GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation  ProbePrimePower ProbeLocal ProbeEuler
local notation "O" => Eisenstein.O

lemma finite_fourier_unit_scale {R : Type*} [CommRing R] [Fintype R]
    (F : R → ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (c : ℂ) (hc : c ≠ 0)
    (hF : ∀ x, F ((u : R) * x) = c * F x) (H : R) :
    (∑ x, F x * ψ (((u : R) * H) * x)) = c⁻¹ * ∑ x, F x * ψ (H*x) := by
  have he : (∑ x, F x * ψ (H*x)) = c * ∑ x, F x * ψ (((u : R)*H)*x) := by
    rw [← Equiv.sum_comp u.mulLeft (fun x => F x * ψ (H*x))]
    simp only [Units.mulLeft_apply, hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show H*((u : R)*x) = ((u : R)*H)*x by ring]
    ring
  rw [he, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem barePhysicalFourier_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    barePhysicalFourier A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA)
        (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        barePhysicalFourier A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA)
          (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) H := by
  have hAs := mul_ne_zero (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs)
  let := finiteEisensteinQuotientOfNonzero hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) b hcop.symm
  have hcA := idealRowHom_ne_zero_of_coprime A b hA hcop.of_mul_right_left.symm
  have hcs := idealRowHom_ne_zero_of_coprime s b hs hcop.of_mul_right_right.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) ((u : Residue (A*s))*x) =
        (idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹) *
          movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) x := by
    exact movingQuotient_unit_scale A s hs b hcop.of_mul_right_right x
  have he := finite_fourier_unit_scale (movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs))
    (primitiveTrace (A*s) hAs) u _ (mul_ne_zero hcA (inv_ne_zero hcs)) hF
    (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x, movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) x *
    primitiveTrace (A*s) hAs (Ideal.Quotient.mk _ (b*H)*x)) =
      _ * ∑ x, movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) x *
        primitiveTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u, residueUnit_coe, map_mul, mul_inv_rev, inv_inv, mul_comm] using he

theorem bareCongruenceCoefficient_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H := by
  have he := barePhysicalFourier_unit_frequency A s hA hs b H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

lemma idealRowHom_norm_one_of_coprime (s b : O)
    (hs : Supported (Ideal.span {s})) (hcop : IsCoprime b s) :
    ‖idealRowHom b (Ideal.span {s})‖ = 1 := by
  have h6 := idealRowHom_sixth_mask b (Ideal.span {s}) ((supported_iff_native _).mp hs)
  rw [idealRowHom_argument_pow _ _ _ ((supported_iff_native _).mp hs).1,
    if_pos ((Ideal.isCoprime_span_singleton_iff s b).mpr hcop.symm)] at h6
  exact Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0)

theorem bareCongruenceCoefficient_unit_frequency_norm (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    ‖bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (b*H)‖ =
      ‖bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H‖ := by
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop,
    norm_mul, norm_mul, norm_inv,
    idealRowHom_norm_one_of_coprime A b hA hcop.of_mul_right_left,
    idealRowHom_norm_one_of_coprime s b hs hcop.of_mul_right_right,
    inv_one, one_mul, one_mul]

theorem bareCongruenceCoefficient_unit_frequency_eq_zero_iff (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (b*H) = 0 ↔
      bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H = 0 := by
  rw [← norm_eq_zero, bareCongruenceCoefficient_unit_frequency_norm A s hA hs b H hcop,
    norm_eq_zero]

lemma supported_element_power (p : O) (hs : Supported (Ideal.span {p})) (n : ℕ) :
    Supported (Ideal.span {p^n}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hs n

lemma idealRowHom_prime_power_value (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (n : ℕ) :
    idealRowHom b (Ideal.span {p^n}) =
      (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^n := by
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg]

lemma complexSexticChar_unit_power_ne_zero (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hcop : IsCoprime b p) (t : ℕ) :
    (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t ≠ 0 := by
  apply pow_ne_zero
  exact (complexSexticChar (Ideal.span {p}) hg).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff p b).mpr hcop.symm)

theorem bareCongruenceCoefficient_prime_power_unit_frequency (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : lambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) := by
  have he := bareCongruenceCoefficient_unit_frequency (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  simpa only [idealRowHom_prime_power_value p b hg, div_eq_mul_inv, mul_comm] using he

theorem bareCongruenceCoefficient_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : lambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          sourceScalar p hp hg t k j := by
  rw [bareCongruenceCoefficient_prime_power_unit_frequency p hp hs hg b hcop t k j,
    bareCongruenceCoefficient_all_prime_powers p hp hg t k j]

theorem barePhysicalFourier_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : lambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    barePhysicalFourier (p^t) (p^k) (pow_ne_zero _ hp.ne_zero)
        (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      (Ideal.absNorm (Ideal.span {p^k}) : ℂ) *
        (((complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
          (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
            sourceScalar p hp hg t k j) := by
  rw [barePhysicalFourier_eq,
    bareCongruenceCoefficient_all_prime_powers_unit p hp hs hg b hcop t k j]

theorem bareCongruenceCoefficient_all_prime_powers_unit_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : lambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    ‖bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j)‖ =
      ‖sourceScalar p hp hg t k j‖ := by
  have he := bareCongruenceCoefficient_unit_frequency_norm (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  rw [bareCongruenceCoefficient_all_prime_powers p hp hg t k j] at he
  exact he

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePrimePower
open Eisenstein CompletedGauss 
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem row_even_kzero (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r+5) 0 (j+6*m) =
      if r+1≤ m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=5 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) else 0 := by
  rw [positiveScalar_kzero,complexSexticChar_primePowerGauss_at_pow p hp hg hc,
    if_pos (by omega : 6∣6*r+5+1)]
  by_cases hm : r+1≤ m
  · rw [if_pos hm,if_pos (by omega),if_pos (by omega),pow_succ]
    ring
  · rw [if_neg hm,if_neg (by omega)]
    by_cases hb : j=5 ∧ m=r
    · rw [if_pos hb,if_pos (by omega),zero_sub]
    · rw [if_neg hb,if_neg (by omega),sub_self]

theorem row_nonprincipal_kzero (r m j d : ℕ) (hj : j<6) (hd : d<5) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r+d) 0 (j+6*m) =
      if j=d ∧ m=r then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
          primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg^(d+1)) 1
      else 0 := by
  rw [positiveScalar_kzero,complexSexticChar_primePowerGauss_at_pow p hp hg hc,
    if_neg (by omega : ¬6∣6*r+d+1)]
  rw [show 6*r+d+1=6*r+(d+1) by omega,complexSexticChar_pow_six_mul_add _ hg hc]
  have he : j+6*m=6*r+d ↔ j=d ∧ m=r := by omega
  simp only [he]

theorem row_squarefree_kone (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r) 1 (j+6*m) =
      ((complexSexticChar (Ideal.span {p}) hg (-1))⁻¹ *
        primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1) *
        (if 6*r+1< j+6*m then
          (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
        else if j=1 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) else 0) := by
  rw [positiveScalar_actual_table p hp hg hc,if_neg (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤ j+6*m
  · rw [if_pos ⟨rfl,hpos⟩,gaussValuationTable,if_pos (by omega : 6∣6*r)]
    congr 1
    by_cases hb : 6*r+1< j+6*m
    · rw [if_pos hb,if_pos (by omega),if_pos (by omega),pow_succ]
      ring
    · rw [if_neg hb,if_neg (by omega)]
      by_cases he : j=1 ∧ m=r
      · rw [if_pos he,if_pos (by omega),zero_sub]
      · rw [if_neg he,if_neg (by omega),sub_self]
  · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),mul_zero]

theorem row_nonprincipal_kone (r m j d : ℕ) (hj : j<6) (hd0 : 0< d) (hd : d<5) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r+d) 1 (j+6*m) =
      if j=d+1 ∧ m=r then
        ((complexSexticChar (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
            primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg^d) 1)
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc,if_neg (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤ j+6*m
  · rw [if_pos ⟨rfl,hpos⟩,gaussValuationTable,if_neg (by omega : ¬6∣6*r+d),
      complexSexticChar_pow_six_mul_add _ hg hc]
    by_cases he : j=d+1 ∧ m=r
    · rw [if_pos he,if_pos (by omega)]
    · rw [if_neg he,if_neg (by omega),mul_zero]
  · rw [if_neg (by omega),if_neg (by omega)]

end ProbePrimePower
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

lemma localCubePhase_step_two (C omega : ℂ) (hC : C ^ 2=omega) (ho : omega^2=1)
    (e l k : ℕ) : localCubePhase C omega e (l+2) k=localCubePhase C omega e l k := by
  have hchoose : (l+2).choose 2=l.choose 2+2*l+1 := by
    rw [show l+2=(l+1)+1 by omega,Nat.choose_succ_succ,Nat.choose_one_right,
      Nat.choose_succ_succ,Nat.choose_one_right]
    change l+1+(l+l.choose 2)=l.choose 2+2*l+1
    omega
  unfold localCubePhase
  rw [pow_add C l 2,hC,hchoose]
  have he : (e+3*(l+2))*k+e*(l+2)+(l.choose 2+2*l+1)=
      ((e+3*l)*k+e*l+l.choose 2)+(2*(3*k+e+l)+1) := by ring
  have ht : omega^(2*(3*k+e+l)+1)=omega := by
    rw [pow_add,pow_mul omega 2,ho,one_pow,pow_one,one_mul]
  rw [he,pow_add omega _ (2*(3*k+e+l)+1),ht]
  calc
    _ = C ^ l*omega^((e+3*l)*k+e*l+l.choose 2)*omega^2 := by ring
    _ = _ := by rw [ho,mul_one]

theorem weightedScalar_step_two (Q eta a G1 C omega X W V scalar : ℂ)
    (hQ : Q≠0) (hC : C ^ 2=omega) (ho : omega^2=1) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*weightedScalar Q eta a G1 C omega X W V scalar e l k m := by
  unfold weightedScalar evenRatio
  rw [localCubePhase_step_two C omega hC ho]
  rw [pow_add (a*X^3/Q) l 2,pow_succ V m]
  have hbase : (a*X^3/Q)^2*Q^6=a^2*Q^4*X^6 := by
    field_simp
  linear_combination (-eta*X/G1)^e*(a*X^3/Q)^l*localCubePhase C omega e l k*scalar*W^k*V^m*V*hbase

def rowWeightedScalar (Q eta a G1 C omega X W V rho scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*weightedScalar Q eta a G1 C omega X W V scalar e l k m

lemma rowWeightedScalar_zero (Q eta a G1 C omega X W V rho : ℂ) (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho 0 e l k m=0 := by
  rw [rowWeightedScalar,weightedScalar_zero,mul_zero]

theorem rowWeightedScalar_parameters (Q eta a G1 C omega X W V rho scalar : ℂ)
    (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m=
      weightedScalar Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar e l k m := by
  unfold rowWeightedScalar weightedScalar
  simp only [pow_add,pow_mul,mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem evenRatio_unit (Q a X V rho : ℂ) (hρ : rho^6=1) :
    evenRatio Q (a/rho^3) X V=evenRatio Q a X V := by
  unfold evenRatio
  rw [div_pow,←pow_mul,show 3*2=6 by decide,hρ,div_one]

theorem rowWeightedScalar_step_two (Q eta a G1 C omega X W V rho scalar : ℂ)
    (hQ : Q≠0) (hC : C ^ 2=omega) (ho : omega^2=1) (hρ : rho^6=1) (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m := by
  rw [rowWeightedScalar_parameters,rowWeightedScalar_parameters,
    weightedScalar_step_two Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar hQ hC ho,
    evenRatio_unit Q a X V rho hρ]

end ProbeEuler
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePrimePower
open Eisenstein CompletedGauss 
local notation "O" => Eisenstein.O

lemma gaussValuationTable_step_six (Q G : ℂ) (r n j : ℕ) :
    gaussValuationTable Q G (r+6) (n+6) (j+6)=Q^6*gaussValuationTable Q G r n j := by
  have hd : 6∣r+6 ↔ 6∣r := by omega
  have hle : n+6+1≤ j+6 ↔ n+1≤ j := by omega
  have hle' : n+6≤ j+6 ↔ n≤ j := by omega
  have he : j+6=n+6 ↔ j=n := by omega
  simp only [gaussValuationTable,hd,hle,hle',he]
  split_ifs <;> simp [pow_add] <;> ring

theorem positiveScalar_step_six (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (n+6) k (j+6)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^6*
        positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k j := by
  rw [positiveScalar_actual_table p hp hg hc,positiveScalar_actual_table p hp hg hc]
  have hp6 (a : ℕ) : complexSexticChar (Ideal.span {p}) hg^(a+6)=
      complexSexticChar (Ideal.span {p}) hg^a := by
    rw [pow_add,complexSexticChar_six _ hg hc,mul_one]
  by_cases hk : k=0
  · simp only [hk,ite_true]
    rw [show n+6+1=(n+1)+6 by omega,hp6,gaussValuationTable_step_six]
  · simp only [if_neg hk]
    by_cases hk1 : k=1
    · subst k
      by_cases hj : 1≤ j
      · rw [if_pos ⟨rfl,by omega⟩,if_pos ⟨rfl,hj⟩,hp6,
          show j+6-1=(j-1)+6 by omega,gaussValuationTable_step_six]
        ring
      · have hz : j=0 := by omega
        subst j
        simp only [show (1:ℕ)≤0+6 by omega,show ¬(1:ℕ)≤0 by omega,
          and_true,and_false,ite_true,ite_false,mul_zero]
        simp only [gaussValuationTable]
        split_ifs <;> simp_all ; omega
    · rw [if_neg (by omega),if_neg (by omega),mul_zero]

theorem positiveScalar_zero_below (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) (hj : j< n) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k j=0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · simp only [gaussValuationTable]
    split_ifs <;> simp_all <;> omega
  · have hbelow : j-1< n := by omega
    have hz : gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg^n) 1) n n (j-1)=0 := by
      simp only [gaussValuationTable]
      split_ifs <;> simp_all <;> omega
    rw [hz,mul_zero]
  · rfl

end ProbePrimePower
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def rowMarkedTerm (eta a X W V rho : ℂ) (j e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    rowWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (complexSexticChar (Ideal.span {p}) hg (-1)) X W V rho
      (positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (e+3*l-1) k (j+6*m)) e l k m

include hc in
theorem rowMarkedTerm_step (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0< e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k (m+1)=
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
        rowMarkedTerm p hp hg eta a X W V rho j e l k m := by
  unfold rowMarkedTerm
  rw [if_neg (by omega),if_neg (by omega),
    show e+3*(l+2)-1=(e+3*l-1)+6 by omega,
    show j+6*(m+1)=(j+6*m)+6 by omega,
    positiveScalar_step_six p hp hg hc]
  exact rowWeightedScalar_step_two _ _ _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (complexSexticChar_neg_one_sq _ hg) hρ e l k m

theorem rowMarkedTerm_higher_outer (eta a X W V rho : ℂ) (j e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho j e l (k+2) m=0 := by
  unfold rowMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp,rowWeightedScalar_zero]

end ProbeEuler
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem bareSourceCoefficient_product_row_frequency (η : HeckeFamily.Character) (u : O) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryIdealGenerator I})) (hd : Supported (Ideal.span {primaryIdealGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : lambda^2∣primaryIdealGenerator I-1) (hpd : lambda^2∣primaryIdealGenerator J-1)
    (hpn : lambda^2∣n-1) (hpm : lambda^2∣m-1)
    (hps : lambda^2∣s-1) (hpr : lambda^2∣r-1)
    (hcop : IsCoprime ((primaryIdealGenerator I*n^3)*s) ((primaryIdealGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryIdealGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryIdealGenerator J*m^3)*r)) :
    let A := primaryIdealGenerator I*n^3
    let B := primaryIdealGenerator J*m^3
    let hA := CenteredMomentSupportedCorrelation.supported_element_ne_zero A (supported_completed _ _ hc hn)
    let hB := CenteredMomentSupportedCorrelation.supported_element_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) (u*(a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (u*a^6) * bareSourceCoefficient η J hJ.2 B r hB (u*b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop (u*(a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryIdealGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (u*a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryIdealGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (u*b^6) hab
  rw [show b^6*(u*a^6)=u*(a*b)^6 by ring] at hi
  rw [show a^6*(u*b^6)=u*(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

theorem bareIdealHighCoefficient_row_mul (η : HeckeFamily.Character) (u : O)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η u (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η u I J K L * bareIdealHighCoefficient η u I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryIdealGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryIdealGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryIdealGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryIdealGenerator_mul,primaryIdealGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_row_frequency η u I I'
      ⟨h.1,supported_primaryIdealGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryIdealGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryIdealGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryIdealGenerator J) (primaryIdealGenerator J') (primaryIdealGenerator K) (primaryIdealGenerator K')
      ((supported_span_primaryIdealGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryIdealGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryIdealGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryIdealGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryIdealGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryIdealGenerator_iff K').mpr h'.2.2.2.1)
      (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I h.2.1)).2
      (primaryIdealGenerator_spec I' (supported_primaryIdealGenerator_ne_zero I' h'.2.1)).2
      (primaryIdealGenerator_spec J (supported_primaryIdealGenerator_ne_zero J h.2.2.1)).2
      (primaryIdealGenerator_spec J' (supported_primaryIdealGenerator_ne_zero J' h'.2.2.1)).2
      (primaryIdealGenerator_spec K (supported_primaryIdealGenerator_ne_zero K h.2.2.2.1)).2
      (primaryIdealGenerator_spec K' (supported_primaryIdealGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryIdealGenerator L) (primaryIdealGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dif_pos hprod,dif_pos h,dif_pos h']
    simp only [primaryIdealGenerator_mul]
    dsimp only at he
    convert he using 1 <;> first | rfl | ring
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dif_neg hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=> h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dif_neg hj,mul_zero]
    · unfold highSupport at hi
      rw [dif_neg hi,zero_mul]

theorem bareIdealHighSummand_row_mul (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η u x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η u x w z I J K L * bareIdealHighSummand η u x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_mul η u I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase  
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

@[simp] theorem bareIdealHighCoefficient_row_one (η : HeckeFamily.Character) (u : O) :
    bareIdealHighCoefficient η u 1 1 1 1=1 := by
  have hs := CenteredMomentAddedZero.supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dif_pos hg]
  simp only [primaryIdealGenerator_one,one_pow,mul_one]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,ProbePhase.G_one,angularFactor_one]
  have ho := odd_of_supported (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_row_one (η : HeckeFamily.Character) (u : O) (x w z : ℂ) :
    bareIdealHighSummand η u x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_row_one,hw,one_mul]

theorem bareIdealHighSeries_row_hasProd (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (bareIdealHighSeries η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=> bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · exact bareIdealHighSummand_row_one η u x w z
  · intro a b hc
    exact bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc
  · intro a ha
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (bareIdealHighSummand_summable η u x w z hx hw hz).norm

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem excludedIdealHighSeries_row_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=> markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def rowHighPrimeTerm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

def idealRowHighLocalFactor (η : HeckeFamily.Character) (u : O) (P : Id) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, ∑' k : ℕ, ∑' m : ℕ,
    bareIdealHighSummand η u x w z (P^e.val) (P^l) (P^k) (P^m)

lemma rowHighPrimeTerm_summable_norm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖rowHighPrimeTerm η u x w z P b‖) := by
  have hs := ((bareIdealHighSummand_summable η u x w z hx hw hz).norm.comp_injective
    highIdeals_injective).comp_injective (Finsupp.single_injective P)
  simpa only [Function.comp_def,highIdeals_single,rowHighPrimeTerm] using hs

lemma rowHighPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤ e) :
    rowHighPrimeTerm η u x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η u x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_unit
  omega

theorem rowHighPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,rowHighPrimeTerm η u x w z P b)=
      idealRowHighLocalFactor η u P.val x w z := by
  have hs := (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, rowHighPrimeTerm η u x w z P ((e,l),b))=
        ∑' k,∑' m,rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=> by
    have hh : 2≤ e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_row_hasProd_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : PrimeIdeal=> idealRowHighLocalFactor η u P.val x w z)
      (bareIdealHighSeries η u x w z) := by
  have h := bareIdealHighSeries_row_hasProd η u x w z hx hw hz
  change HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,rowHighPrimeTerm η u x w z P b) _ at h
  simpa only [rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz] using h

theorem excludedRowHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η u x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealRowHighLocalFactor η u P.val x w z := by
  by_cases hP : P.val∈S
  · rw [if_pos hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_row_one,mul_one]
      · simp only [if_neg hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [if_neg hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

theorem excludedIdealHighSeries_row_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=> idealRowHighLocalFactor η u P.val.val x w z)
      (markedIdealHighSeries S 1 η u x w z) := by
  have h := excludedIdealHighSeries_row_hasProd S hS η u x w z hx hw hz
  simp only [excludedRowHighLocalFactor S hS η u x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=> idealRowHighLocalFactor η u P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_setOf_eq]
  split_ifs <;> simp_all

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

def sourceRowTerm (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (complexSexticChar (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (j+6*m)) e l k m

theorem sourceRowTerm_pos (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ)
    (ht : e+3*l≠0) :
    sourceRowTerm p hp hg eta a rho x w z j e l k m=
      rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowMarkedTerm,rowWeightedScalar,sourceScalar,if_neg ht,coordV,Complex.ofReal_natCast]

end ProbeEuler
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => Eisenstein.O

theorem bareSourceCoefficient_unit_frequency (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryIdealGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareSourceCoefficient η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (b*H)=
      ((idealRowHom b (Ideal.span {A}))⁻¹*idealRowHom b (Ideal.span {s}))*
        bareSourceCoefficient η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop]
  ring

theorem bareSourceCoefficient_row_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (e l k j : ℕ) (he : e≤1) (hI : primaryIdealGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^j)=
    ((complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (CompletedGauss.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (complexSexticChar (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j) := by
  rw [bareSourceCoefficient_unit_frequency η _ hI _ _
    (supported_element_power p hs _) (supported_element_power p hs _) b _
    (hb.pow_right.mul_right hb.pow_right),
    bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k j he hI,
    idealRowHom_prime_power_value p b hg,idealRowHom_prime_power_value p b hg]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem bareSourceCoefficient_row_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j e l k m : ℕ) (he : e≤1)
    (hI : primaryIdealGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^(j+6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
      (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  rw [bareSourceCoefficient_row_prime_formula η p hp hg hchar hprimary hs b hb e l k (j+6*m) he hI]
  unfold sourceRowTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (complexSexticChar (Ideal.span {p}) hg (-1)) (complexSexticChar_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (CompletedGauss.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  linear_combination -((complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
    sourceScalar p hp hg (e+3*l) k (j+6*m) *
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) * hpdiag

theorem bareIdealHighCoefficient_row_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (u : O) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η u ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryIdealGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (u*p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dif_pos hguard]
  simp only [primaryIdealGenerator_prime_power p hp.ne_zero hprimary]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

theorem bareIdealHighSummand_row_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η (b*p^j) x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m)=
      sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_at_prime η p hp hprimary hs (b*p^j) e l k m he]
  rw [show b*p^j*p^(6*m)=b*p^(j+6*m) by rw [pow_add]; ring]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_row_weighted_prime η p hp hg hchar hprimary hs b hb j e l k m he _ x w z

theorem idealRowHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j : ℕ) (x w z : ℂ) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e.val l k m := by
  unfold idealRowHighLocalFactor
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_row_at_prime η p hp hg hchar hprimary hs b hb j e.val l k m (by omega) x w z

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators
namespace ProbeEuler

theorem diagonal_recurrence_eq (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0) :
    ∀ r m,f r m=if r≤ m then R^r*f 0 (m-r) else 0 := by
  intro r
  induction r with
  | zero => intro m; simp
  | succ r ih =>
    intro m
    cases m with
    | zero => simp [hz]
    | succ m =>
      rw [hstep,ih]
      by_cases h : r≤ m
      · simp only [h,ite_true,Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub,pow_succ]
        ring
      · simp only [h,ite_false,Nat.succ_le_succ_iff,mul_zero]

theorem diagonal_recurrence_inner_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (r : ℕ) : HasSum (f r) (R^r*∑' m,f 0 m) := by
  have he := diagonal_recurrence_eq f R hstep hz
  have htail : HasSum (fun m=> f r (m+r)) (R^r*∑' m,f 0 m) := by
    apply (hs.hasSum.mul_left (R^r)).congr_fun
    intro m
    rw [he,if_pos (Nat.le_add_left r m),Nat.add_sub_cancel]
  have hzero : (∑ m∈Finset.range r,f r m)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [he,if_neg (by have := Finset.mem_range.mp hm; omega)]
  simpa only [hzero,zero_add] using htail.sum_range_add

theorem diagonal_recurrence_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (hR : ‖R‖<1) :
    HasSum (fun r=>∑' m,f r m) ((∑' m,f 0 m)/(1-R)) := by
  have he (r : ℕ) := (diagonal_recurrence_inner_hasSum f R hstep hz hs r).tsum_eq
  have hg : HasSum (fun r=> R^r*(∑' m,f 0 m)) ((∑' m,f 0 m)/(1-R)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (∑' m,f 0 m)
  exact hg.congr_fun he

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePrimePower
open Eisenstein CompletedGauss 
local notation "O" => Eisenstein.O

lemma geometric_indicator_summable (V A : ℂ) (hV : ‖V‖<1) (p : ℕ→Prop) :
    Summable (fun m=>(if p m then A else 0)*V^m) := by
  apply (((hasSum_geometric_of_norm_lt_one hV).summable.mul_left A).indicator {m | p m}).congr
  intro m
  by_cases hm : p m <;> simp [hm]

lemma gaussValuationTable_geometric_summable (Q G V : ℂ) (hV : ‖V‖<1)
    (r n : ℕ) (j : ℕ→ℕ) :
    Summable (fun m=> gaussValuationTable Q G r n (j m)*V^m) := by
  by_cases hr : 6∣r
  · have ha := geometric_indicator_summable V (Q^(n+1)) hV (fun m=> n+1≤ j m)
    have hb := geometric_indicator_summable V (Q^n) hV (fun m=> n≤ j m)
    apply (ha.sub hb).congr
    intro m
    simp only [gaussValuationTable,if_pos hr,sub_mul]
    split_ifs <;> rfl
  · apply (geometric_indicator_summable V (Q^n*G) hV (fun m=> j m=n)).congr
    intro m
    simp only [gaussValuationTable,if_neg hr]
    split_ifs <;> rfl

theorem positiveScalar_geometric_summable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k : ℕ) (j : ℕ→ℕ) (V : ℂ) (hV : ‖V‖<1) :
    Summable (fun m=> positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k (j m)*V^m) := by
  simp only [positiveScalar_actual_table p hp hg hc]
  by_cases hk : k=0
  · simp only [if_pos hk]
    exact gaussValuationTable_geometric_summable _ _ V hV (n+1) n j
  · simp only [if_neg hk]
    have hs := (gaussValuationTable_geometric_summable (Ideal.absNorm (Ideal.span {p}))
      (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg^n) 1) V hV n n (fun m=> j m-1)).mul_left
      (((complexSexticChar (Ideal.span {p}) hg (-1))⁻¹)*primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1)
    apply (hs.indicator {m | k=1 ∧ 1≤ j m}).congr
    intro m
    by_cases hm : k=1 ∧ 1≤ j m <;> simp [hm,mul_assoc]

end ProbePrimePower
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem rowMarkedTerm_frequency_summable (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l k : ℕ) : Summable (fun m=> rowMarkedTerm p hp hg eta a X W V rho j e l k m) := by
  by_cases ht : e+3*l=0
  · simp only [rowMarkedTerm,if_pos ht,summable_zero]
  · simp only [rowMarkedTerm,if_neg ht,rowWeightedScalar,weightedScalar]
    have hs := ProbePrimePower.positiveScalar_geometric_summable p hp hg hc (e+3*l-1) k (fun m=> j+6*m) V hV
    apply (hs.mul_left ((rho^k/rho^(e+3*l)) *
      ((-eta*X/primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1)^e *
        (a*X^3/(Ideal.absNorm (Ideal.span {p}):ℂ))^l *
        localCubePhase (star (localGamma p hp.ne_zero hg 3))
          (complexSexticChar (Ideal.span {p}) hg (-1)) e l k) *W^k)).congr
    intro m
    ring

theorem rowMarkedTerm_zero_lower_edge (eta a X W V rho : ℂ)
    (j e l k : ℕ) (hj : j<6) (ht : 0< e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k 0=0 := by
  unfold rowMarkedTerm
  rw [if_neg (by omega),positiveScalar_zero_below p hp hg hc _ _ _ (by omega),
    rowWeightedScalar_zero]

theorem rowMarkedFamily_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l k : ℕ) (hj : j<6) (ht : 0< e+3*l) :
    HasSum (fun r=>∑' m,rowMarkedTerm p hp hg eta a X W V rho j e (l+2*r) k m)
      ((∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply diagonal_recurrence_hasSum
  · intro r m
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_step p hp hg hc eta a X W V rho hρ j e (l+2*r) k m (by omega)
  · intro r
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_zero_lower_edge p hp hg hc eta a X W V rho j e (l+2*r) k hj (by omega)
  · simpa only [mul_zero,add_zero] using rowMarkedTerm_frequency_summable p hp hg hc eta a X W V rho hV j e l k
  · exact hR

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowInner (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑' k, ∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m

def rowMarkedSeries (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2, ∑' l,rowInner p hp hg eta a X W V rho j e.val l

lemma rowInner_two (eta a X W V rho : ℂ) (j e l : ℕ) :
    rowInner p hp hg eta a X W V rho j e l=
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 0 m)+
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [rowMarkedTerm_higher_outer,tsum_zero]

@[simp] lemma rowInner_zero (eta a X W V rho : ℂ) (j : ℕ) :
    rowInner p hp hg eta a X W V rho j 0 0=0 := by
  simp only [rowInner,rowMarkedTerm,mul_zero,add_zero,ite_true,tsum_zero]

include hc in
theorem rowInner_family_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l : ℕ) (hj : j<6) (ht : 0< e+3*l) :
    HasSum (fun r=> rowInner p hp hg eta a X W V rho j e (l+2*r))
      (rowInner p hp hg eta a X W V rho j e l/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  have h0 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 0 hj ht
  have h1 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 1 hj ht
  convert h0.add h1 using 1
  · funext r
    exact rowInner_two p hp hg eta a X W V rho j e (l+2*r)
  · rw [rowInner_two,add_div]

include hc in

theorem rowMarkedSeries_four_families (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=
      (rowInner p hp hg eta a X W V rho j 0 2+
       rowInner p hp hg eta a X W V rho j 1 0+
       rowInner p hp hg eta a X W V rho j 0 1+
       rowInner p hp hg eta a X W V rho j 1 1)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  have h02 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 2 hj (by omega)
  have h10 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 0 hj (by omega)
  have h01 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 1 hj (by omega)
  have h11 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 1 hj (by omega)
  have he0 : HasSum (fun r=> rowInner p hp hg eta a X W V rho j 0 (2*r))
      (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    have hshift : HasSum (fun r=> rowInner p hp hg eta a X W V rho j 0 (2*(r+1)))
        (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
      convert h02 using 1
      funext r
      congr 1
      omega
    have h := hshift.sum_range_add (f:=fun r=> rowInner p hp hg eta a X W V rho j 0 (2*r)) (k:=1)
    simpa only [Finset.sum_range_one,mul_zero,rowInner_zero,zero_add] using h
  have he1 : HasSum (fun r=> rowInner p hp hg eta a X W V rho j 1 (2*r))
      (rowInner p hp hg eta a X W V rho j 1 0/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [zero_add] using h10
  have ho0 : HasSum (fun r=> rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h01
  have ho1 : HasSum (fun r=> rowInner p hp hg eta a X W V rho j 1 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 1 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h11
  unfold rowMarkedSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
  rw [(he0.even_add_odd ho0).tsum_eq,(he1.even_add_odd ho1).tsum_eq]
  ring

end ProbeEuler
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
