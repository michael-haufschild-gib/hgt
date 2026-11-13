/-
Physical dyad integrals adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeRows.MarkedCompensation

/-!
# Physical dyad integrals

Continued rows on lines and physical row kernels, contour tuples and absolute dyad integrals;
first growth of calibrated numerators; small row and source scale bounds.
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
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem calibrated_physical_row_dyad (K : ℕ) (e δ a b r B : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0< a) (hb : 0< b) (hr : (17/50:ℝ)≤ r) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (U : ℝ),1≤ U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤ Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤ x.re → HeckeZeroSupremum.beta+8*e≤ x.re →
      (1/2:ℝ)≤ w.re → z.re=r →
      (∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=> hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_tuple_sum K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  let A : ℝ := ProbeSelectedPrimeSums.annularPower 1 2 (3/5+δ-r)
  have hA : 0< A := by
    have hh := le_max_left ((1:ℝ)^(3/5+δ-r)) ((2:ℝ)^(3/5+δ-r))
    rw [Real.one_rpow] at hh
    simpa only [A,ProbeSelectedPrimeSums.annularPower,Real.one_rpow] using (lt_of_lt_of_le zero_lt_one hh)
  refine ⟨256*C*A,by positivity,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let F : FreeRow→ℝ := fun u=>∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
    (fun i=> hT i (P i).val (P i).property) W Y x w z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^δ*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=> Real.rpow_nonneg (by linarith [hY i]) _
  have hD : 0≤ D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈R) : F u≤ D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ) := by
    have hh := hmain η u (hR u hu).1 T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
    apply hh.trans_eq
    dsimp [D]
    ring
  have heq (u : FreeRow) :
      (∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=> hT i (P i).val (P i).property) W Y x w z‖)=
      ‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    simp only [norm_mul,Finset.mul_sum,F]
  simp_rw [heq]
  apply (dyadic_weighted_rows (3/5+δ) r D U hD hU R (fun u hu=>(hR u hu).2) F hF z hz).trans_eq
  change 256*D*A*U^(1+(3/5+δ)-r)=_
  rw [show (1:ℝ)+(3/5+δ)-r=8/5+δ-r by ring]
  dsimp [D]
  ring

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α]
    (Q : ℂ) (hQ : Q≠0) (f : α→ℂ) (hf : Measurable f) : Measurable (fun t=> Q^(f t)) :=
  ((continuous_id.const_cpow (Or.inl hQ)).measurable).comp hf

lemma rowClosedMarked_measurable {α : Type*} [MeasurableSpace α]
    (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (η a ρ : ℂ) (j : ℕ)
    (X W V : α→ℂ) (hX : Measurable X) (hW : Measurable W) (hV : Measurable V) :
    Measurable (fun t=> rowClosedMarked p hp hg η a (X t) (W t) (V t) ρ j) := by
  unfold rowClosedMarked rowBaseFinite rowMarkedTerm rowWeightedScalar weightedScalar evenRatio
  simp only [Nat.reduceAdd,Nat.reduceMul,OfNat.ofNat_ne_zero,Nat.one_ne_zero,ite_false]
  fun_prop

lemma continuedMarkedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=> continuedMarkedLocal η u P hs (x t) (w t) (z t)) := by
  have hQ : (P.val.absNorm:ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  let : (Ideal.span {primaryIdealGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold continuedMarkedLocal
  apply rowClosedMarked_measurable
  · exact measurable_const_cpow _ hQ _ hx.neg
  · exact measurable_const_cpow _ hQ _ hw.neg
  · unfold coordV
    apply measurable_const_cpow _ (by exact_mod_cast hQ)
    fun_prop

lemma ramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=> ramifiedCorrection η u P hs (x t) (w t) (z t)) := by
  have hm := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  simp_rw [ramifiedCorrection_eq_marked]
  unfold coordV
  fun_prop (disch := exact hQ)

lemma idealUnramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=> idealUnramifiedCorrection η u P (x t) (w t) (z t)) := by
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealUnramifiedCorrection unramifiedClosed ProbeLocal.continuedCorrection markedFactor
    coordV coordR coordW coordD coordK
  fun_prop (disch := exact hQ)

lemma continuedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=> continuedCorrection S hS η u (x t) (w t) (z t)) := by
  unfold continuedCorrection ramifiedProduct unramifiedProduct
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro P hP
    exact ramifiedCorrection_measurable η u P.val _ x w z hx hw hz
  · apply Measurable.tprod
    intro P
    unfold unramifiedFactor
    split_ifs
    · exact measurable_const
    · exact idealUnramifiedCorrection_measurable η u P.val x w z hx hw hz

lemma continuedCompensatedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val)
    (x w z B q : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z)
    (hB : Measurable B) (hq : Measurable q) :
    Measurable (fun t=> continuedCompensatedLocal η u P hs (x t) (w t) (z t) (B t) (q t)) := by
  have hM := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement coordV coordW coordD
  fun_prop (disch := exact hQ)

lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  apply measurable_of_countable_not_continuousAt
  apply ((Set.finite_singleton (1:ℂ)).insert 0).countable.mono
  intro s hs
  by_contra hn
  have h0 : s≠0 := fun h=> hn (by simp [h])
  have h1 : s≠1 := fun h=> hn (by simp [h])
  exact hs (LFunction_differentiableAt χ h0 (Or.inl h1)).continuousAt

lemma regularizedL_measurable (χ : Character) : Measurable (HeckeReciprocal.regularizedL χ) := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_singleton (0:ℂ)).mono
  intro s hs
  by_contra hn
  exact hs (HeckeReciprocal.regularizedL_differentiableAt χ (by simpa using hn)).continuousAt

lemma reciprocal_measurable (χ : Character) : Measurable (HeckeReciprocal.reciprocal χ) := by
  have hL := LFunction_measurable χ
  have hR := regularizedL_measurable χ
  unfold HeckeReciprocal.reciprocal
  split_ifs <;> fun_prop

lemma continuedL_measurable (χ : Character) : Measurable (HeckeOrigin.continued χ) := by
  have hL := LFunction_measurable χ
  have hR := (HeckeOrigin.poleRemoved_entire χ).continuous.measurable
  unfold HeckeOrigin.continued
  split_ifs <;> fun_prop

lemma physicalCompensatedRow_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=> physicalCompensatedRow S hS T hT η u (x t) (w t) (z t)) := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply Measurable.mul
  · exact (((LFunction_measurable _).comp (by fun_prop)).mul
      ((continuedL_measurable _).comp hw)).mul ((reciprocal_measurable _).comp hx)
  · apply Measurable.mul
    · exact continuedCorrection_measurable _ _ η u x w z hx hw hz
    · apply Finset.measurable_prod
      intro P hP
      have hQ : (P.val.val.absNorm:ℂ)≠0 := by
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
      apply continuedCompensatedLocal_measurable _ _ _ _ x w z _ _ hx hw hz
      · exact (measurable_const_cpow _ hQ x hx).const_mul _
      · exact measurable_const_cpow _ hQ _ hw.neg

lemma calibratedTupleValue_measurable {α : Type*} [MeasurableSpace α] {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=> calibratedTupleValue S hS hmax η u P hPS W Y (x t) (w t) (z t)) := by
  unfold calibratedTupleValue
  apply Measurable.mul
  · apply Measurable.const_mul
    apply Finset.measurable_prod
    intro i hi
    apply Measurable.const_mul
    apply measurable_const_cpow _ _ _ (hz.sub measurable_const)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  · exact physicalCompensatedRow_measurable S hS _ _ η u x w z hx hw hz

lemma calibratedTupleValue_onLines_aestronglyMeasurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (σ υ ξ : ℝ)
    (μ : Measure ((ℝ×ℝ)×ℝ)) :
    AEStronglyMeasurable (fun t : (ℝ×ℝ)×ℝ=>
      calibratedTupleValue S hS hmax η u P hPS W Y
        ((σ:ℂ)+t.1.1*Complex.I) ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)) μ :=
  (calibratedTupleValue_measurable S hS hmax η u P hPS W Y _ _ _
    (by fun_prop) (by fun_prop) (by fun_prop)).aestronglyMeasurable

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

/-- Absolute row mass in a finite dyadic range, including all selected prime tuples. -/
def physicalDyadNorm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℝ :=
  ∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=> hT i (P i).val (P i).property) W Y x w z‖

lemma physicalDyadNorm_nonneg {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    0≤ physicalDyadNorm S hS hmax η R T hT W Y x w z := by
  exact Finset.sum_nonneg fun u hu=> Finset.sum_nonneg fun P hP=> norm_nonneg _

lemma physicalDyadNorm_onLines_aestronglyMeasurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (σ υ r : ℝ) : AEStronglyMeasurable (fun p : HeightSpace=> physicalDyadNorm S hS hmax η R T hT W Y
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  unfold physicalDyadNorm
  simp_rw [norm_mul,frequencyWeight_ideal_norm]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  convert Finset.aestronglyMeasurable_sum R (fun u hu=>
    Finset.aestronglyMeasurable_sum (Finset.univ : Finset (∀i,T i)) (fun P hP=>
      (calibratedTupleValue_onLines_aestronglyMeasurable S hS hmax η u
        (fun i=>(P i).val) (fun i=> hT i (P i).val (P i).property) W Y σ υ r heightMeasure).norm.const_mul
          (((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)))) using 1
  ext p
  simp only [Finset.sum_apply]

theorem calibrated_physical_dyad_integral (K : ℕ) (e δ a b r B σ υ : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0< a) (hb : 0< b) (hr : (17/50:ℝ)≤ r) (hB : 0≤ B)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hυ : (1/2:ℝ)≤υ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (U : ℝ),1≤ U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤ Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀X Y0 Z : ℝ,0< X → 0< Y0 → 0< Z →
      Integrable (fun p : HeightSpace=>‖sourceMellinWeight W0 W1 X Y0 Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
          physicalDyadNorm S hS hmax η R T hT W Y
            ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure ∧
      (∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y0 Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
          physicalDyadNorm S hS hmax η R T hT W Y
            ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*(∏i,(Y i)^r)*
        (X^(1/2-r)*Z^(σ+r-1)*Y0^(υ-1)) := by
  obtain ⟨C,hC,hD⟩ := calibrated_physical_row_dyad K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  obtain ⟨D,hDp,hP⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r υ υ (by linarith)
  refine ⟨D*C,mul_pos hDp hC,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB X Y0 Z hX hY0 hZ
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*(∏i,(Y i)^r)
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=> Real.rpow_nonneg (by linarith [hY i]) _
  have hA : 0≤ A := by dsimp [A];positivity
  have hbnd (p : HeightSpace) : physicalDyadNorm S hS hmax η R T hT W Y
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)
      ≤ A*(3+|p.1.1|)^2*(3+|p.2|)^2 := by
    have hh := hD η U hU R hR T hT hdis Y hY W hWS hWB
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)
      (by simpa using hσ) (by simpa using hσβ) (by simpa using hυ) (by simp)
    simpa only [A,physicalDyadNorm,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,mul_one,mul_zero,add_zero,zero_add] using hh
  obtain ⟨hi,hb⟩ := hP σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y0 Z hX hY0 hZ A hA _
    (physicalDyadNorm_onLines_aestronglyMeasurable S hS hmax η R T hT W Y σ υ r)
    (fun p=> physicalDyadNorm_nonneg S hS hmax η R T hT W Y _ _ _) hbnd
  refine ⟨hi,hb.trans_eq ?_⟩
  dsimp [A]
  ring

end ProbeHighRowFamily
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem nonprincipal_first_growth (χ : Character) (hχ : χ.residue≠1) :
    ∃C : ℝ,0< C ∧ ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖HeckeOrigin.continued χ s‖≤ C*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=> hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let R : ℝ := (HeckeDeletionBounds.radical χ.modulus).absNorm
  have hR : 1≤ R := by
    dsimp only [R]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  let C : ℝ := HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*Cd*R^(101/100:ℝ)
  have hC : 0≤ C := by dsimp [C];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro s hs
  have hl := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hl
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤ Cd*R^(101/100:ℝ) := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    exact Real.rpow_le_rpow_of_exponent_le hR (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num); linarith)
  rw [HeckeOrigin.continued,if_neg hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*R^(101/100:ℝ)) := mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ = C*(3+|s.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|s.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

theorem calibrated_numerator_first_growth (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0< C ∧ ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤ C*(3+|s.im|)^2 := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · refine ⟨1,by norm_num,?_⟩
    intro s hs
    simp only [hc,star_zero,zero_mul,norm_zero,one_mul]
    positivity
  · obtain ⟨C,hC,hbound⟩ := nonprincipal_first_growth (rowCharacter S hS.prime u)
      (calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc)
    refine ⟨C,hC,?_⟩
    intro s hs
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
      (hbound s hs)

theorem calibrated_physicalRow_first_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤ x.re) (hl : -(1/100:ℝ)≤ l) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+l) :
    ∃C : ℝ,0< C ∧ ∀w : ℂ,l≤ w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤ C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=> selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*Cn*(Ch*N)*∏P:T,A P
  have hA (P : T) : 0≤ A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=> hA P)
  have hC : 0≤ C := by dsimp [C,L,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn w (hl.trans hw)
  have hh' := hh eps S hS hfirst T η u x w z hx (hl.trans hw) hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      (hl.trans hw) hz (by linarith [hfirst.positive])
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
        ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [he,norm_mul,norm_mul,norm_mul]
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh'
  calc
    _ ≤ L*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      rw [norm_mul]
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [L,N];positivity)
      apply mul_le_mul _ hh'' (norm_nonneg _) (by dsimp [L,N];positivity)
      exact mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = C*(3+|w.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem physicalRow_first_z_bounded (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re)
    (hxw : 1+eps≤ x.re+w.re) :
    ∃C : ℝ,0≤ C ∧ ∀z : ℂ,(17/50:ℝ)≤ z.re →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤ C := by
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=> selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := HeckeReciprocalBound.bound 2*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  have hLb : 0≤ HeckeReciprocalBound.bound 2 := by unfold HeckeReciprocalBound.bound; positivity
  have hL : 0≤ L := by dsimp [L];positivity
  have hA (P : T) : 0≤ A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=> hA P)
  refine ⟨L*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro z hz
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤ HeckeReciprocalBound.bound 2 :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z hx hw hz hxw
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  rw [mul_assoc L]
  apply mul_le_mul _ (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hL
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (norm_nonneg _)) (norm_nonneg _)

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem physicalRow_first_x_growth (e eps : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤ l) (hlβ : HeckeZeroSupremum.beta+8*e≤ l)
    (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hlw : 1+eps≤ l+w.re) :
    ∃C : ℝ,0≤ C ∧ ∀x : ℂ,l≤ x.re → x.re≤ r →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤ C*(3+|x.im|)^2 := by
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e 1 he he' (by norm_num) (by norm_num) S hS.prime
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=> selectedFirstBound P.val.val.absNorm r
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖
  let B : ℝ := Cr*(η.modulus.absNorm:ℝ)*N
  have hL : 0≤ L := by dsimp [L];positivity
  have hB : 0≤ B := by dsimp [B,N];positivity
  have hA (P : T) : 0≤ A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=> hA P)
  refine ⟨L*B*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x hxl hxr
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤ B*(3+|x.im|)^2 := by
    simpa only [Real.rpow_one] using hr η u x (hlβ.trans hxl)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z (hl.trans hxl) hw hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) r x w z (hl.trans hxl) hxr
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  calc
    _ ≤ L*(B*(3+|x.im|)^2)*((Ch*N)*(∏P:T,A P)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrec hL)
        (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem calibrated_physicalRow_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+1/2) :
    ∃C : ℝ,0< C ∧ ∀w : ℂ,(1/2:ℝ)≤ w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤ C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) 1 (by norm_num) (by norm_num) S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>961*((P.val.val.absNorm:ℝ)^(1/2:ℝ)+1)
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*(Cn*N^(3/5+1:ℝ))*(Ch*N)*∏P:T,A P
  have hC : 0≤ C := by dsimp [C,L,A,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn u hu w hw
  have hh' := hh eps S hS hfirst T η u x w z (by linarith) (by linarith) hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    change (∏P:T,‖continuedCompensatedLocal η u P.val _ x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖)≤ _
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P _
    have hQ : (4:ℝ)≤ P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    apply (continuedCompensatedLocal_bound η u P.val _ hQ x w z hx hw hz).trans
    dsimp [A]
    by_cases hp : P.val.val∣Ideal.span {u.val}
    · rw [if_pos hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤ P.val.val.absNorm)
        (max_le (by linarith) (by norm_num) : max (1-w.re) 0≤(1/2:ℝ))).trans
      linarith
    · rw [if_neg hp]
      have hnq := Real.rpow_nonneg (show (0:ℝ)≤ P.val.val.absNorm by positivity) (1/2:ℝ)
      nlinarith
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
        ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [he,norm_mul,norm_mul,norm_mul]
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh'
  have hn'' : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w‖≤ Cn*N^(3/5+1:ℝ)*(3+|w.im|)^2 := hn'
  calc
    _ ≤ L*(Cn*N^(3/5+1:ℝ)*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      rw [norm_mul]
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [L,N];positivity)
      apply mul_le_mul _ hh'' (norm_nonneg _) (by dsimp [L,N];positivity)
      exact mul_le_mul_of_nonneg_left hn'' (by positivity)
    _ = C*(3+|w.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

lemma calibrated_physicalRow_first_w (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    DifferentiableAt ℂ (fun w=> star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z) w := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiableAt_const _
  · have hp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    apply DifferentiableAt.const_mul
    unfold physicalCompensatedRow continuedCompensatedRow
    apply DifferentiableAt.mul
    · exact ((HeckeOrigin.continued_differentiableAt _ (Or.inr hp)).const_mul _).mul_const _
    · apply DifferentiableAt.mul
      · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
          (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
          hx hw hz hxw).differentiableAt
      · apply DifferentiableAt.fun_finsetProd
        intro P hP
        exact (continuedCompensatedLocal_first_differentiable_w η u P.val _
          (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z
          (by linarith) (by linarith)) w

theorem contourTupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→HeckeIdealSeries.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

/-- Mellin kernel of a calibrated row, with the marked Euler factors continued analytically. -/
def continuedPhysicalRowKernel {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z x w z*
    (∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z)

theorem continuedPhysicalRowKernel_initial {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (t : ProbeMellinBoundary.HeightSpace) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)=
    compensatedRowOnLines η S (calibrationForSet S hmax)
      (fun i=> primaryIdealGenerator (P i).val) W0 W1 X Y Z ⟨u.val,u.property.1⟩ t := by
  unfold continuedPhysicalRowKernel physicalCompensatedRow compensatedRowOnLines
  rw [continuedCompensatedRow_eq_indexed S hS P hP hPS η u _ _ _
    (by norm_num) (by norm_num) (by norm_num)]
  ring

lemma sourceMellinWeight_differentiable_w (W0 W1 : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) :
    Differentiable ℂ (fun w=> sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hm : Differentiable ℂ (mellin W1) := fun w=>
    compact_source_mellin_differentiable W1 a b ha hW (W1.smooth (⊤:ℕ∞)) w
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hy)

theorem continuedPhysicalRowKernel_differentiableAt_w {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    DifferentiableAt ℂ (fun w=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) w := by
  exact (((sourceMellinWeight_differentiable_w W0 W1 a b ha hW X Y Z hY x z) w).mul_const _ |>.mul_const _).mul
    (calibrated_physicalRow_first_w eps heps S hS hfirst hmax _ (contourTupleOutside S P hPS) η u hu x w z hx hw hz hxw)

theorem nonprincipal_w_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) (l r T : ℝ)
    (hx : (51/100:ℝ)≤ x.re) (hl : -(1/100:ℝ)≤ l) (hr : -(1/100:ℝ)≤ r)
    (hz : (17/50:ℝ)≤ z.re) (hxl : 1+eps≤ x.re+l) (hxr : 1+eps≤ x.re+r) :
    let F := fun w=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun w=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro w hw
    have hwlo : min l r≤ w.re := hw.1.1
    have hw' : -(1/100:ℝ)≤ w.re := (le_min hl hr).trans hwlo
    have hxw : 1+eps≤ x.re+w.re := by
      have := (le_min (by linarith : 1+eps-x.re≤ l) (by linarith : 1+eps-x.re≤ r)).trans hwlo
      linarith
    exact (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
      W0 W1 a b ha hW X Y Z hY x w z hx hw' hz hxw).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

lemma reciprocal_differentiableAt_of_nonzero (χ : Character) (s : ℂ) (h0 : s≠0)
    (hnz : ¬(χ.residue=1 ∧ s=1) → LFunction χ s≠0) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal χ) s := by
  by_cases hχ : χ.residue=1
  · have hr : HeckeReciprocal.regularizedL χ s≠0 := by
      by_cases hs : s=1
      · subst s
        exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ
      · rw [HeckeReciprocal.regularizedL_eq χ h0 hs]
        exact mul_ne_zero (sub_ne_zero.mpr hs) (hnz (by simp [hs]))
    have he : HeckeReciprocal.reciprocal χ=(fun z=>(z-1)/HeckeReciprocal.regularizedL χ z) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,if_pos hχ]
    rw [he]
    exact (differentiableAt_id.sub_const 1).div
      (HeckeReciprocal.regularizedL_differentiableAt χ h0) hr
  · have he : HeckeReciprocal.reciprocal χ=(fun z=>(LFunction χ z)⁻¹) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,if_neg hχ]
    rw [he]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv (hnz (by simp [hχ]))

theorem physicalCompensatedRow_buffered_differentiableAt_x
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=> physicalCompensatedRow S hS T hT η u x w z) x := by
  have hx0 : x≠0 := by intro h;norm_num [h] at hx
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (reciprocal_differentiableAt_of_nonzero _ x hx0 hnz).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiable_x (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ) :
    Differentiable ℂ (fun x=> sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hz)

theorem continuedPhysicalRowKernel_buffered_differentiableAt_x {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) x :=
  (((sourceMellinWeight_differentiable_x W0 W1 X Y Z hZ w z) x).mul_const _ |>.mul_const _).mul
    ((physicalCompensatedRow_buffered_differentiableAt_x eps heps S hS hfirst _
      (contourTupleOutside S P hPS) η u x w z hx hw hz hxw hnz).const_mul _)

theorem buffered_x_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ) (l r T : ℝ)
    (hl : (51/100:ℝ)≤ l) (hr : (51/100:ℝ)≤ r) (hw : -(1/100:ℝ)≤ w.re)
    (hz : (17/50:ℝ)≤ z.re) (hlw : 1+eps≤ l+w.re) (hrw : 1+eps≤ r+w.re)
    (hnz : ∀x∈(uIcc l r ×ℂ uIcc (-T) T),
      ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
        LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    let F := fun x=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun x=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro x hx
    have hxlo : min l r≤ x.re := hx.1.1
    have hx' : (51/100:ℝ)≤ x.re := (le_min hl hr).trans hxlo
    have hxw : 1+eps≤ x.re+w.re := by
      have := (le_min (by linarith : 1+eps-w.re≤ l) (by linarith : 1+eps-w.re≤ r)).trans hxlo
      linarith
    exact (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hZ x w z hx' hw hz hxw (hnz x hx)).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

def rowKernelScalar {K : ℕ} (P : Fin K→HeckeIdealSeries.PrimeIdeal) (u : FreeRow)
    (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (x z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
    mellin (SchwartzPlanePoisson.paperRadialFourier W0) z*
    (∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_w_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      rowKernelScalar P u W0 X Z x z*(Y:ℂ)^(w-1)*mellin W1 w*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel rowKernelScalar sourceMellinWeight
  ring

theorem continuedPhysicalRowKernel_cauchy {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤ C)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    ∃B : ℝ,0≤ B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((v:ℂ)+t*I) z‖≤ B*cauchy t := by
  obtain ⟨D,hD,hm⟩ := compact_source_mellin_strip_decay W1 a b ha hW
    (W1.smooth ⊤) l r (N+2)
  have hscale := (scaleBound_pos Y (l-1) (r-1)).le
  let A := ‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*C
  refine ⟨A*D,by dsimp [A]; positivity,?_⟩
  intro v hv t
  have hYbd := cpow_le_scaleBound hY (((v:ℂ)+t*I)-1)
    (show (((v:ℂ)+t*I)-1).re∈Icc (l-1) (r-1) by simpa using hv)
  have hm' : height t^2*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖)≤ D := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using hm v hv t
  have hmc : height t^N*‖mellin W1 ((v:ℂ)+t*I)‖≤ D*cauchy t :=
    weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le N) (norm_nonneg _)) t hm'
  rw [continuedPhysicalRowKernel_w_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*
        ‖mellin W1 ((v:ℂ)+t*I)‖)*(C*height t^N) := by
      apply mul_le_mul _ (hpoly v hv t) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYbd (norm_nonneg _)) (norm_nonneg _)
    _ = A*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖) := by dsimp [A]; ring
    _ ≤ A*(D*cauchy t) := mul_le_mul_of_nonneg_left hmc (by dsimp [A]; positivity)
    _ = _ := by ring

theorem nonprincipal_w_integral_eq_of_polynomial {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤ C)
    (hlr : l≤ r) (hx : (51/100:ℝ)≤ x.re) (hl : -(1/100:ℝ)≤ l)
    (hz : (17/50:ℝ)≤ z.re) (hxl : 1+eps≤ x.re+l)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW
    X Y Z hY x z l r C N hC hpoly
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun w=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro w hw
  exact (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x w z hx (hl.trans hw.1) hz (by linarith [hw.1])).differentiableWithinAt

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma physicalRow_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) (hxw : 1+eps≤ x.re+1/2) :
    ∃C : ℝ,0< C ∧ ∀v : ℝ,(1/2:ℝ)≤ v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z hx hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by
    unfold height
    nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) (l r : ℝ) (hlr : l≤ r) (hl : (1/2:ℝ)≤ l)
    (hx : (7/8:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) (hxw : 1+eps≤ x.re+1/2) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z hx hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr (by linarith) (by linarith)
    hz (by linarith) (fun v hv t=> hbound v (hl.trans hv.1) t)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=> trivial⟩

def shiftedRowInner {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z l : ℝ) (q : ℝ×ℝ) : ℂ :=
  ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((3:ℂ)+q.1*I) ((l:ℂ)+t*I) ((2:ℂ)+q.2*I)

theorem rowIntegral_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (heps' : eps≤5/2)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (l : ℝ) (hl : (1/2:ℝ)≤ l) (hl3 : l≤3) :
    Integrable (shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l) (volume.prod volume) ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=> primaryIdealGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q ∂(volume.prod volume) := by
  let p : Fin K→O := fun i=> primaryIdealGenerator (P i).val
  have hp : ∀i,p i≠0 := fun i=>(supported_primeGenerator_prime (P i)
    (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=> Subtype.ext (congrArg (fun v : NonzeroFrequency=> v.val) h)
  have hF := compensatedRows_counting_product_integrable e he η S (calibrationForSet S hmax) p hp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hi : Integrable (compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u))
      heightMeasure := (Measure.ae_count_iff.mp hF.prod_right_ae) u
  have heq (q : ℝ×ℝ) :
      (∫t : ℝ,compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u) (q,t))=
        shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q := by
    have hs := nonprincipal_w_integral_eq eps heps S hS hfirst hmax P hPS η u hu W0 W1
      a1 b1 ha1 hW1 X Y Z hY ((3:ℂ)+q.1*I) ((2:ℂ)+q.2*I) l 3 hl3 hl
      (by norm_num) (by norm_num) (by norm_num;linarith)
    unfold shiftedRowInner
    rw [hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>(continuedPhysicalRowKernel_initial S hS hmax P hP hPS
      η u W0 W1 X Y Z (q,t)).symm)
  refine ⟨?_,?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall heq)
  · unfold rowIntegral
    rw [integral_prod _ hi]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall heq)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma continuedPhysicalRowKernel_eq_calibratedTuple {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (hW : ∀i,W i (((P i).val.absNorm:ℝ)/Yp i)=1) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      sourceMellinWeight W0 W1 X Y Z x w z*frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u P hPS W Yp x w z := by
  have hnorm (i : Fin K) : (elementNorm (primaryIdealGenerator (P i).val):ℂ)=
      (Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold continuedPhysicalRowKernel calibratedTupleValue
  simp only [hW,one_mul,hnorm]
  ring

theorem continuedPhysicalRowKernel_integrable {K : ℕ}
    (e σ υ r : ℝ) (he : 0< e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hr : (17/50:ℝ)≤ r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (fun p : HeightSpace=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  let W : Fin K→ℝ→ℂ := fun _ y=> if y=1 then 1 else 0
  let Yp : Fin K→ℝ := fun i=>(P i).val.absNorm
  let T : Fin K→Finset HeckeIdealSeries.PrimeIdeal := fun i=>{P i}
  have hT (i : Fin K) (Q : HeckeIdealSeries.PrimeIdeal) (hQ : Q∈T i) : Q.val∉S := by
    have heq : Q=P i := Finset.mem_singleton.mp hQ
    simpa only [heq] using hPS i
  let P0 : ∀i,T i := fun i=>⟨P i,Finset.mem_singleton_self _⟩
  have hTP (Q : ∀i,T i) : (fun i=>(Q i).val)=P := by
    funext i
    exact Finset.mem_singleton.mp (Q i).property
  have hdis (Q : ∀i,T i) : Function.Injective (fun i=>(Q i).val) := by rw [hTP Q];exact hP
  have hYp (i : Fin K) : 1≤ Yp i := by
    dsimp [Yp]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  have hWS (i : Fin K) : Function.support (W i)⊆Icc (1:ℝ) 1 := by
    intro y hy
    by_cases h : y=1
    · simpa only [h] using (show (1:ℝ)∈Icc 1 1 from ⟨le_rfl,le_rfl⟩)
    · simp [W,h,Function.mem_support] at hy
  have hWB (i : Fin K) (y : ℝ) : ‖W i y‖≤1 := by dsimp [W];split_ifs <;> simp
  have hWeq (i : Fin K) : W i (((P i).val.absNorm:ℝ)/Yp i)=1 := by
    have hn : Yp i≠0 := by linarith [hYp i]
    simp [W,Yp,div_self hn]
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  have hU : 1≤ U := by
    dsimp [U]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e (1/2) 1 1 r 1 σ υ he he'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by norm_num) hσ hσβ hυ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hR (v : FreeRow) (hv : v∈({u}:Finset FreeRow)) :
      v.val≠1 ∧ U≤((Ideal.span {v.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {v.val}:Ideal O).absNorm:ℝ)≤2*U := by
    have hvu := Finset.mem_singleton.mp hv
    subst v
    exact ⟨hu,le_rfl,by change U≤2*U;linarith⟩
  have hi := (hmain η U hU {u} hR T hT hdis Yp hYp W hWS hWB X Y Z hX hY hZ).1
  have hm := calibratedTupleValue_onLines_aestronglyMeasurable S hS hmax η u P hPS W Yp σ υ r heightMeasure
  have hfn : (elementNorm u.val:ℂ)≠0 := by
    exact_mod_cast (elementNorm_pos u.val u.property.1).ne'
  have hf : Continuous (fun p : HeightSpace=> frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩) := by
    unfold frequencyWeight
    exact (by fun_prop : Continuous (fun p : HeightSpace=>-((r:ℂ)+p.1.2*Complex.I))).const_cpow (Or.inl hfn)
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r υ (by linarith)
  have hme : AEStronglyMeasurable (fun p : HeightSpace=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
    simp_rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
    exact (hs.mul hf).aestronglyMeasurable.mul hm
  apply hi.mono' hme
  apply Filter.Eventually.of_forall
  intro p
  rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
  rw [mul_assoc,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  dsimp only [physicalDyadNorm]
  rw [Finset.sum_singleton]
  have hh := Finset.single_le_sum (fun Q (_ : Q∈(Finset.univ:Finset (∀i,T i)))=> norm_nonneg
    (frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩*
      calibratedTupleValue S hS hmax η u (fun i=>(Q i).val)
        (fun i=> hT i (Q i).val (Q i).property) W Yp ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I))) (Finset.mem_univ P0)
  exact hh

end ProbeHighRowFamily
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

lemma physicalCompensatedRow_first_z (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    DifferentiableAt ℂ (fun z=> physicalCompensatedRow S hS T hT η u x w z) z := by
  have hz0 : 6*z≠0 := by intro h;have hh:=congrArg Complex.re h;norm_num [Complex.mul_re] at hh;linarith
  have hz1 : 6*z≠1 := by intro h;have hh:=congrArg Complex.re h;norm_num [Complex.mul_re] at hh;linarith
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hz1)).comp z
      (differentiableAt_id.const_mul 6)).mul_const _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_z eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiableAt_z (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) (x w z : ℂ) (hz : 0< z.re) :
    DifferentiableAt ℂ (fun z=> sourceMellinWeight W0 W1 X Y Z x w z) z := by
  have hxc : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hzc : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hm := (ProbeRadialMellin.radial_mellin_analytic W0 z hz).differentiableAt
  unfold sourceMellinWeight
  fun_prop (disch := first | exact Or.inl hxc | exact Or.inl hzc)

theorem continuedPhysicalRowKernel_differentiableAt_z {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    DifferentiableAt ℂ (fun z=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z := by
  have hm := sourceMellinWeight_differentiableAt_z W0 W1 X Y Z hX hZ x w z (by linarith)
  have hp : Differentiable ℂ (fun z : ℂ=>∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(z-1)) := by
    apply Differentiable.fun_finsetProd
    intro i hi
    have hp0 := (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
    have hn : (elementNorm (primaryIdealGenerator (P i).val):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (elementNorm_pos _ hp0).ne'
    exact (differentiable_id.sub_const 1).const_cpow (Or.inl hn)
  have hNu : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hfreq : Differentiable ℂ (fun z=> frequencyWeight z ⟨u.val,u.property.1⟩) :=
    differentiable_id.neg.const_cpow (Or.inl hNu)
  exact ((hm.mul (hp z)).mul (hfreq z)).mul
    ((physicalCompensatedRow_first_z eps heps S hS hfirst _ (contourTupleOutside S P hPS) η u x w z hx hw hz hxw).const_mul _)

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

private lemma norm_mul_seven_le {a b c d e f g : ℂ} {A B C D E F G : ℝ}
    (ha : ‖a‖≤ A) (hb : ‖b‖≤ B) (hc : ‖c‖≤ C) (hd : ‖d‖≤ D)
    (he : ‖e‖≤ E) (hf : ‖f‖≤ F) (hg : ‖g‖≤ G) :
    ‖a*b*c*d*e*f*g‖≤ A*B*C*D*E*F*G := by
  have hA := (norm_nonneg a).trans ha
  have hB := (norm_nonneg b).trans hb
  have hC := (norm_nonneg c).trans hc
  have hD := (norm_nonneg d).trans hd
  have hE := (norm_nonneg e).trans he
  have hF := (norm_nonneg f).trans hf
  simp only [norm_mul]
  gcongr

def zRowScalar {K : ℕ} (P : Fin K→HeckeIdealSeries.PrimeIdeal) (u : FreeRow)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin W1 w*
    (∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_z_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      zRowScalar P u W1 X Y Z x w z*mellin (SchwartzPlanePoisson.paperRadialFourier W0) z*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel zRowScalar sourceMellinWeight
  ring

lemma zRowScalar_bounded {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (u : FreeRow)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (x w : ℂ) (l r : ℝ) (hl : 0< l) :
    ∃A : ℝ,0≤ A ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖zRowScalar P u W1 X Y Z x w ((v:ℂ)+t*I)‖≤ A := by
  let B : Fin K→ℝ := fun i=> scaleBound (elementNorm (primaryIdealGenerator (P i).val)) (l-1) (r-1)
  let A := scaleBound X (1/2-r) (1/2-l)*scaleBound Z (x.re+l-1) (x.re+r-1)*
    ‖(Y:ℂ)^(w-1)‖*Real.exp ((|x.re|+r+1)^2)*‖mellin W1 w‖*
    (∏i,B i)*scaleBound (elementNorm u.val) (-r) (-l)
  have hB (i : Fin K) : 0≤ B i := (scaleBound_pos _ _ _).le
  have hBP : 0≤∏i,B i := Finset.prod_nonneg (fun i _=> hB i)
  have hscale (a b c : ℝ) : 0≤ scaleBound a b c := (scaleBound_pos _ _ _).le
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro v hv t
  have hXb := cpow_le_scaleBound hX (1/2-((v:ℂ)+t*I))
    (show (1/2-((v:ℂ)+t*I)).re∈Icc (1/2-r) (1/2-l) by
      simpa using And.intro (sub_le_sub_left hv.2 (1/2)) (sub_le_sub_left hv.1 (1/2)))
  have hZb := cpow_le_scaleBound hZ (x+((v:ℂ)+t*I)-1)
    (show (x+((v:ℂ)+t*I)-1).re∈Icc (x.re+l-1) (x.re+r-1) by
      simpa using And.intro (by linarith [hv.1] : x.re+l-1≤ x.re+v-1)
        (by linarith [hv.2] : x.re+v-1≤ x.re+r-1))
  have hGb := gaussian_strip_norm_le x hl hv t
  have hPb : ‖∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((v:ℂ)+t*I)-1)‖≤∏i,B i := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro i hi
    apply cpow_le_scaleBound
      (elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)
    simpa using And.intro (sub_le_sub_right hv.1 1) (sub_le_sub_right hv.2 1)
  have hFb : ‖frequencyWeight (((v:ℂ)+t*I)) ⟨u.val,u.property.1⟩‖≤ scaleBound (elementNorm u.val) (-r) (-l) := by
    apply cpow_le_scaleBound (elementNorm_pos _ u.property.1)
    simpa using And.intro (neg_le_neg hv.2) (neg_le_neg hv.1)
  exact (norm_mul_seven_le hXb hZb le_rfl hGb le_rfl hPb hFb).trans (le_max_left A 0)

theorem continuedPhysicalRowKernel_z_cauchy {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0< a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) (x w : ℂ) (l r : ℝ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re)
    (hxw : 1+eps≤ x.re+w.re) (hl : (17/50:ℝ)≤ l) :
    ∃B : ℝ,0≤ B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((v:ℂ)+t*I)‖≤ B*cauchy t := by
  obtain ⟨A,hA,hscalar⟩ := zRowScalar_bounded S hS P hPS u W1 X Y Z hX hZ x w l r (by linarith)
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_z_bounded eps S hS hfirst _
    (contourTupleOutside S P hPS) η u x w hx hw hxw
  obtain ⟨D,hD,hm⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a b ha hW l r (by linarith) 2
  refine ⟨A*D*C,mul_nonneg (mul_nonneg hA hD.le) hC,?_⟩
  intro v hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w ((v:ℂ)+t*I)‖≤ C := by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans (hrow _ (by simpa using hl.trans hv.1))
  have hm' : ‖mellin (SchwartzPlanePoisson.paperRadialFourier W0) ((v:ℂ)+t*I)‖≤ D*cauchy t :=
    weighted_two_to_cauchy (norm_nonneg _) t (hm v hv t)
  rw [continuedPhysicalRowKernel_z_factor,norm_mul,norm_mul]
  calc
    _ ≤ A*(D*cauchy t)*C := mul_le_mul (mul_le_mul (hscalar v hv t) hm' (norm_nonneg _) hA)
      hr (norm_nonneg _) (mul_nonneg hA (mul_nonneg hD.le (cauchy_nonneg t)))
    _ = _ := by ring

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

theorem first_z_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) (x w : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re)
    (hxw : 1+eps≤ x.re+w.re) (hl : (17/50:ℝ)≤ l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_z_cauchy (eps/2) S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l r hx hw (by linarith) hl
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun z=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro z hz
  exact (continuedPhysicalRowKernel_differentiableAt_z eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hX hZ x w z hx hw (hl.trans hz.1) hxw).differentiableWithinAt

lemma first_z_vertical_integrable {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) (x w : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re)
    (hxw : 1+eps≤ x.re+w.re) (hl : (17/50:ℝ)≤ l) :
    Integrable (fun t : ℝ=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I)) := by
  obtain ⟨B,hB,hb⟩ := continuedPhysicalRowKernel_z_cauchy (eps/2) S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l l hx hw (by linarith) hl
  have hc : Continuous (fun t : ℝ=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuedPhysicalRowKernel_differentiableAt_z eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hX hZ x w ((l:ℂ)+t*I) hx hw (by simpa using hl) hxw).continuousAt.comp
        (f:=fun t : ℝ=>(l:ℂ)+t*I)
    fun_prop
  exact (cauchy_integrable.const_mul B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=> hb l ⟨le_rfl,le_rfl⟩ t))

theorem finite_rows_first_z_shift {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (F : Finset FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z) (x w : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re)
    (hxw : 1+eps≤ x.re+w.re) (hl : (17/50:ℝ)≤ l) :
    (∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  rw [integral_finsetSum F (fun u hu=> first_z_vertical_integrable eps heps S hS hfirst hmax P hPS η u
      W0 W1 a b ha hW X Y Z hX hZ x w l hx hw hxw hl),
    integral_finsetSum F (fun u hu=> first_z_vertical_integrable eps heps S hS hfirst hmax P hPS η u
      W0 W1 a b ha hW X Y Z hX hZ x w r hx hw hxw (hl.trans hlr))]
  exact Finset.sum_congr rfl (fun u hu=> first_z_integral_eq eps heps S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l r hlr hx hw hxw hl)

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

def xRowScalar {K : ℕ} (P : Fin K→HeckeIdealSeries.PrimeIdeal) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y : ℝ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Y:ℂ)^(w-1)*
    mellin (SchwartzPlanePoisson.paperRadialFourier W0) z*mellin W1 w*
    (∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_x_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      xRowScalar P u W0 W1 X Y w z*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel xRowScalar sourceMellinWeight
  ring

lemma coupled_gaussian_bound (z : ℂ) {l r v : ℝ} (hl : 0< l) (hv : v∈Icc l r) (t : ℝ) :
    ‖Complex.exp ((((v:ℂ)+t*I)+z-1)^2)‖≤
      Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)) := by
  rw [Complex.norm_exp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : ((((v:ℂ)+t*I)+z-1)^2).re=(v+z.re-1)^2-(t+z.im)^2 := by simp [pow_two]
  rw [hre]
  have hvp : 0< v := hl.trans_le hv.1
  have hA : |v+z.re-1|≤|z.re|+r+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le z.re,le_abs_self z.re,hv.2]
  have hh := pow_le_pow_left₀ (abs_nonneg (v+z.re-1)) hA 2
  rw [sq_abs] at hh
  linarith

theorem continuedPhysicalRowKernel_x_gaussian {K : ℕ}
    (e eps : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤ l) (hlβ : HeckeZeroSupremum.beta+8*e≤ l)
    (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hlw : 1+eps≤ l+w.re) :
    ∃B : ℝ,0≤ B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((v:ℂ)+t*I) w z‖≤
        B*Continuation.polynomialGaussian 2 (t+z.im) := by
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_x_growth e eps he he' S hS hfirst _
    (contourTupleOutside S P hPS) η u w z l r hl hlβ hw hz hlw
  let A := ‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1)*
    Real.exp ((|z.re|+r+1)^2)*C
  have hA : 0≤ A := by dsimp [A,scaleBound];positivity
  refine ⟨A*(2*(3+|z.im|)^2),by positivity,?_⟩
  intro v hv t
  have hZb := cpow_le_scaleBound hZ (((v:ℂ)+t*I)+z-1)
    (show (((v:ℂ)+t*I)+z-1).re∈Icc (l+z.re-1) (r+z.re-1) by
      simpa using And.intro (by linarith [hv.1] : l+z.re-1≤ v+z.re-1)
        (by linarith [hv.2] : v+z.re-1≤ r+z.re-1))
  have hgb := coupled_gaussian_bound z (by linarith : 0< l) hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u ((v:ℂ)+t*I) w z‖≤ C*(3+|t|)^2 := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
    simpa using hrow ((v:ℂ)+t*I) (by simpa using hv.1) (by simpa using hv.2)
  rw [continuedPhysicalRowKernel_x_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1))*
        (Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)))*(C*(3+|t|)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hZb (norm_nonneg _)) hgb
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (scaleBound_pos _ _ _).le))
        hr (norm_nonneg _) (by unfold scaleBound;positivity)
    _ = A*(3+|t|)^2*Real.exp (-((t+z.im)^2)) := by dsimp [A];ring
    _ ≤ A*(2*(3+|z.im|)^2*(1+|t+z.im|^2))*Real.exp (-((t+z.im)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Continuation.shifted_height_two t z.im) hA) (Real.exp_pos _).le
    _ = _ := by unfold Continuation.polynomialGaussian;ring

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem first_x_integral_eq {K : ℕ}
    (e eps : ℝ) (he : 0< e) (he' : e<1/1000) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hl : (51/100:ℝ)≤ l) (hlβ : HeckeZeroSupremum.beta+8*e≤ l)
    (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hlw : 1+eps≤ l+w.re) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((l:ℂ)+t*I) w z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((r:ℂ)+t*I) w z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_x_gaussian e (eps/2) he he' S hS hfirst hmax P hPS
    η u W0 W1 X Y Z hZ w z l r hl hlβ hw hz (by linarith)
  apply Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
    (fun x=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z.im 2 hlr _ hbound
  intro x hx
  apply (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hZ x w z (hl.trans hx.1) hw hz (by linarith [hx.1]) ?_).differentiableWithinAt
  intro hpole
  exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt _ (by linarith [hx.1]) (by tauto)

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma FirstTail.of_ge_one_fiftieth {S : Finset (Ideal O)} (h : FirstTail (1/4) S)
    {eps : ℝ} (heps : (1/50:ℝ)≤ eps) : FirstTail eps S := by
  refine ⟨by linarith,h.norm_four,?_⟩
  simpa only [firstPrimeDefectBound,min_eq_right heps,
    min_eq_right (by norm_num : (1/50:ℝ)≤1/4)] using h.small

private lemma height_integral_wxz (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫x : ℝ,∫z : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod _ hw

/-- The continued row kernel on three vertical Mellin contours. -/
def continuedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

theorem continuedRowOnLines_z_transport {K : ℕ}
    (e σ υ l r : ℝ) (he : 0< e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hl : (17/50:ℝ)≤ l) (hlr : l≤ r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ l p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi (q : ℝ) (hq : (17/50:ℝ)≤ q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable e σ υ q he he' hσ hσβ hυ hq S hS hmax hfirst P hP hPS η u hu
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wxz _ (hi l hl),height_integral_wxz _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tx
  exact first_z_integral_eq (1/4) (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 a0 b0 ha0 hW0
    X Y Z hX hZ ((σ:ℂ)+tx*I) ((υ:ℂ)+tw*I) l r hlr
    (by simp;linarith) (by simp;linarith) (by simp;linarith) hl

theorem rowIntegral_wz_transport {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (υ r : ℝ) (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤ r) (hr2 : r≤2) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=> primaryIdealGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤3 := by linarith [HeckeZeroSupremum.beta_le_one]
  have hi (q : ℝ) (hq : (17/50:ℝ)≤ q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable (1/2000) 3 υ q (by norm_num) (by norm_num) (by norm_num) hβ hυ hq
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_w_shift (1/2) (by norm_num) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hP hPS
    η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ hυ hυ3
  have hinner : (∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z υ q ∂(volume.prod volume))=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure :=
    (integral_prod _ (hi 2 (by norm_num))).symm
  have hz := continuedRowOnLines_z_transport (1/2000) 3 υ r 2 (by norm_num) (by norm_num)
    (by norm_num) hβ hυ hr hr2 S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  exact ⟨hi r hr,hphysical.trans (by rw [hinner,hz])⟩

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

private lemma height_integral_wzx (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫z : ℝ,∫x : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod_symm _ hw

theorem continuedRowOnLines_x_transport {K : ℕ}
    (e l r υ ξ : ℝ) (he : 0< e) (he' : e<1/1000)
    (hl : (7/8:ℝ)≤ l) (hlβ : HeckeZeroSupremum.beta+8*e≤ l) (hlr : l≤ r)
    (hυ : (1/2:ℝ)≤υ) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z l υ ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z r υ ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : l≤ q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z q υ ξ) heightMeasure :=
    continuedPhysicalRowKernel_integrable e q υ ξ he he' (hl.trans hq) (hlβ.trans hq) hυ hξ
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wzx _ (hi l le_rfl),height_integral_wzx _ (hi r hlr)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  exact first_x_integral_eq e (1/4) he he' (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 X Y Z hZ
    ((υ:ℂ)+tw*I) ((ξ:ℂ)+tz*I) l r hlr (by linarith) hlβ
    (by simp;linarith) (by simpa using hξ) (by simp;linarith)

theorem rowIntegral_source_lines {K : ℕ}
    (e σ υ r : ℝ) (he : 0< e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤ r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=> primaryIdealGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi := continuedPhysicalRowKernel_integrable e σ υ r he he' hσ hσβ hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_wz_transport S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ 2 hυ hυ3 (by norm_num) le_rfl
  have hβ3 : HeckeZeroSupremum.beta+8*e≤3 := hσβ.trans hσ3
  have hz : (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure := by
    by_cases hr2 : r≤2
    · exact continuedRowOnLines_z_transport e 3 υ r 2 he he' (by norm_num) hβ3 hυ hr hr2
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    · exact (continuedRowOnLines_z_transport e 3 υ 2 r he he' (by norm_num) hβ3 hυ (by norm_num) (le_of_not_ge hr2)
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).symm
  have hx := continuedRowOnLines_x_transport e σ 3 υ r he he' hσ hσβ hσ3 hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨hi,hphysical.trans (by rw [hx,hz])⟩

end ProbeHighRowFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators
namespace ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(1/6:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(23/48:ℝ))^((1/2:ℝ)-1))=Z^(β-11/16-79/800+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

lemma small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤ Z) (hU : 1≤ U)
    (hUsmall : U≤ Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(1/6:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(23/48:ℝ))^((1/2:ℝ)-1))≤ Z^(β-11/16-63/800+8*e) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤ Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-11/16-79/800+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1;ring

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0< Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(1/6:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(17/48:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(23/48:ℝ))^((2:ℝ)-1))=
      Z^((53/32:ℝ)+(13/16:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

end ProbeHighRowFamily
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

def absolutePhysicalDyadIntegral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) : ℝ :=
  ∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
      physicalDyadNorm S hS hmax η R T hT W Yp ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure

theorem small_physical_dyad_bound (K : ℕ) (e δ a b B : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0< a) (hb : 0< b) (hB : 0≤ B) (hβ : (7/8:ℝ)≤ HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (Z U : ℝ),1≤ Z → 1≤ U → U≤ Z^(1/100:ℝ) →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) le_rfl le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU hUsmall R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤ Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=> Z^(length i)) hYp W hWS hWB
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  have hscale := small_row_scale_bound Z U δ hZ hU hUsmall hδ.le hδ' length hl HeckeZeroSupremum.beta e
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(23/48:ℝ))^((1/2:ℝ)-1)) := hh
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*(U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(23/48:ℝ))^((1/2:ℝ)-1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

end ProbeHighRowFamily
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
