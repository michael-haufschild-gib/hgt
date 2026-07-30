import GaloisForLFunctions.HTGeometry.ComplexRealChannelIndependence
import GaloisForLFunctions.HilbertMetric.UnisolventEvaluation

/-!
# Cofinite Hilbert reconstruction for continuous real features

The real unisolvent theorem in `HilbertMetric` produces exact dual reconstruction from ordinary
linear independence, while continuous finite-support rigidity in `HTGeometry` preserves that
independence after every finite deletion of a perfect domain.  This module composes those existing
interfaces and records the resulting real positive-definite evaluation Gram.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped BigOperators

noncomputable section

/-- Real evaluation column on a square packet surviving a finite deletion. -/
def cofiniteRealEvaluationColumn
    {J X : Type*} [Fintype J] (u : J → X → ℝ) (F : Set X)
    (points : J → {x : X // x ∉ F}) (j : J) :
    EuclideanSpace ℝ J :=
  WithLp.toLp 2 fun row => u j (points row)

/-- Real evaluation Gram on a square packet surviving a finite deletion. -/
def cofiniteRealEvaluationGram
    {J X : Type*} [Fintype J] (u : J → X → ℝ) (F : Set X)
    (points : J → {x : X // x ∉ F}) :
    Matrix J J ℝ :=
  Matrix.gram ℝ (cofiniteRealEvaluationColumn u F points)

/-- Finite exact tagged-channel reconstruction phase for both real coordinates of arbitrary
complex coefficients. -/
def ComplexCoefficientRealChannelHilbertReconstruction
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ) : Prop :=
  ∃ (points : J × Bool → X × Bool)
      (dual : J × Bool → J × Bool → ℝ),
    Function.Injective points ∧
    (∀ q r, ∑ i, dual q i *
        complexCoefficientRealChannelFeature u r (points i) =
      if q = r then 1 else 0) ∧
    (∀ (a : J × Bool → ℝ) q,
      ∑ i, dual q i *
        (∑ r, a r * complexCoefficientRealChannelFeature u r (points i)) =
      a q) ∧
    (GaloisForLFunctions.HilbertMetric.realEvaluationGram
      (complexCoefficientRealChannelFeature u) points).PosDef ∧
    0 < (GaloisForLFunctions.HilbertMetric.realEvaluationGram
      (complexCoefficientRealChannelFeature u) points).det

/-- **Finite full-complex tagged-channel reconstruction.**  A finite complex-linearly independent
dictionary admits a square packet of tagged real/imaginary observations that exactly recovers both
real coordinates of every complex coefficient.  The doubled real feature dictionary has strict
Hilbert geometry and positive volume. -/
theorem
    exists_injective_complexCoefficientRealChannelHilbertReconstruction_of_linearIndependent
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ)
    (hlin : LinearIndependent ℂ u) :
    ∃ (points : J × Bool → X × Bool)
        (dual : J × Bool → J × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature u r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : J × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature u r (points i)) =
        a q) ∧
      (GaloisForLFunctions.HilbertMetric.realEvaluationGram
        (complexCoefficientRealChannelFeature u) points).PosDef ∧
      0 < (GaloisForLFunctions.HilbertMetric.realEvaluationGram
        (complexCoefficientRealChannelFeature u) points).det := by
  classical
  exact
    GaloisForLFunctions.HilbertMetric.exists_injective_realEvaluationHilbertReconstruction
      (complexCoefficientRealChannelFeature u)
      (linearIndependent_complexCoefficientRealChannelFeature_of_complex u hlin)

/-- **Finite full-complex reconstruction classification.**  Exact recovery of both real
coordinates of every complex coefficient exists exactly when the original complex dictionary is
linearly independent. -/
theorem complexCoefficientRealChannelHilbertReconstruction_iff_linearIndependent
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ) :
    ComplexCoefficientRealChannelHilbertReconstruction u ↔
      LinearIndependent ℂ u := by
  constructor
  · rintro ⟨points, dual, _hinj, _hdelta, hrecovery, _hgram, _hdet⟩
    apply (linearIndependent_complexCoefficientRealChannelFeature_iff_complex u).1
    exact
      GaloisForLFunctions.HilbertMetric.linearIndependent_of_dual_reconstruction
        (complexCoefficientRealChannelFeature u) points dual hrecovery
  · exact
      exists_injective_complexCoefficientRealChannelHilbertReconstruction_of_linearIndependent u

/-- **Continuous real cofinite Hilbert reconstruction.**  Every finite linearly independent
continuous real feature family on a perfect T₁ domain has, after any finite deletion, distinct
surviving nodes with exact real dual recovery, a positive-definite evaluation Gram, and positive
Hilbert volume. -/
theorem exists_injective_cofiniteRealEvaluationHilbertReconstruction_of_linearIndependent_of_continuous
    {J X : Type*} [Fintype J] [DecidableEq J]
    [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℝ) (hu : ∀ j, Continuous (u j))
    (hlin : LinearIndependent ℝ u) (F : Set X) (hF : F.Finite) :
    ∃ (points : J → {x : X // x ∉ F}) (dual : J → J → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0) ∧
      (∀ (a : J → ℝ) q,
        ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram u F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram u F points).det := by
  classical
  have hlinCompl :=
    linearIndependent_restrict_compl_of_continuous u hu hlin F hF
  simpa only [cofiniteRealEvaluationGram, cofiniteRealEvaluationColumn,
    GaloisForLFunctions.HilbertMetric.realEvaluationGram,
    GaloisForLFunctions.HilbertMetric.realEvaluationColumn] using!
    GaloisForLFunctions.HilbertMetric.exists_injective_realEvaluationHilbertReconstruction
      (fun j => fun x : {x : X // x ∉ F} => u j x) hlinCompl

/-- **Tail-to-real cofinite Hilbert bridge.** A finite complex family independent modulo finite
support admits exact tagged real/imaginary reconstruction after every finite tagged deletion, with
a positive-definite real Gram and positive Hilbert volume. This requires no topology or
continuity. -/
theorem exists_injective_cofiniteComplexRealChannelHilbertReconstruction_of_tailCoefficientIndependent
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ)
    (htail : TailCoefficientIndependent u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    ∃ (points : J → {sample : X × Bool // sample ∉ F})
        (dual : J → J → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexRealChannelFeature u r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : J → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexRealChannelFeature u r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexRealChannelFeature u) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexRealChannelFeature u) F points).det := by
  classical
  have hlin :=
    linearIndependent_complexRealChannelFeature_restrict_compl_of_tailCoefficientIndependent
      u htail F hF
  simpa only [cofiniteRealEvaluationGram, cofiniteRealEvaluationColumn,
    GaloisForLFunctions.HilbertMetric.realEvaluationGram,
    GaloisForLFunctions.HilbertMetric.realEvaluationColumn] using!
    GaloisForLFunctions.HilbertMetric.exists_injective_realEvaluationHilbertReconstruction
      (fun j => fun sample : {sample : X × Bool // sample ∉ F} =>
        complexRealChannelFeature u j sample) hlin

/-- Cofinite exact tagged-channel reconstruction phase for both real coordinates of arbitrary
complex coefficients. -/
def ComplexCoefficientRealChannelCofiniteHilbertReconstruction
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ) : Prop :=
  ∀ F : Set (X × Bool), F.Finite →
    ∃ (points : J × Bool → {sample : X × Bool // sample ∉ F})
        (dual : J × Bool → J × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature u r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : J × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            complexCoefficientRealChannelFeature u r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature u) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature u) F points).det

/-- **Cofinite full-complex tagged-channel reconstruction.**  Complex coefficient independence
modulo finite support yields exact recovery of both real coordinates of every complex coefficient
after any finite deletion of tagged observations.  This topology-free bridge doubles the feature
index and retains strict real Hilbert geometry. -/
theorem
    exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_tailCoefficientIndependent
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ)
    (htail : TailCoefficientIndependent u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    ∃ (points : J × Bool → {sample : X × Bool // sample ∉ F})
        (dual : J × Bool → J × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature u r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : J × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            complexCoefficientRealChannelFeature u r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature u) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature u) F points).det := by
  classical
  have hlin :=
    linearIndependent_complexCoefficientRealChannelFeature_restrict_compl_of_tailCoefficientIndependent
      u htail F hF
  simpa only [cofiniteRealEvaluationGram, cofiniteRealEvaluationColumn,
    GaloisForLFunctions.HilbertMetric.realEvaluationGram,
    GaloisForLFunctions.HilbertMetric.realEvaluationColumn] using!
    GaloisForLFunctions.HilbertMetric.exists_injective_realEvaluationHilbertReconstruction
      (fun index => fun sample : {sample : X × Bool // sample ∉ F} =>
        complexCoefficientRealChannelFeature u index sample) hlin

/-- **Universal cofinite full-complex classification.**  Exact tagged recovery of arbitrary
complex coefficients after every finite deletion is equivalent to complex coefficient
independence modulo finite support.  No topology or continuity is required in either direction. -/
theorem
    complexCoefficientRealChannelCofiniteHilbertReconstruction_iff_tailCoefficientIndependent
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ) :
    ComplexCoefficientRealChannelCofiniteHilbertReconstruction u ↔
      TailCoefficientIndependent u := by
  constructor
  · intro hphase c hsupp
    let F : Set (X × Bool) :=
      (fun x => (x, false)) '' {x | ∑ j, c j * u j x ≠ 0} ∪
      (fun x => (x, true)) '' {x | ∑ j, c j * u j x ≠ 0}
    have hF : F.Finite :=
      (hsupp.image fun x => (x, false)).union
        (hsupp.image fun x => (x, true))
    obtain ⟨points, dual, _hinj, _hdelta, hrecovery, _hgram, _hdet⟩ :=
      hphase F hF
    let q : J × Bool → ℝ :=
      fun index => if index.2 then (c index.1).im else (c index.1).re
    have hcomplex : ∀ i, ∑ j, c j * u j (points i).1.1 = 0 := by
      intro i
      apply not_ne_iff.mp
      intro hne
      apply (points i).property
      rcases hs : (points i).1 with ⟨x, channel⟩
      cases channel with
      | false =>
          have hx : ∑ j, c j * u j x ≠ 0 := by
            simpa [hs] using hne
          exact Or.inl ⟨x, hx, rfl⟩
      | true =>
          have hx : ∑ j, c j * u j x ≠ 0 := by
            simpa [hs] using hne
          exact Or.inr ⟨x, hx, rfl⟩
    have hzero :
        ∀ i, ∑ r, q r *
          complexCoefficientRealChannelFeature u r (points i) = 0 := by
      intro i
      rcases hs : (points i).1 with ⟨x, channel⟩
      cases channel with
      | false =>
          have hre := congrArg Complex.re (hcomplex i)
          convert! hre using 1
          simp [q, complexCoefficientRealChannelFeature, complexRealChannelFeature,
            Fintype.sum_prod_type, Complex.mul_re, Finset.sum_add_distrib, hs]
          ring
      | true =>
          have him := congrArg Complex.im (hcomplex i)
          convert! him using 1
          simp [q, complexCoefficientRealChannelFeature, complexRealChannelFeature,
            Fintype.sum_prod_type, Complex.mul_im, Finset.sum_add_distrib, hs]
          ring
    have hq : q = 0 := by
      funext r
      calc
        q r = ∑ i, dual r i *
            (∑ s, q s * complexCoefficientRealChannelFeature u s (points i)) :=
          (hrecovery q r).symm
        _ = 0 := by simp [hzero]
    funext j
    apply Complex.ext
    · have hj := congrFun hq (j, false)
      simpa [q] using hj
    · have hj := congrFun hq (j, true)
      simpa [q] using hj
  · intro htail
    exact
      exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_tailCoefficientIndependent
        u htail

/-- **Complex-to-real cofinite Hilbert bridge.**  Every finite complex-linearly independent
continuous family on a perfect T₁ domain admits, after any finite deletion of tagged real/imaginary
observations, exact real dual recovery, a positive-definite real evaluation Gram, and positive
Hilbert volume. -/
theorem exists_injective_cofiniteComplexRealChannelHilbertReconstruction_of_linearIndependent_of_continuous
    {J X : Type*} [Fintype J] [DecidableEq J]
    [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j))
    (hlin : LinearIndependent ℂ u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    ∃ (points : J → {sample : X × Bool // sample ∉ F})
        (dual : J → J → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexRealChannelFeature u r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : J → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexRealChannelFeature u r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexRealChannelFeature u) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexRealChannelFeature u) F points).det := by
  letI : PerfectSpace (X × Bool) := perfectSpace_prod_left X Bool
  exact
    exists_injective_cofiniteRealEvaluationHilbertReconstruction_of_linearIndependent_of_continuous
      (complexRealChannelFeature u)
      (continuous_complexRealChannelFeature u hu)
      (linearIndependent_complexRealChannelFeature_of_complex u hlin) F hF

/-- **Continuous full-complex tagged-channel bridge.**  Every finite complex-linearly independent
continuous family on a perfect T₁ domain admits exact recovery of arbitrary complex coefficient
vectors, represented by their doubled real coordinates, after any finite tagged deletion. -/
theorem
    exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_linearIndependent_of_continuous
    {J X : Type*} [Fintype J] [DecidableEq J]
    [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j))
    (hlin : LinearIndependent ℂ u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    ∃ (points : J × Bool → {sample : X × Bool // sample ∉ F})
        (dual : J × Bool → J × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature u r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : J × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            complexCoefficientRealChannelFeature u r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature u) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature u) F points).det := by
  have htail :=
    (tailCoefficientIndependent_iff_linearIndependent_of_continuous u hu).2 hlin
  exact
    exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_tailCoefficientIndependent
      u htail F hF

end

end GaloisForLFunctions.HTGeometry
