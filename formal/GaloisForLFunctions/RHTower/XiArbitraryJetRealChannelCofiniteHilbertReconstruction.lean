import GaloisForLFunctions.HTGeometry.ContinuousCofiniteRealHilbertReconstruction
import GaloisForLFunctions.RHTower.XiArbitraryJetCofiniteHilbertReconstruction

/-!
# Cofinite arbitrary-jet real-channel completed-Xi reconstruction

The existing arbitrary-jet theorem classifies complex linear independence by collisions in the
chosen derivative-order map.  Splitting literal Xi values into tagged real and imaginary channels
preserves that exact classification over `ℝ`.  Continuity and the real cofinite Hilbert bridge then
upgrade it to exact reconstruction after every finite deletion of the tagged domain `ℂ × Bool`.
-/

open scoped BigOperators ComplexOrder

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tagged real/imaginary observation of one member of an arbitrary completed-Xi derivative-order
dictionary. -/
def xiDerivativeOrderRealChannelFeature
    {d : ℕ} (order : Fin d → ℕ) (j : Fin d) (sample : ℂ × Bool) : ℝ :=
  match sample.2 with
  | false => (iteratedDeriv (order j) xi sample.1).re
  | true => (iteratedDeriv (order j) xi sample.1).im

/-- Every tagged real/imaginary observation in an arbitrary finite Xi derivative dictionary is
continuous. -/
theorem continuous_xiDerivativeOrderRealChannelFeature
    {d : ℕ} (order : Fin d → ℕ) :
    ∀ j, Continuous (xiDerivativeOrderRealChannelFeature order j) := by
  simpa [xiDerivativeOrderRealChannelFeature, complexRealChannelFeature,
    xiDerivativeOrderFamily] using
    continuous_complexRealChannelFeature
      (xiDerivativeOrderFamily order)
      (fun j => (differentiable_iteratedDeriv_of_entire
        xi_differentiable (order j)).continuous)

/-- The tagged real-channel dictionary has exactly the same collision law as the complex Xi
derivative dictionary: it is real-linearly independent precisely when all derivative orders are
distinct. -/
theorem linearIndependent_xiDerivativeOrderRealChannelFeature_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    LinearIndependent ℝ (xiDerivativeOrderRealChannelFeature order) ↔
      Function.Injective order := by
  constructor
  · intro hlin i j hij
    apply hlin.injective
    funext sample
    simp [xiDerivativeOrderRealChannelFeature, hij]
  · intro horder
    simpa [xiDerivativeOrderRealChannelFeature,
      complexRealChannelFeature, xiDerivativeOrderFamily] using
      linearIndependent_complexRealChannelFeature_of_complex
        (xiDerivativeOrderFamily order)
        ((linearIndependent_xiDerivativeOrderFamily_iff_injective
          order).2 horder)

/-- The exact derivative-order collision law persists after deleting any finite collection of
tagged real/imaginary measurements. -/
theorem linearIndependent_xiDerivativeOrderRealChannelFeature_on_compl_iff_injective
    {d : ℕ} (order : Fin d → ℕ)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    LinearIndependent ℝ
        (fun j => fun sample : {sample : ℂ × Bool // sample ∉ F} =>
          xiDerivativeOrderRealChannelFeature order j sample) ↔
      Function.Injective order := by
  constructor
  · intro hlin i j hij
    apply hlin.injective
    funext sample
    simp [xiDerivativeOrderRealChannelFeature, hij]
  · intro horder
    simpa [xiDerivativeOrderRealChannelFeature,
      complexRealChannelFeature, xiDerivativeOrderFamily] using
      linearIndependent_complexRealChannelFeature_restrict_compl_of_complex
        (xiDerivativeOrderFamily order)
        (fun j => (differentiable_iteratedDeriv_of_entire
          xi_differentiable (order j)).continuous)
        ((linearIndependent_xiDerivativeOrderFamily_iff_injective
          order).2 horder) F hF

/-- **Complex-tail/real-channel matroid connector.** Complex coefficient independence modulo every
finite support is equivalent to real tagged-channel independence after any prescribed finite
deletion. Thus changing scalar field, splitting values into real and imaginary observations, and
deleting finitely many tagged samples all preserve the derivative-order matroid. -/
theorem tailCoefficientIndependent_xiDerivativeOrderFamily_iff_realChannelFeature_on_compl
    {d : ℕ} (order : Fin d → ℕ)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    TailCoefficientIndependent (xiDerivativeOrderFamily order) ↔
      LinearIndependent ℝ
        (fun j => fun sample : {sample : ℂ × Bool // sample ∉ F} =>
          xiDerivativeOrderRealChannelFeature order j sample) := by
  rw [tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective,
    linearIndependent_xiDerivativeOrderRealChannelFeature_on_compl_iff_injective
      order F hF]

/-- Real Hilbert Gram of an arbitrary completed-Xi derivative-order dictionary on a finite tagged
real/imaginary sampling packet. -/
def xiDerivativeOrderRealChannelEvaluationGram
    {d : ℕ} (order : Fin d → ℕ) (points : Fin d → ℂ × Bool) :
    Matrix (Fin d) (Fin d) ℝ :=
  GaloisForLFunctions.HilbertMetric.realEvaluationGram
    (xiDerivativeOrderRealChannelFeature order) points

/-- Every collision-free derivative-order dictionary has one finite tagged real-channel packet
with exact dual recovery and strict real Hilbert geometry. -/
theorem exists_injective_xiDerivativeOrderRealChannelEvaluationHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order) :
    ∃ (points : Fin d → ℂ × Bool) (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiDerivativeOrderRealChannelFeature order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiDerivativeOrderRealChannelFeature order r (points i)) = a q) ∧
      (xiDerivativeOrderRealChannelEvaluationGram order points).PosDef ∧
      0 < (xiDerivativeOrderRealChannelEvaluationGram order points).det := by
  simpa only [xiDerivativeOrderRealChannelEvaluationGram] using
    GaloisForLFunctions.HilbertMetric.exists_injective_realEvaluationHilbertReconstruction
      (xiDerivativeOrderRealChannelFeature order)
      ((linearIndependent_xiDerivativeOrderRealChannelFeature_iff_injective
        order).2 horder)

/-- **Finite arbitrary-jet tagged-real classification.** Exact finite real-channel reconstruction
with strict Hilbert geometry exists exactly when the derivative-order dictionary is
collision-free. -/
theorem exists_injective_xiDerivativeOrderRealChannelEvaluationHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ × Bool) (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiDerivativeOrderRealChannelFeature order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiDerivativeOrderRealChannelFeature order r (points i)) = a q) ∧
      (xiDerivativeOrderRealChannelEvaluationGram order points).PosDef ∧
      0 < (xiDerivativeOrderRealChannelEvaluationGram order points).det) ↔
      Function.Injective order := by
  constructor
  · rintro ⟨points, dual, _hinj, _hdelta, hrecovery, _hgram, _hdet⟩
    apply
      (linearIndependent_xiDerivativeOrderRealChannelFeature_iff_injective
        order).1
    exact
      GaloisForLFunctions.HilbertMetric.linearIndependent_of_dual_reconstruction
        (xiDerivativeOrderRealChannelFeature order) points dual hrecovery
  · exact
      exists_injective_xiDerivativeOrderRealChannelEvaluationHilbertReconstruction
        order

/-- Complete cofinite real-channel Hilbert reconstruction phase of an arbitrary finite
completed-Xi derivative-order dictionary. -/
def XiDerivativeOrderRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) : Prop :=
  ∀ F : Set (ℂ × Bool), F.Finite →
    ∃ (points : Fin d → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiDerivativeOrderRealChannelFeature order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiDerivativeOrderRealChannelFeature order r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (xiDerivativeOrderRealChannelFeature order) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (xiDerivativeOrderRealChannelFeature order) F points).det

/-- Every collision-free derivative-order dictionary has exact real-channel reconstruction after
an arbitrary finite deletion, with a positive-definite Gram and positive Hilbert volume. -/
theorem exists_injective_xiDerivativeOrderRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ (points : Fin d → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiDerivativeOrderRealChannelFeature order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiDerivativeOrderRealChannelFeature order r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (xiDerivativeOrderRealChannelFeature order) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (xiDerivativeOrderRealChannelFeature order) F points).det := by
  simpa [xiDerivativeOrderRealChannelFeature,
    complexRealChannelFeature, xiDerivativeOrderFamily] using
    exists_injective_cofiniteComplexRealChannelHilbertReconstruction_of_linearIndependent_of_continuous
      (xiDerivativeOrderFamily order)
      (fun j => (differentiable_iteratedDeriv_of_entire
        xi_differentiable (order j)).continuous)
      ((linearIndependent_xiDerivativeOrderFamily_iff_injective
        order).2 horder) F hF

/-- **Cofinite arbitrary-jet real-channel classification.**  Exact dual recovery and strict real
Hilbert geometry survive every finite tagged-measurement deletion exactly when the derivative-order
dictionary is collision-free. -/
theorem xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    XiDerivativeOrderRealChannelCofiniteHilbertReconstruction order ↔
      Function.Injective order := by
  constructor
  · intro hrec
    obtain ⟨points, dual, _hinj, _hdelta, hrecovery, _hgram, _hdet⟩ :=
      hrec ∅ Set.finite_empty
    apply
      (linearIndependent_xiDerivativeOrderRealChannelFeature_iff_injective
        order).1
    exact
      GaloisForLFunctions.HilbertMetric.linearIndependent_of_dual_reconstruction
        (xiDerivativeOrderRealChannelFeature order)
        (fun i => (points i : ℂ × Bool)) dual hrecovery
  · intro horder F hF
    exact
      exists_injective_xiDerivativeOrderRealChannelCofiniteHilbertReconstruction
        order horder F hF

/-- **Finite/cofinite tagged-real arbitrary-jet connector.** One finite exact real-channel packet
exists exactly when such reconstruction survives every finite tagged deletion. -/
theorem exists_injective_xiDerivativeOrderRealChannelEvaluationHilbertReconstruction_iff_cofinite
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ × Bool) (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiDerivativeOrderRealChannelFeature order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiDerivativeOrderRealChannelFeature order r (points i)) = a q) ∧
      (xiDerivativeOrderRealChannelEvaluationGram order points).PosDef ∧
      0 < (xiDerivativeOrderRealChannelEvaluationGram order points).det) ↔
      XiDerivativeOrderRealChannelCofiniteHilbertReconstruction order := by
  calc
    _ ↔ Function.Injective order :=
      exists_injective_xiDerivativeOrderRealChannelEvaluationHilbertReconstruction_iff_injective
        order
    _ ↔ _ :=
      (xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective
        order).symm

/-- **Complex/real-channel cofinite connector.** Exact completed-Xi derivative reconstruction
survives every finite deletion of the complex sampling domain exactly when it survives every finite
deletion of the tagged real/imaginary sampling domain. Both interfaces therefore detect the same
intrinsic derivative-order collision phase. -/
theorem xiDerivativeOrderCofiniteHilbertReconstruction_iff_realChannel
    {d : ℕ} (order : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
        Function.Injective points ∧
        (∀ q r, ∑ i, dual q i * iteratedDeriv (order r) xi (points i) =
          if q = r then 1 else 0) ∧
        (∀ (a : Fin d → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * iteratedDeriv (order r) xi (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).det) ↔
      XiDerivativeOrderRealChannelCofiniteHilbertReconstruction order := by
  calc
    _ ↔ Function.Injective order :=
      xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective order
    _ ↔ _ :=
      (xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective
        order).symm

/-- **Finite-complex/cofinite-real connector.** One exact complex completed-Xi derivative packet
exists exactly when exact tagged real/imaginary reconstruction survives every finite deletion.
Thus changing scalar field and observation channel introduces no hypothesis beyond excluding
derivative-order collisions. -/
theorem exists_injective_xiDerivativeOrderEvaluationHilbertReconstruction_iff_realChannelCofinite
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * iteratedDeriv (order r) xi (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (order r) xi (points i)) = a q) ∧
      (xiDerivativeOrderEvaluationGram order points).PosDef ∧
      0 < (xiDerivativeOrderEvaluationGram order points).det) ↔
      XiDerivativeOrderRealChannelCofiniteHilbertReconstruction order := by
  calc
    _ ↔ Function.Injective order :=
      exists_injective_xiDerivativeOrderEvaluationHilbertReconstruction_iff
        order
    _ ↔ _ :=
      (xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective
        order).symm

/-- A collision-free arbitrary Xi derivative dictionary admits, after any finite tagged deletion,
one fixed surviving real-channel packet detecting every nonzero real coefficient vector while
carrying strict Hilbert geometry. -/
theorem exists_injective_xiDerivativeOrderRealChannelCofiniteUniversalDetector
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ points : Fin d → {sample : ℂ × Bool // sample ∉ F},
      Function.Injective points ∧
      (∀ a : Fin d → ℝ, a ≠ 0 →
        ∃ i, (∑ r, a r *
          xiDerivativeOrderRealChannelFeature order r (points i)) ≠ 0) ∧
      (cofiniteRealEvaluationGram
        (xiDerivativeOrderRealChannelFeature order) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (xiDerivativeOrderRealChannelFeature order) F points).det := by
  classical
  obtain ⟨points, dual, hinj, _hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiDerivativeOrderRealChannelCofiniteHilbertReconstruction
      order horder F hF
  refine ⟨points, hinj, ?_, hgram, hdet⟩
  intro a ha
  by_contra hdetect
  have hzero :
      ∀ i, ∑ r, a r *
        xiDerivativeOrderRealChannelFeature order r (points i) = 0 := by
    intro i
    by_contra hi
    exact hdetect ⟨i, hi⟩
  apply ha
  funext q
  calc
    a q = ∑ i, dual q i *
        (∑ r, a r *
          xiDerivativeOrderRealChannelFeature order r (points i)) :=
      (hrecovery a q).symm
    _ = 0 := by simp [hzero]

/-- Real Hilbert Gram of the doubled real-coordinate dictionary representing arbitrary complex
coefficients in a completed-Xi derivative family. -/
def xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram
    {d : ℕ} (order : Fin d → ℕ)
    (points : Fin d × Bool → ℂ × Bool) :
    Matrix (Fin d × Bool) (Fin d × Bool) ℝ :=
  GaloisForLFunctions.HilbertMetric.realEvaluationGram
    (complexCoefficientRealChannelFeature (xiDerivativeOrderFamily order)) points

/-- A collision-free derivative-order dictionary admits finite exact tagged-channel recovery of
both real coordinates of every complex coefficient, with strict real Hilbert geometry. -/
theorem
    exists_injective_xiDerivativeOrderComplexCoefficientRealChannelEvaluationHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order) :
    ∃ (points : Fin d × Bool → ℂ × Bool)
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i)) = a q) ∧
      (xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram
        order points).PosDef ∧
      0 < (xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram
        order points).det := by
  simpa only [xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram] using
    exists_injective_complexCoefficientRealChannelHilbertReconstruction_of_linearIndependent
      (xiDerivativeOrderFamily order)
      ((linearIndependent_xiDerivativeOrderFamily_iff_injective order).2 horder)

/-- **Finite full-complex arbitrary-jet classification.**  Finite tagged real/imaginary
observations recover arbitrary complex derivative coefficients exactly iff derivative orders do
not collide. -/
theorem
    exists_injective_xiDerivativeOrderComplexCoefficientRealChannelEvaluationHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ (points : Fin d × Bool → ℂ × Bool)
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i)) = a q) ∧
      (xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram
        order points).PosDef ∧
      0 < (xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram
        order points).det) ↔
      Function.Injective order := by
  change
    ComplexCoefficientRealChannelHilbertReconstruction
      (xiDerivativeOrderFamily order) ↔ Function.Injective order
  calc
    _ ↔ LinearIndependent ℂ (xiDerivativeOrderFamily order) :=
      complexCoefficientRealChannelHilbertReconstruction_iff_linearIndependent
        (xiDerivativeOrderFamily order)
    _ ↔ _ := linearIndependent_xiDerivativeOrderFamily_iff_injective order

/-- Complete cofinite tagged-channel reconstruction phase for arbitrary complex coefficients in a
finite completed-Xi derivative dictionary. -/
def XiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) : Prop :=
  ComplexCoefficientRealChannelCofiniteHilbertReconstruction
    (xiDerivativeOrderFamily order)

/-- Collision-free derivative orders admit full complex-coefficient tagged reconstruction after
every finite deletion. -/
theorem
    exists_injective_xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ (points : Fin d × Bool → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiDerivativeOrderFamily order)) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiDerivativeOrderFamily order)) F points).det :=
  exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_tailCoefficientIndependent
    (xiDerivativeOrderFamily order)
    ((tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective
      order).2 horder) F hF

/-- **Cofinite full-complex arbitrary-jet classification.**  Exact recovery of arbitrary complex
coefficients survives every finite tagged deletion exactly when derivative orders are distinct. -/
theorem
    xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    XiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction order ↔
      Function.Injective order := by
  calc
    _ ↔ TailCoefficientIndependent (xiDerivativeOrderFamily order) :=
      complexCoefficientRealChannelCofiniteHilbertReconstruction_iff_tailCoefficientIndependent
        (xiDerivativeOrderFamily order)
    _ ↔ _ := tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective order

/-- Finite and cofinite full-complex tagged-channel arbitrary-jet reconstruction have the same
collision phase. -/
theorem
    exists_injective_xiDerivativeOrderComplexCoefficientRealChannelEvaluationHilbertReconstruction_iff_cofinite
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ (points : Fin d × Bool → ℂ × Bool)
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiDerivativeOrderFamily order) r (points i)) = a q) ∧
      (xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram
        order points).PosDef ∧
      0 < (xiDerivativeOrderComplexCoefficientRealChannelEvaluationGram
        order points).det) ↔
      XiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction order := by
  calc
    _ ↔ Function.Injective order :=
      exists_injective_xiDerivativeOrderComplexCoefficientRealChannelEvaluationHilbertReconstruction_iff_injective
        order
    _ ↔ _ :=
      (xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
        order).symm

/-- Real-coefficient and full complex-coefficient tagged reconstruction detect exactly the same
arbitrary-jet collision phase. -/
theorem xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_complexCoefficient
    {d : ℕ} (order : Fin d → ℕ) :
    XiDerivativeOrderRealChannelCofiniteHilbertReconstruction order ↔
      XiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction order := by
  calc
    _ ↔ Function.Injective order :=
      xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective order
    _ ↔ _ :=
      (xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
        order).symm

/-- A collision-free arbitrary Xi derivative dictionary has one surviving tagged packet detecting
every nonzero complex coefficient vector through its doubled real coordinates. -/
theorem
    exists_injective_xiDerivativeOrderComplexCoefficientRealChannelCofiniteUniversalDetector
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ points : Fin d × Bool → {sample : ℂ × Bool // sample ∉ F},
      Function.Injective points ∧
      (∀ a : Fin d × Bool → ℝ, a ≠ 0 →
        ∃ i, (∑ r, a r * complexCoefficientRealChannelFeature
          (xiDerivativeOrderFamily order) r (points i)) ≠ 0) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiDerivativeOrderFamily order)) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiDerivativeOrderFamily order)) F points).det := by
  classical
  obtain ⟨points, dual, hinj, _hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction
      order horder F hF
  refine ⟨points, hinj, ?_, hgram, hdet⟩
  intro a ha
  by_contra hdetect
  have hzero :
      ∀ i, ∑ r, a r * complexCoefficientRealChannelFeature
        (xiDerivativeOrderFamily order) r (points i) = 0 := by
    intro i
    by_contra hi
    exact hdetect ⟨i, hi⟩
  apply ha
  funext q
  calc
    a q = ∑ i, dual q i *
        (∑ r, a r * complexCoefficientRealChannelFeature
          (xiDerivativeOrderFamily order) r (points i)) :=
      (hrecovery a q).symm
    _ = 0 := by simp [hzero]

end

end RHTower
