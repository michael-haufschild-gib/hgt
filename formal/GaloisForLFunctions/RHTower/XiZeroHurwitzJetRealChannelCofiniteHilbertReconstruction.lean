import GaloisForLFunctions.HTGeometry.ContinuousCofiniteRealHilbertReconstruction
import GaloisForLFunctions.RHTower.XiZeroHurwitzJetFiniteCofiniteHilbertPhase

/-!
# Cofinite real-channel Xi-zero Hurwitz jet reconstruction

Xi-zero Hurwitz jets are not globally continuous on the complex shift plane, so a global
continuity argument would impose a false interface.  Their existing upper-end theorem supplies the
stronger fact needed here: every collision-free finite jet dictionary is independent modulo finite
complex support.

The generic HTGeometry tail-to-tagged-channel bridge converts that tail independence into real
linear independence after arbitrary finite deletion of real/imaginary observations.  The generic
real Hilbert theorem then gives exact reconstruction, a positive-definite Gram, and positive
volume.  The result has the same exact support/order collision phase as the existing complex finite
and cofinite interfaces.
-/

open scoped BigOperators ComplexOrder

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tagged real/imaginary observation of one Xi-zero Hurwitz jet. -/
def xiZeroHurwitzJetRealChannelFeature
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (j : Fin d) (sample : ℂ × Bool) : ℝ :=
  complexRealChannelFeature (xiZeroHurwitzJetFamily ρ order) j sample

/-- The tagged real-channel Xi-zero Hurwitz jet dictionary is linearly independent exactly when
its intrinsic support/order labels do not collide. -/
theorem linearIndependent_xiZeroHurwitzJetRealChannelFeature_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    LinearIndependent ℝ (xiZeroHurwitzJetRealChannelFeature ρ order) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · intro hlin i j hij
    have hρ : ρ i = ρ j := congrArg Prod.fst hij
    have horder : order i = order j := congrArg Prod.snd hij
    apply hlin.injective
    funext sample
    simp [xiZeroHurwitzJetRealChannelFeature, complexRealChannelFeature,
      xiZeroHurwitzJetFamily, hρ, horder]
  · intro hindex
    simpa only [xiZeroHurwitzJetRealChannelFeature] using
      linearIndependent_complexRealChannelFeature_of_complex
        (xiZeroHurwitzJetFamily ρ order)
        ((linearIndependent_xiZeroHurwitzJetFamily_iff_injective
          ρ order).2 hindex)

/-- Complex tail independence and tagged real-channel independence after any finite deletion have
the same intrinsic support/order collision law. -/
theorem linearIndependent_xiZeroHurwitzJetRealChannelFeature_on_compl_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    LinearIndependent ℝ
        (fun j => fun sample : {sample : ℂ × Bool // sample ∉ F} =>
          xiZeroHurwitzJetRealChannelFeature ρ order j sample) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · intro hlin i j hij
    have hρ : ρ i = ρ j := congrArg Prod.fst hij
    have horder : order i = order j := congrArg Prod.snd hij
    apply hlin.injective
    funext sample
    simp [xiZeroHurwitzJetRealChannelFeature, complexRealChannelFeature,
      xiZeroHurwitzJetFamily, hρ, horder]
  · intro hindex
    simpa only [xiZeroHurwitzJetRealChannelFeature] using
      linearIndependent_complexRealChannelFeature_restrict_compl_of_tailCoefficientIndependent
        (xiZeroHurwitzJetFamily ρ order)
        ((tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective
          ρ order).2 hindex) F hF

/-- Complex coefficient independence modulo finite support is equivalent to real tagged-channel
independence after any prescribed finite deletion. -/
theorem tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_realChannelFeature_on_compl
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    TailCoefficientIndependent (xiZeroHurwitzJetFamily ρ order) ↔
      LinearIndependent ℝ
        (fun j => fun sample : {sample : ℂ × Bool // sample ∉ F} =>
          xiZeroHurwitzJetRealChannelFeature ρ order j sample) := by
  rw [tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective,
    linearIndependent_xiZeroHurwitzJetRealChannelFeature_on_compl_iff_injective
      ρ order F hF]

/-- Real Hilbert Gram of an arbitrary Xi-zero Hurwitz jet dictionary on a finite tagged sampling
packet. -/
def xiZeroHurwitzJetRealChannelEvaluationGram
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (points : Fin d → ℂ × Bool) : Matrix (Fin d) (Fin d) ℝ :=
  GaloisForLFunctions.HilbertMetric.realEvaluationGram
    (xiZeroHurwitzJetRealChannelFeature ρ order) points

/-- Every collision-free Xi-zero Hurwitz jet dictionary has one finite tagged real-channel packet
with exact dual recovery and strict real Hilbert geometry. -/
theorem exists_injective_xiZeroHurwitzJetRealChannelEvaluationHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (hindex : Function.Injective (xiZeroHurwitzJetIndex ρ order)) :
    ∃ (points : Fin d → ℂ × Bool) (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiZeroHurwitzJetRealChannelFeature ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiZeroHurwitzJetRealChannelFeature ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).det := by
  simpa only [xiZeroHurwitzJetRealChannelEvaluationGram] using
    GaloisForLFunctions.HilbertMetric.exists_injective_realEvaluationHilbertReconstruction
      (xiZeroHurwitzJetRealChannelFeature ρ order)
      ((linearIndependent_xiZeroHurwitzJetRealChannelFeature_iff_injective
        ρ order).2 hindex)

/-- **Finite tagged-real Xi-zero Hurwitz classification.** Exact finite real-channel
reconstruction with strict Hilbert geometry exists exactly when the support/order dictionary is
collision-free. -/
theorem exists_injective_xiZeroHurwitzJetRealChannelEvaluationHilbertReconstruction_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ × Bool) (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiZeroHurwitzJetRealChannelFeature ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiZeroHurwitzJetRealChannelFeature ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).det) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · rintro ⟨points, dual, _hinj, _hdelta, hrecovery, _hgram, _hdet⟩
    apply
      (linearIndependent_xiZeroHurwitzJetRealChannelFeature_iff_injective
        ρ order).1
    exact
      GaloisForLFunctions.HilbertMetric.linearIndependent_of_dual_reconstruction
        (xiZeroHurwitzJetRealChannelFeature ρ order) points dual hrecovery
  · exact
      exists_injective_xiZeroHurwitzJetRealChannelEvaluationHilbertReconstruction
        ρ order

/-- Exact cofinite tagged real-channel reconstruction phase of an arbitrary finite Xi-zero
Hurwitz jet dictionary. -/
def XiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) : Prop :=
  ∀ F : Set (ℂ × Bool), F.Finite →
    ∃ (points : Fin d → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiZeroHurwitzJetRealChannelFeature ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiZeroHurwitzJetRealChannelFeature ρ order r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (xiZeroHurwitzJetRealChannelFeature ρ order) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (xiZeroHurwitzJetRealChannelFeature ρ order) F points).det

/-- Every collision-free Xi-zero Hurwitz jet dictionary has exact tagged real-channel
reconstruction after an arbitrary finite deletion, with strict real Hilbert geometry. -/
theorem exists_injective_xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (hindex : Function.Injective (xiZeroHurwitzJetIndex ρ order))
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ (points : Fin d → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiZeroHurwitzJetRealChannelFeature ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiZeroHurwitzJetRealChannelFeature ρ order r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (xiZeroHurwitzJetRealChannelFeature ρ order) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (xiZeroHurwitzJetRealChannelFeature ρ order) F points).det := by
  simpa only [xiZeroHurwitzJetRealChannelFeature] using
    exists_injective_cofiniteComplexRealChannelHilbertReconstruction_of_tailCoefficientIndependent
      (xiZeroHurwitzJetFamily ρ order)
      ((tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective
        ρ order).2 hindex) F hF

/-- **Cofinite real-channel Xi-zero Hurwitz jet classification.** Exact tagged real reconstruction
and strict Hilbert geometry survive every finite deletion exactly when the support/order dictionary
is collision-free. -/
theorem xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    XiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction ρ order ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · intro hrec
    obtain ⟨points, dual, _hinj, _hdelta, hrecovery, _hgram, _hdet⟩ :=
      hrec ∅ Set.finite_empty
    apply
      (linearIndependent_xiZeroHurwitzJetRealChannelFeature_iff_injective
        ρ order).1
    exact
      GaloisForLFunctions.HilbertMetric.linearIndependent_of_dual_reconstruction
        (xiZeroHurwitzJetRealChannelFeature ρ order)
        (fun i => (points i : ℂ × Bool)) dual hrecovery
  · intro hindex F hF
    exact
      exists_injective_xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction
        ρ order hindex F hF

/-- **Finite/cofinite tagged-real Xi-zero Hurwitz connector.** One finite exact real-channel
packet exists exactly when such reconstruction survives every finite tagged deletion. -/
theorem exists_injective_xiZeroHurwitzJetRealChannelEvaluationHilbertReconstruction_iff_cofinite
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ × Bool) (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiZeroHurwitzJetRealChannelFeature ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiZeroHurwitzJetRealChannelFeature ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).det) ↔
      XiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction ρ order := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      exists_injective_xiZeroHurwitzJetRealChannelEvaluationHilbertReconstruction_iff_injective
        ρ order
    _ ↔ _ :=
      (xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction_iff_injective
        ρ order).symm

/-- **Finite complex/real Xi-zero Hurwitz connector.** Exact finite reconstruction is invariant
under replacing complex observations by tagged real/imaginary observations. -/
theorem exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff_realChannelFinite
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetEvaluationGram ρ order points).det) ↔
    (∃ (points : Fin d → ℂ × Bool) (dual : Fin d → Fin d → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiZeroHurwitzJetRealChannelFeature ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiZeroHurwitzJetRealChannelFeature ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetRealChannelEvaluationGram ρ order points).det) := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff
        ρ order
    _ ↔ _ :=
      (exists_injective_xiZeroHurwitzJetRealChannelEvaluationHilbertReconstruction_iff_injective
        ρ order).symm

/-- **Complex/real cofinite Xi-zero Hurwitz connector.** Exact reconstruction survives every
finite complex deletion exactly when tagged real reconstruction survives every finite tagged
deletion. Both interfaces detect the same support/order collision phase. -/
theorem xiZeroHurwitzJetCofiniteHilbertReconstruction_iff_realChannel
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
        Function.Injective points ∧
        (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
          if q = r then 1 else 0) ∧
        (∀ (a : Fin d → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiZeroHurwitzJetFamily ρ order) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiZeroHurwitzJetFamily ρ order) F points).det) ↔
      XiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction ρ order := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      xiZeroHurwitzJetCofiniteHilbertReconstruction_iff_injective ρ order
    _ ↔ _ :=
      (xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction_iff_injective
        ρ order).symm

/-- **Finite-complex/cofinite-real Xi-zero Hurwitz connector.** One finite exact complex packet
exists exactly when tagged real reconstruction survives every finite tagged deletion. -/
theorem exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff_realChannelCofinite
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetEvaluationGram ρ order points).det) ↔
      XiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction ρ order := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff
        ρ order
    _ ↔ _ :=
      (xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction_iff_injective
        ρ order).symm

/-- Real Hilbert Gram of the doubled real-coordinate dictionary representing arbitrary complex
coefficients in a Xi-zero Hurwitz jet family. -/
def xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (points : Fin d × Bool → ℂ × Bool) :
    Matrix (Fin d × Bool) (Fin d × Bool) ℝ :=
  GaloisForLFunctions.HilbertMetric.realEvaluationGram
    (complexCoefficientRealChannelFeature
      (xiZeroHurwitzJetFamily ρ order)) points

/-- A collision-free Xi-zero Hurwitz jet dictionary admits finite tagged-channel recovery of both
real coordinates of every complex coefficient. -/
theorem
    exists_injective_xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (hindex : Function.Injective (xiZeroHurwitzJetIndex ρ order)) :
    ∃ (points : Fin d × Bool → ℂ × Bool)
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i)) = a q) ∧
      (xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram
        ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram
        ρ order points).det := by
  simpa only [xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram] using
    exists_injective_complexCoefficientRealChannelHilbertReconstruction_of_linearIndependent
      (xiZeroHurwitzJetFamily ρ order)
      ((linearIndependent_xiZeroHurwitzJetFamily_iff_injective
        ρ order).2 hindex)

/-- **Finite full-complex Xi-zero Hurwitz classification.**  Exact tagged recovery of arbitrary
complex coefficients exists exactly when support/order labels do not collide. -/
theorem
    exists_injective_xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationHilbertReconstruction_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ (points : Fin d × Bool → ℂ × Bool)
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i)) = a q) ∧
      (xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram
        ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram
        ρ order points).det) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  change
    ComplexCoefficientRealChannelHilbertReconstruction
      (xiZeroHurwitzJetFamily ρ order) ↔
        Function.Injective (xiZeroHurwitzJetIndex ρ order)
  calc
    _ ↔ LinearIndependent ℂ (xiZeroHurwitzJetFamily ρ order) :=
      complexCoefficientRealChannelHilbertReconstruction_iff_linearIndependent
        (xiZeroHurwitzJetFamily ρ order)
    _ ↔ _ := linearIndependent_xiZeroHurwitzJetFamily_iff_injective ρ order

/-- Complete cofinite tagged-channel reconstruction phase for arbitrary complex coefficients in a
finite Xi-zero Hurwitz jet dictionary. -/
def XiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) : Prop :=
  ComplexCoefficientRealChannelCofiniteHilbertReconstruction
    (xiZeroHurwitzJetFamily ρ order)

/-- Collision-free support/order labels admit full complex-coefficient tagged reconstruction after
every finite deletion, without a continuity hypothesis. -/
theorem
    exists_injective_xiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (hindex : Function.Injective (xiZeroHurwitzJetIndex ρ order))
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ (points : Fin d × Bool → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiZeroHurwitzJetFamily ρ order)) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiZeroHurwitzJetFamily ρ order)) F points).det :=
  exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_tailCoefficientIndependent
    (xiZeroHurwitzJetFamily ρ order)
    ((tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective
      ρ order).2 hindex) F hF

/-- **Cofinite full-complex Xi-zero Hurwitz classification.**  Exact tagged recovery of arbitrary
complex coefficients survives every finite deletion exactly off the support/order collision
locus. -/
theorem
    xiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    XiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction ρ order ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  calc
    _ ↔ TailCoefficientIndependent (xiZeroHurwitzJetFamily ρ order) :=
      complexCoefficientRealChannelCofiniteHilbertReconstruction_iff_tailCoefficientIndependent
        (xiZeroHurwitzJetFamily ρ order)
    _ ↔ _ :=
      tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective ρ order

/-- Finite and cofinite full-complex Xi-zero Hurwitz reconstruction have the same support/order
collision phase. -/
theorem
    exists_injective_xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationHilbertReconstruction_iff_cofinite
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ (points : Fin d × Bool → ℂ × Bool)
        (dual : Fin d × Bool → Fin d × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiZeroHurwitzJetFamily ρ order) r (points i)) = a q) ∧
      (xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram
        ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationGram
        ρ order points).det) ↔
      XiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction
        ρ order := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      exists_injective_xiZeroHurwitzJetComplexCoefficientRealChannelEvaluationHilbertReconstruction_iff_injective
        ρ order
    _ ↔ _ :=
      (xiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
        ρ order).symm

/-- Real-coefficient and full complex-coefficient tagged Xi-zero Hurwitz reconstruction detect
exactly the same support/order collision phase. -/
theorem xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction_iff_complexCoefficient
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    XiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction ρ order ↔
      XiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction
        ρ order := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      xiZeroHurwitzJetRealChannelCofiniteHilbertReconstruction_iff_injective
        ρ order
    _ ↔ _ :=
      (xiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
        ρ order).symm

/-- A collision-free Xi-zero Hurwitz jet dictionary has one surviving tagged packet detecting
every nonzero complex coefficient vector through its doubled real coordinates. -/
theorem
    exists_injective_xiZeroHurwitzJetComplexCoefficientRealChannelCofiniteUniversalDetector
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (hindex : Function.Injective (xiZeroHurwitzJetIndex ρ order))
    (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ points : Fin d × Bool → {sample : ℂ × Bool // sample ∉ F},
      Function.Injective points ∧
      (∀ a : Fin d × Bool → ℝ, a ≠ 0 →
        ∃ i, (∑ r, a r * complexCoefficientRealChannelFeature
          (xiZeroHurwitzJetFamily ρ order) r (points i)) ≠ 0) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiZeroHurwitzJetFamily ρ order)) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiZeroHurwitzJetFamily ρ order)) F points).det := by
  classical
  obtain ⟨points, dual, hinj, _hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiZeroHurwitzJetComplexCoefficientRealChannelCofiniteHilbertReconstruction
      ρ order hindex F hF
  refine ⟨points, hinj, ?_, hgram, hdet⟩
  intro a ha
  by_contra hdetect
  have hzero :
      ∀ i, ∑ r, a r * complexCoefficientRealChannelFeature
        (xiZeroHurwitzJetFamily ρ order) r (points i) = 0 := by
    intro i
    by_contra hi
    exact hdetect ⟨i, hi⟩
  apply ha
  funext q
  calc
    a q = ∑ i, dual q i *
        (∑ r, a r * complexCoefficientRealChannelFeature
          (xiZeroHurwitzJetFamily ρ order) r (points i)) :=
      (hrecovery a q).symm
    _ = 0 := by simp [hzero]

end

end RHTower
