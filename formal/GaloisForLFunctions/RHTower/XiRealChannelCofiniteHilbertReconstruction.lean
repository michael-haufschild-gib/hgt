import GaloisForLFunctions.RHTower.XiArbitraryJetRealChannelCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiJetFreeness

/-!
# Cofinite real-channel completed-Xi Hilbert reconstruction

`XiJetFreeness` already proves real linear independence and finite exact reconstruction for the
first completed-Xi derivatives observed through tagged real/imaginary channels.  The tagged domain
`ℂ × Bool` is perfect because its complex factor is perfect.  Continuity therefore connects that
finite result to the real cofinite Hilbert bridge: arbitrary finite sets of tagged measurements may
be removed without losing exact recovery or strict Gram geometry.
-/

open scoped BigOperators

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every tagged real/imaginary observation of a finite initial completed-Xi jet is continuous. -/
theorem continuous_xiInitialJetRealChannelFeature (n : ℕ) :
    ∀ j, Continuous (xiInitialJetRealChannelFeature n j) := by
  simpa only [xiInitialJetRealChannelFeature,
    xiDerivativeOrderRealChannelFeature] using!
    continuous_xiDerivativeOrderRealChannelFeature
      (fun j : Fin (n + 1) => (j : ℕ))

/-- Removing an arbitrary finite collection of tagged real/imaginary measurements preserves real
linear independence of the first completed-Xi derivatives. -/
theorem linearIndependent_xiInitialJetRealChannelFeature_on_compl
    (n : ℕ) (F : Set (ℂ × Bool)) (hF : F.Finite) :
    LinearIndependent ℝ
      (fun j => fun sample : {sample : ℂ × Bool // sample ∉ F} =>
        xiInitialJetRealChannelFeature n j sample) := by
  simpa only [xiInitialJetRealChannelFeature,
    xiDerivativeOrderRealChannelFeature] using!
    (linearIndependent_xiDerivativeOrderRealChannelFeature_on_compl_iff_injective
      (fun j : Fin (n + 1) => (j : ℕ)) F hF).2 Fin.val_injective

/-- The generic real cofinite evaluation Gram is definitionally the existing completed-Xi
real-channel evaluation Gram on the underlying surviving tagged nodes. -/
theorem cofiniteRealEvaluationGram_xiInitialJetRealChannel
    (n : ℕ) (F : Set (ℂ × Bool))
    (points : Fin (n + 1) → {sample : ℂ × Bool // sample ∉ F}) :
    cofiniteRealEvaluationGram
        (xiInitialJetRealChannelFeature n) F points =
      xiInitialJetRealChannelEvaluationGram n
        (fun i => (points i : ℂ × Bool)) :=
  rfl

/-- **Cofinite real-channel completed-Xi reconstruction.**  After deleting any finite collection
of tagged real/imaginary measurements, one distinct surviving packet exactly recovers every real
coefficient vector and carries the existing positive-definite Xi real-channel Gram with positive
volume. -/
theorem exists_injective_xiInitialJetRealChannelCofiniteHilbertReconstruction
    (n : ℕ) (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ (points : Fin (n + 1) → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin (n + 1) → Fin (n + 1) → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          xiInitialJetRealChannelFeature n r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 1) → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiInitialJetRealChannelFeature n r (points i)) = a q) ∧
      (xiInitialJetRealChannelEvaluationGram n
        (fun i => (points i : ℂ × Bool))).PosDef ∧
      0 < (xiInitialJetRealChannelEvaluationGram n
        (fun i => (points i : ℂ × Bool))).det := by
  obtain ⟨points, dual, hinj, hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiDerivativeOrderRealChannelCofiniteHilbertReconstruction
      (fun j : Fin (n + 1) => (j : ℕ)) Fin.val_injective F hF
  refine ⟨points, dual, hinj, ?_, ?_, ?_, ?_⟩
  · simpa only [xiInitialJetRealChannelFeature,
      xiDerivativeOrderRealChannelFeature] using! hdelta
  · simpa only [xiInitialJetRealChannelFeature,
      xiDerivativeOrderRealChannelFeature] using! hrecovery
  · simpa only [xiInitialJetRealChannelFeature,
      xiDerivativeOrderRealChannelFeature,
      cofiniteRealEvaluationGram_xiInitialJetRealChannel] using! hgram
  · simpa only [xiInitialJetRealChannelFeature,
      xiDerivativeOrderRealChannelFeature,
      cofiniteRealEvaluationGram_xiInitialJetRealChannel] using! hdet

/-- **Finite/cofinite initial-jet tagged-real connector.** One finite exact real-channel packet
exists exactly when exact reconstruction survives every finite deletion of tagged observations. -/
theorem exists_injective_xiInitialJetRealChannelEvaluationHilbertReconstruction_iff_cofinite
    (n : ℕ) :
    (∃ (nodes : Fin (n + 1) → ℂ × Bool)
        (dual : Fin (n + 1) → Fin (n + 1) → ℝ),
      Function.Injective nodes ∧
      (∀ q r, ∑ i, dual q i *
          xiInitialJetRealChannelFeature n r (nodes i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 1) → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiInitialJetRealChannelFeature n r (nodes i)) = a q) ∧
      (xiInitialJetRealChannelEvaluationGram n nodes).PosDef ∧
      0 < (xiInitialJetRealChannelEvaluationGram n nodes).det) ↔
    (∀ F : Set (ℂ × Bool), F.Finite →
      ∃ (points : Fin (n + 1) → {sample : ℂ × Bool // sample ∉ F})
          (dual : Fin (n + 1) → Fin (n + 1) → ℝ),
        Function.Injective points ∧
        (∀ q r, ∑ i, dual q i *
            xiInitialJetRealChannelFeature n r (points i) =
          if q = r then 1 else 0) ∧
        (∀ (a : Fin (n + 1) → ℝ) q,
          ∑ i, dual q i *
            (∑ r, a r *
              xiInitialJetRealChannelFeature n r (points i)) = a q) ∧
        (xiInitialJetRealChannelEvaluationGram n
          (fun i => (points i : ℂ × Bool))).PosDef ∧
        0 < (xiInitialJetRealChannelEvaluationGram n
          (fun i => (points i : ℂ × Bool))).det) := by
  constructor
  · intro _hfinite F hF
    exact exists_injective_xiInitialJetRealChannelCofiniteHilbertReconstruction
      n F hF
  · intro _hcofinite
    exact exists_injective_xiInitialJetRealChannelEvaluationHilbertReconstruction n

/-- **Universal cofinite real-channel detector.**  After any finite deletion of tagged
measurements, one fixed surviving packet detects every nonzero real coefficient vector in the
initial completed-Xi jet and carries strict real Hilbert geometry. -/
theorem exists_injective_xiInitialJetRealChannelCofiniteUniversalDetector
    (n : ℕ) (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ points : Fin (n + 1) → {sample : ℂ × Bool // sample ∉ F},
      Function.Injective points ∧
      (∀ a : Fin (n + 1) → ℝ, a ≠ 0 →
        ∃ i, (∑ r, a r *
          xiInitialJetRealChannelFeature n r (points i)) ≠ 0) ∧
      (xiInitialJetRealChannelEvaluationGram n
        (fun i => (points i : ℂ × Bool))).PosDef ∧
      0 < (xiInitialJetRealChannelEvaluationGram n
        (fun i => (points i : ℂ × Bool))).det := by
  classical
  obtain ⟨points, dual, hinj, _hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiInitialJetRealChannelCofiniteHilbertReconstruction n F hF
  refine ⟨points, hinj, ?_, hgram, hdet⟩
  intro a ha
  by_contra hdetect
  have hzero :
      ∀ i, ∑ r, a r * xiInitialJetRealChannelFeature n r (points i) = 0 := by
    intro i
    by_contra hi
    exact hdetect ⟨i, hi⟩
  apply ha
  funext q
  calc
    a q = ∑ i, dual q i *
        (∑ r, a r * xiInitialJetRealChannelFeature n r (points i)) :=
      (hrecovery a q).symm
    _ = 0 := by simp [hzero]

end

end RHTower
