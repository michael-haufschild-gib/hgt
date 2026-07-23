import GaloisForLFunctions.HTGeometry.ContinuousCofiniteRealHilbertReconstruction
import GaloisForLFunctions.HTGeometry.ContinuousFiniteSupportTailIndependence
import GaloisForLFunctions.RHTower.XiJetFreeness

/-!
# Cofinite point-jet completed-Xi Hilbert reconstruction

The existing Xi jet-freeness theorems give ordinary linear independence and finite Hilbert
reconstruction for the point coordinate, initial Xi derivatives, and all bounded monomials in
those functions.  Continuity upgrades these finite dictionaries through the HTGeometry
finite-support bridge: every finite deletion of the complex sampling domain still leaves one
square packet with exact dual recovery and strict Hilbert geometry.

The bounded-monomial packet is universal over all coefficient vectors of the chosen degree:
one packet, selected after the deletion but before the coefficients, detects every nonzero bounded
differential polynomial in `z, ξ, ξ′, …, ξ⁽ⁿ⁾`.
-/

open scoped BigOperators ComplexOrder

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The point coordinate and every member of a finite initial completed-Xi jet are continuous. -/
theorem continuous_xiPointInitialJets (n : ℕ) :
    ∀ j, Continuous (pointJetFunctionTuple xi n j) := by
  intro j
  induction j using Fin.cases with
  | zero =>
      simpa [pointJetFunctionTuple, Fin.cons_zero] using
        (continuous_id : Continuous (id : ℂ → ℂ))
  | succ j =>
      simpa [pointJetFunctionTuple, Fin.cons_succ] using
        (differentiable_iteratedDeriv_of_entire xi_differentiable (j : ℕ)).continuous

/-- Every bounded monomial in the point coordinate and finite initial Xi jet is continuous. -/
theorem continuous_xiPointInitialJetMonomial (n M : ℕ) :
    ∀ i, Continuous (xiPointInitialJetMonomial n M i) := by
  intro i
  simpa only [xiPointInitialJetMonomial] using
    continuous_finsuppMonomial
      (pointJetFunctionTuple xi n) (continuous_xiPointInitialJets n)
      (xiPointInitialJetMonomialExponent n M i)

/-- The point coordinate and finite initial Xi jet remain coefficient-independent after deleting
any finite subset of the complex domain. -/
theorem tailCoefficientIndependent_xiPointInitialJets (n : ℕ) :
    TailCoefficientIndependent (pointJetFunctionTuple xi n) :=
  (tailCoefficientIndependent_iff_linearIndependent_of_continuous
    (pointJetFunctionTuple xi n) (continuous_xiPointInitialJets n)).2
      (algebraicIndependent_xi_pointInitialJets n).linearIndependent

/-- Every finite bounded point/Xi-jet monomial dictionary remains coefficient-independent after
deleting any finite subset of the complex domain. -/
theorem tailCoefficientIndependent_xiPointInitialJetMonomial (n M : ℕ) :
    TailCoefficientIndependent (xiPointInitialJetMonomial n M) :=
  (tailCoefficientIndependent_iff_linearIndependent_of_continuous
    (xiPointInitialJetMonomial n M)
    (continuous_xiPointInitialJetMonomial n M)).2
      (linearIndependent_xiPointInitialJetMonomial n M)

/-- One finite point/Xi-jet Hilbert packet exists exactly when complete reconstruction survives
every finite deletion of the complex sampling domain. -/
theorem xiPointInitialJetsFiniteHilbertReconstruction_iff_cofinite (n : ℕ) :
    FiniteEvaluationHilbertReconstruction (pointJetFunctionTuple xi n) ↔
      CofiniteEvaluationHilbertReconstruction (pointJetFunctionTuple xi n) :=
  finiteEvaluationHilbertReconstruction_iff_cofinite_of_continuous
    (pointJetFunctionTuple xi n) (continuous_xiPointInitialJets n)

/-- Finite and deletion-robust Hilbert reconstruction have the same phase for every bounded
point/Xi-jet monomial dictionary. -/
theorem xiPointInitialJetMonomialFiniteHilbertReconstruction_iff_cofinite
    (n M : ℕ) :
    FiniteEvaluationHilbertReconstruction (xiPointInitialJetMonomial n M) ↔
      CofiniteEvaluationHilbertReconstruction
        (xiPointInitialJetMonomial n M) :=
  finiteEvaluationHilbertReconstruction_iff_cofinite_of_continuous
    (xiPointInitialJetMonomial n M)
    (continuous_xiPointInitialJetMonomial n M)

/-- After any finite deletion, the point coordinate and initial completed-Xi jet provide distinct
surviving nodes, exact dual coefficient recovery, a positive-definite Gram, and positive volume. -/
theorem exists_injective_xiPointInitialJetCofiniteHilbertReconstruction
    (n : ℕ) (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : Fin (n + 2) → {z : ℂ // z ∉ F})
        (dual : Fin (n + 2) → Fin (n + 2) → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * pointJetFunctionTuple xi n r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 2) → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * pointJetFunctionTuple xi n r (points i)) = a q) ∧
      (cofiniteEvaluationGram (pointJetFunctionTuple xi n) F points).PosDef ∧
      0 < (cofiniteEvaluationGram (pointJetFunctionTuple xi n) F points).det :=
  exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
    (pointJetFunctionTuple xi n)
    (tailCoefficientIndependent_xiPointInitialJets n) F hF

/-- After any finite deletion, every bounded point/Xi-jet monomial dictionary has one distinct
surviving packet with exact coefficient recovery and strict Hilbert geometry. -/
theorem exists_injective_xiPointInitialJetMonomialCofiniteHilbertReconstruction
    (n M : ℕ) (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : XiPointInitialJetMonomialIndex n M → {z : ℂ // z ∉ F})
        (dual : XiPointInitialJetMonomialIndex n M →
          XiPointInitialJetMonomialIndex n M → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiPointInitialJetMonomial n M r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : XiPointInitialJetMonomialIndex n M → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiPointInitialJetMonomial n M r (points i)) = a q) ∧
      (cofiniteEvaluationGram (xiPointInitialJetMonomial n M) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiPointInitialJetMonomial n M) F points).det :=
  exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
    (xiPointInitialJetMonomial n M)
    (tailCoefficientIndependent_xiPointInitialJetMonomial n M) F hF

/-- **Finite full-complex point-jet reconstruction from real channels.**  A doubled packet of
tagged real/imaginary observations exactly recovers both real coordinates of every complex
coefficient of `z, ξ, ξ′, …, ξ⁽ⁿ⁾`, with a positive-definite real Gram. -/
theorem
    exists_injective_xiPointInitialJetsComplexCoefficientRealChannelHilbertReconstruction
    (n : ℕ) :
    ∃ (points : Fin (n + 2) × Bool → ℂ × Bool)
        (dual : Fin (n + 2) × Bool → Fin (n + 2) × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (pointJetFunctionTuple xi n) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 2) × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (pointJetFunctionTuple xi n) r (points i)) = a q) ∧
      (GaloisForLFunctions.HilbertMetric.realEvaluationGram
        (complexCoefficientRealChannelFeature
          (pointJetFunctionTuple xi n)) points).PosDef ∧
      0 < (GaloisForLFunctions.HilbertMetric.realEvaluationGram
        (complexCoefficientRealChannelFeature
          (pointJetFunctionTuple xi n)) points).det :=
  exists_injective_complexCoefficientRealChannelHilbertReconstruction_of_linearIndependent
    (pointJetFunctionTuple xi n)
    (algebraicIndependent_xi_pointInitialJets n).linearIndependent

/-- **Cofinite full-complex point-jet reconstruction from real channels.**  After deleting any
finite set of tagged measurements, a surviving doubled packet still exactly recovers arbitrary
complex point/Xi-jet coefficients through their real and imaginary coordinates. -/
theorem
    exists_injective_xiPointInitialJetsComplexCoefficientRealChannelCofiniteHilbertReconstruction
    (n : ℕ) (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ (points : Fin (n + 2) × Bool → {sample : ℂ × Bool // sample ∉ F})
        (dual : Fin (n + 2) × Bool → Fin (n + 2) × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (pointJetFunctionTuple xi n) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 2) × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (pointJetFunctionTuple xi n) r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (pointJetFunctionTuple xi n)) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (pointJetFunctionTuple xi n)) F points).det :=
  exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_tailCoefficientIndependent
    (pointJetFunctionTuple xi n)
    (tailCoefficientIndependent_xiPointInitialJets n) F hF

/-- **Finite full-complex differential-polynomial reconstruction from real channels.**  One
tagged packet exactly recovers both real coordinates of every complex coefficient in the bounded
point/Xi-jet monomial dictionary. -/
theorem
    exists_injective_xiPointInitialJetMonomialComplexCoefficientRealChannelHilbertReconstruction
    (n M : ℕ) :
    ∃ (points : XiPointInitialJetMonomialIndex n M × Bool → ℂ × Bool)
        (dual : XiPointInitialJetMonomialIndex n M × Bool →
          XiPointInitialJetMonomialIndex n M × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiPointInitialJetMonomial n M) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : XiPointInitialJetMonomialIndex n M × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiPointInitialJetMonomial n M) r (points i)) = a q) ∧
      (GaloisForLFunctions.HilbertMetric.realEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M)) points).PosDef ∧
      0 < (GaloisForLFunctions.HilbertMetric.realEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M)) points).det :=
  exists_injective_complexCoefficientRealChannelHilbertReconstruction_of_linearIndependent
    (xiPointInitialJetMonomial n M)
    (linearIndependent_xiPointInitialJetMonomial n M)

/-- **Cofinite full-complex differential-polynomial reconstruction from real channels.**  Exact
recovery of every complex bounded differential-polynomial coefficient survives arbitrary finite
deletion of tagged observations, with strict real Hilbert geometry. -/
theorem
    exists_injective_xiPointInitialJetMonomialComplexCoefficientRealChannelCofiniteHilbertReconstruction
    (n M : ℕ) (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ (points : XiPointInitialJetMonomialIndex n M × Bool →
          {sample : ℂ × Bool // sample ∉ F})
        (dual : XiPointInitialJetMonomialIndex n M × Bool →
          XiPointInitialJetMonomialIndex n M × Bool → ℝ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
          complexCoefficientRealChannelFeature
            (xiPointInitialJetMonomial n M) r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : XiPointInitialJetMonomialIndex n M × Bool → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * complexCoefficientRealChannelFeature
            (xiPointInitialJetMonomial n M) r (points i)) = a q) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M)) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M)) F points).det :=
  exists_injective_cofiniteComplexCoefficientRealChannelHilbertReconstruction_of_tailCoefficientIndependent
    (xiPointInitialJetMonomial n M)
    (tailCoefficientIndependent_xiPointInitialJetMonomial n M) F hF

/-- **Cofinite universal bounded differential-polynomial detector.**  After an arbitrary finite
deletion, one fixed square packet of surviving complex points detects every nonzero coefficient
vector in the degree-`M` point/Xi-jet monomial dictionary.  The same packet carries a
positive-definite Gram and positive Hilbert volume. -/
theorem exists_injective_xiPointInitialJetMonomialCofiniteUniversalDetector
    (n M : ℕ) (F : Set ℂ) (hF : F.Finite) :
    ∃ points : XiPointInitialJetMonomialIndex n M → {z : ℂ // z ∉ F},
      Function.Injective points ∧
      (∀ a : XiPointInitialJetMonomialIndex n M → ℂ, a ≠ 0 →
        ∃ i, (∑ r, a r * xiPointInitialJetMonomial n M r (points i)) ≠ 0) ∧
      (cofiniteEvaluationGram (xiPointInitialJetMonomial n M) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiPointInitialJetMonomial n M) F points).det := by
  classical
  obtain ⟨points, dual, hinj, _hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiPointInitialJetMonomialCofiniteHilbertReconstruction
      n M F hF
  refine ⟨points, hinj, ?_, hgram, hdet⟩
  intro a ha
  by_contra hdetect
  have hzero :
      ∀ i, ∑ r, a r * xiPointInitialJetMonomial n M r (points i) = 0 := by
    intro i
    by_contra hi
    exact hdetect ⟨i, hi⟩
  apply ha
  funext q
  calc
    a q = ∑ i, dual q i *
        (∑ r, a r * xiPointInitialJetMonomial n M r (points i)) :=
      (hrecovery a q).symm
    _ = 0 := by simp [hzero]

/-- **Cofinite universal complex-coefficient detector from real channels.**  After any finite
tagged deletion, one fixed doubled packet detects every nonzero complex coefficient vector,
represented by its real and imaginary coordinates, in the bounded point/Xi-jet monomial
dictionary. -/
theorem
    exists_injective_xiPointInitialJetMonomialComplexCoefficientRealChannelCofiniteUniversalDetector
    (n M : ℕ) (F : Set (ℂ × Bool)) (hF : F.Finite) :
    ∃ points : XiPointInitialJetMonomialIndex n M × Bool →
          {sample : ℂ × Bool // sample ∉ F},
      Function.Injective points ∧
      (∀ a : XiPointInitialJetMonomialIndex n M × Bool → ℝ, a ≠ 0 →
        ∃ i, (∑ r, a r * complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M) r (points i)) ≠ 0) ∧
      (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M)) F points).PosDef ∧
      0 < (cofiniteRealEvaluationGram
        (complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M)) F points).det := by
  classical
  obtain ⟨points, dual, hinj, _hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiPointInitialJetMonomialComplexCoefficientRealChannelCofiniteHilbertReconstruction
      n M F hF
  refine ⟨points, hinj, ?_, hgram, hdet⟩
  intro a ha
  by_contra hdetect
  have hzero :
      ∀ i, ∑ r, a r * complexCoefficientRealChannelFeature
        (xiPointInitialJetMonomial n M) r (points i) = 0 := by
    intro i
    by_contra hi
    exact hdetect ⟨i, hi⟩
  apply ha
  funext q
  calc
    a q = ∑ i, dual q i *
        (∑ r, a r * complexCoefficientRealChannelFeature
          (xiPointInitialJetMonomial n M) r (points i)) :=
      (hrecovery a q).symm
    _ = 0 := by simp [hzero]

end

end RHTower
