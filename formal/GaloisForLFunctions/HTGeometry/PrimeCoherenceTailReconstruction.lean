import GaloisForLFunctions.HTGeometry.CoherenceEndReconstruction
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# Prime-tail consequences of coherence-end reconstruction

This file joins the graph-theoretic finite-defect coherence theorem to the already formalized
projective prime-orientation tail line.  The result is stated at the coefficient-tail matroid
level; no analytic field-identification hypothesis is hidden in the statement.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {P : Type u}

/-- The graph-native projective finite-tail relation is exactly the established projective
prime-orientation relation. -/
theorem booleanProjectiveFiniteEquivalent_iff_primeOrientationTailPairDependent
    (ε δ : P → Bool) :
    BooleanProjectiveFiniteEquivalent ε δ ↔
      PrimeOrientationTailPairDependent ε δ := by
  rw [primeOrientationTailPairDependent_iff]
  rfl

/-- **Prime coherence-tail law.**  Finite-boundary one-endedness is exactly faithfulness of
finite-defect graph coherence on the projective prime-orientation coefficient-tail line. -/
theorem finiteBoundaryOneEnded_iff_primeOrientationCoherenceTail_faithful
    (G : SimpleGraph P) :
    FiniteBoundaryOneEnded G ↔
      ∀ ε δ : P → Bool,
        BooleanEdgeTailEquivalent G ε δ →
          PrimeOrientationTailPairDependent ε δ := by
  rw [finiteBoundaryOneEnded_iff_booleanEdgeTail_faithful]
  constructor
  · intro h ε δ hedge
    exact (booleanProjectiveFiniteEquivalent_iff_primeOrientationTailPairDependent ε δ).mp
      (h ε δ hedge)
  · intro h ε δ hedge
    exact (booleanProjectiveFiniteEquivalent_iff_primeOrientationTailPairDependent ε δ).mpr
      (h ε δ hedge)

/-- If the finite-boundary one-ended property fails, finitely defective edge data can hide two
genuinely independent projective prime-orientation tail directions. -/
theorem exists_coherenceTailEquivalent_not_primeOrientationTailPairDependent_of_not_oneEnded
    (G : SimpleGraph P) (hG : ¬FiniteBoundaryOneEnded G) :
    ∃ ε δ : P → Bool,
      BooleanEdgeTailEquivalent G ε δ ∧
        ¬PrimeOrientationTailPairDependent ε δ := by
  classical
  rw [finiteBoundaryOneEnded_iff_primeOrientationCoherenceTail_faithful] at hG
  push Not at hG
  exact hG

/-- Tensoring two infinite preconnected prime-indexing graphs removes every finite-defect
coherence ambiguity at the coefficient-tail-line level. -/
theorem primeOrientationCoherenceTail_faithful_boxProd
    {Q : Type*} [Infinite P] [Infinite Q]
    (G : SimpleGraph P) (H : SimpleGraph Q)
    (hG : G.Preconnected) (hH : H.Preconnected)
    (ε δ : P × Q → Bool)
    (hcoherence : BooleanEdgeTailEquivalent (G □ H) ε δ) :
    PrimeOrientationTailPairDependent ε δ := by
  apply
    (finiteBoundaryOneEnded_iff_primeOrientationCoherenceTail_faithful (G □ H)).mp
      (finiteBoundaryOneEnded_boxProd G H hG hH)
  exact hcoherence

end GaloisForLFunctions.HTGeometry
