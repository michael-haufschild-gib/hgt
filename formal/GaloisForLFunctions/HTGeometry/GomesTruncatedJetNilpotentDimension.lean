import GaloisForLFunctions.HTGeometry.GomesDyadicJetSymmetrySelection
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetPositiveCoordinates
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetSymmetryDimension

/-!
# Exact dimension of the additive unipotent coordinates

Removing the one constant resonance leaves exactly n/orderOf(z) independent
complex coordinates. The formula includes order zero and the scalar-collapse
horizon without separate hypotheses.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The exact number of positive resonant weights below the finite horizon. -/
theorem gomesTruncatedJetPositiveResonantIndex_card (n : ℕ) (z : ℂ) :
    Fintype.card (GomesTruncatedJetPositiveResonantIndex n z) = n / orderOf z := by
  change Fintype.card {k : GomesTruncatedJetResonantIndex n z //
    ¬ (k = gomesTruncatedJetZeroResonance n z)} = n / orderOf z
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    gomesTruncatedJetResonantIndex_card, Nat.add_sub_cancel]

/-- The full nilpotent joint matrix space has exactly the number of nonconstant resonances as its dimension. -/
theorem gomesTruncatedJetNilpotentSpace_finrank (n : ℕ) (z : ℂ) :
    Module.finrank ℂ (gomesTruncatedJetNilpotentSpace n z) = n / orderOf z := by
  rw [(gomesTruncatedJetNilpotentLinearEquiv n z).finrank_eq,
    Module.finrank_fintype_fun_eq_card, gomesTruncatedJetPositiveResonantIndex_card]

/-- The existing named dyadic phase supplies exactly n/2^k additive unipotent coordinates. -/
theorem gomesDyadicJetNilpotentSpace_finrank (n k : ℕ) :
    Module.finrank ℂ (gomesTruncatedJetNilpotentSpace n (Bottcher.dyadicRoot k)) = n / (2 ^ k) := by
  rw [gomesTruncatedJetNilpotentSpace_finrank, Bottcher.orderOf_dyadicRoot_named]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
