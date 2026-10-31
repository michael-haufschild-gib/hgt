import GaloisForLFunctions.HTGeometry.LoopEisenstein.DiscreteHaarMagnitude
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticPlaceNormalization
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Actual elliptic local Haar moduli

At every finite completion and at infinity, the additive Haar modulus is
exactly the normalized magnitude used in the adelic product formula.
Actual uniformizers and completed residue-field equivalences fix the scale.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory IsDedekindDomain
open HTGeometry.DiscreteValuationHaar HTGeometry.LoopEisenstein
open scoped WithZero WithZeroMulInt NNReal
noncomputable section

local instance (v : FinitePlace) : MeasurableSpace (v.adicCompletion K) := borel _
local instance (v : FinitePlace) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance (v : FinitePlace) : CompactSpace (Integer (v.adicCompletion K)) :=
  finiteCompletionInteger_compact v
local instance : MeasurableSpace InfinityCompletion := borel _
local instance : BorelSpace InfinityCompletion := ⟨rfl⟩

/-- Actual finite-place magnitude is the additive Haar change-of-variables factor. -/
theorem finiteCompletion_distribHaarChar (v : FinitePlace) (u : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) u = finiteCompletionMagnitude v (u : v.adicCompletion K) := by
  have hrange : WithZero.exp (-1 : ℤ) ∈
      Set.range (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := by
    refine ⟨algebraMap K (v.adicCompletion K) (HTGeometry.placeUniformizer K v), ?_⟩
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HTGeometry.placeUniformizer_valuation]
  have h := distribHaarChar_eq_residueMagnitude (v.adicCompletion K) hrange u
  have hcard : Nat.card (Residue (v.adicCompletion K)) =
      Nat.card (RingOfIntegers ⧸ v.asIdeal) :=
    Nat.card_congr (finiteCompletionResidueEquiv v).toEquiv
  rw [hcard] at h
  exact h

/-- The actual infinity Haar modulus uses residue cardinality three. -/
theorem infinityCompletion_distribHaarChar (u : InfinityCompletionˣ) :
    distribHaarChar InfinityCompletion u = infinityCompletionMagnitude (u : InfinityCompletion) := by
  have hrange : WithZero.exp (-1 : ℤ) ∈
      Set.range (Valued.v : Valuation InfinityCompletion ℤᵐ⁰) := by
    refine ⟨infinityEmbedding (x / y), ?_⟩
    rw [infinityEmbedding_valuation]
    exact infinityValuation_parameter
  have h := distribHaarChar_eq_residueMagnitude InfinityCompletion hrange u
  have hcard : Nat.card (Residue InfinityCompletion) = 3 := infinityCompletionResidue_card
  rw [hcard] at h
  exact h

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finiteCompletion_distribHaarChar
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.infinityCompletion_distribHaarChar
