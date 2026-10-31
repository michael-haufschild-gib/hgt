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

local instance localMagnitudeFiniteMeasurable (v : FinitePlace) : MeasurableSpace (v.adicCompletion K) := borel _
local instance localMagnitudeFiniteBorel (v : FinitePlace) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance localMagnitudeFiniteCompact (v : FinitePlace) : CompactSpace (Integer (v.adicCompletion K)) :=
  finiteCompletionInteger_compact v
local instance localMagnitudeInfinityMeasurable : MeasurableSpace InfinityCompletion := borel _
local instance localMagnitudeInfinityBorel : BorelSpace InfinityCompletion := ⟨rfl⟩

private theorem toNNReal_base_congr {q r : ℝ≥0} (hq : q ≠ 0) (hr : r ≠ 0)
    (h : q = r) (z : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal hq z = WithZeroMulInt.toNNReal hr z := by
  subst r
  rfl

/-- Actual finite-place magnitude is the additive Haar change-of-variables factor. -/
theorem finiteCompletion_distribHaarChar (v : FinitePlace) (u : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) u = finiteCompletionMagnitude v (u : v.adicCompletion K) := by
  have hrange : WithZero.exp (-1 : ℤ) ∈
      Set.range (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := by
    refine ⟨algebraMap K (v.adicCompletion K) (HTGeometry.placeUniformizer K v), ?_⟩
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)
      (HTGeometry.placeUniformizer K v)).trans (HTGeometry.placeUniformizer_valuation K v)
  have h := distribHaarChar_eq_residueMagnitude (v.adicCompletion K) hrange u
  have hcard : Nat.card (Residue (v.adicCompletion K)) =
      Nat.card (RingOfIntegers ⧸ v.asIdeal) :=
    Nat.card_congr (finiteCompletionResidueEquiv v).toEquiv
  have hq₀ : (Nat.card (Residue (v.adicCompletion K)) : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ :
      Nat.card (Residue (v.adicCompletion K)) ≠ 0)
  have hq : (Nat.card (RingOfIntegers ⧸ v.asIdeal) : ℝ≥0) ≠ 0 := by
    rwa [hcard] at hq₀
  change distribHaarChar (v.adicCompletion K) u =
    WithZeroMulInt.toNNReal hq (Valued.v (u : v.adicCompletion K))
  exact h.trans (toNNReal_base_congr hq₀ hq (by exact_mod_cast hcard) _)

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
  have hq₀ : (Nat.card (Residue InfinityCompletion) : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ :
      Nat.card (Residue InfinityCompletion) ≠ 0)
  have hq : (3 : ℝ≥0) ≠ 0 := by norm_num
  change distribHaarChar InfinityCompletion u =
    WithZeroMulInt.toNNReal hq (Valued.v (u : InfinityCompletion))
  exact h.trans (toNNReal_base_congr hq₀ hq (by exact_mod_cast hcard) _)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finiteCompletion_distribHaarChar
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.infinityCompletion_distribHaarChar
