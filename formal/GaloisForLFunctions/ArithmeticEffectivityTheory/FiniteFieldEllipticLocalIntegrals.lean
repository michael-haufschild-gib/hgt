import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLocalFields
import GaloisForLFunctions.HTGeometry.LocalRankOneIntegral

/-!
# Rank-one Haar integrals at every actual place

The generic shell integral applies to the proved local fields of the curve.
Its finite-place parameter is the cardinality of the actual prime residue ring;
the infinity parameter is three.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open IsDedekindDomain MeasureTheory HTGeometry.DiscreteValuationHaar
open scoped WithZero WithZeroMulInt

noncomputable section

instance finiteCompletion_valuationNontrivial (v : FinitePlace) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsNontrivial := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective
    (K := K) (v := v) (WithZero.exp (-1))
  refine ⟨π, ?_, ?_⟩
  · rw [hπ]
    exact WithZero.exp_ne_zero
  · rw [hπ]
    exact ne_of_lt (show (WithZero.exp (-1) : ℤᵐ⁰) < 1 by decide)

instance finiteCompletion_integerCompact (v : FinitePlace) :
    CompactSpace (Integer (v.adicCompletion K)) := finiteCompletionInteger_compact v

instance infinityCompletion_integerCompact : CompactSpace (Integer InfinityCompletion) :=
  HTGeometry.DiscreteValuedCompletion.completedIntegerCompact (WithVal infinityValuation)

local instance (v : FinitePlace) : IsDiscreteValuationRing (Integer (v.adicCompletion K)) :=
  (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring_isDiscreteValuationRing

local instance : IsDiscreteValuationRing (Integer InfinityCompletion) :=
  (Valued.v : Valuation InfinityCompletion ℤᵐ⁰).valuationSubring_isDiscreteValuationRing

local instance (v : FinitePlace) : MeasurableSpace (v.adicCompletion K) := borel _
local instance (v : FinitePlace) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance : MeasurableSpace InfinityCompletion := borel _
local instance : BorelSpace InfinityCompletion := ⟨rfl⟩

/-- A uniformizer of the actual completed finite-place integer ring. -/
def finiteLocalUniformizer (v : FinitePlace) : Integer (v.adicCompletion K) :=
  (IsDiscreteValuationRing.exists_irreducible (Integer (v.adicCompletion K))).choose

theorem finiteLocalUniformizer_irreducible (v : FinitePlace) :
    Irreducible (finiteLocalUniformizer v) :=
  (IsDiscreteValuationRing.exists_irreducible (Integer (v.adicCompletion K))).choose_spec

def infinityLocalUniformizer : Integer InfinityCompletion :=
  (IsDiscreteValuationRing.exists_irreducible (Integer InfinityCompletion)).choose

theorem infinityLocalUniformizer_irreducible : Irreducible infinityLocalUniformizer :=
  (IsDiscreteValuationRing.exists_irreducible (Integer InfinityCompletion)).choose_spec

def finiteLocalKernel (v : FinitePlace) (z : ℂ) : v.adicCompletion K → ℂ :=
  sphericalKernel (v.adicCompletion K) (finiteLocalUniformizer v)
    (finiteLocalUniformizer_irreducible v) z

def infinityLocalKernel (z : ℂ) : InfinityCompletion → ℂ :=
  sphericalKernel InfinityCompletion infinityLocalUniformizer infinityLocalUniformizer_irreducible z

theorem finiteLocalKernel_integrable (v : FinitePlace) {z : ℂ} (hz : ‖z‖ < 1) :
    Integrable (finiteLocalKernel v z) (normalizedHaar (v.adicCompletion K)) :=
  sphericalKernel_integrable (v.adicCompletion K) (finiteLocalUniformizer v)
    (finiteLocalUniformizer_irreducible v) hz

theorem infinityLocalKernel_integrable {z : ℂ} (hz : ‖z‖ < 1) :
    Integrable (infinityLocalKernel z) (normalizedHaar InfinityCompletion) :=
  sphericalKernel_integrable InfinityCompletion infinityLocalUniformizer
    infinityLocalUniformizer_irreducible hz

/-- The finite local integral uses the residue cardinality of the actual affine prime. -/
theorem integral_finiteLocalKernel (v : FinitePlace) {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, finiteLocalKernel v z x ∂normalizedHaar (v.adicCompletion K)) =
      (1 - (Nat.card (RingOfIntegers ⧸ v.asIdeal) : ℂ)⁻¹ * z) / (1 - z) := by
  have hc : Nat.card (Residue (v.adicCompletion K)) = Nat.card (RingOfIntegers ⧸ v.asIdeal) :=
    Nat.card_congr (finiteCompletionResidueEquiv v).toEquiv
  simpa only [finiteLocalKernel, hc] using
    integral_sphericalKernel (v.adicCompletion K) (finiteLocalUniformizer v)
      (finiteLocalUniformizer_irreducible v) hz

/-- The infinity local factor has the proved residue size three. -/
theorem integral_infinityLocalKernel {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, infinityLocalKernel z x ∂normalizedHaar InfinityCompletion) =
      (1 - (3 : ℂ)⁻¹ * z) / (1 - z) := by
  simpa only [infinityLocalKernel, infinityCompletionResidue_card, Nat.cast_ofNat] using
    integral_sphericalKernel InfinityCompletion infinityLocalUniformizer
      infinityLocalUniformizer_irreducible hz

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
