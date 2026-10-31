import GaloisForLFunctions.HTGeometry.LoopEisenstein.ValuationSpectralKernel
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticPlaceNormalization
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Spectral integrals at the actual elliptic completions

The actual finite-place and infinity magnitudes define radial spectral
characters. Their completed residue fields and genuine uniformizers identify
these characters with the integrable local spherical kernels, giving the
exact local factors throughout the right half-plane.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory IsDedekindDomain
open HTGeometry.DiscreteValuationHaar HTGeometry.LoopEisenstein
open scoped NNReal WithZero WithZeroMulInt
noncomputable section

local instance (v : FinitePlace) : MeasurableSpace (v.adicCompletion K) := borel _
local instance (v : FinitePlace) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance (v : FinitePlace) : CompactSpace (Integer (v.adicCompletion K)) :=
  finiteCompletionInteger_compact v
local instance : MeasurableSpace InfinityCompletion := borel _
local instance : BorelSpace InfinityCompletion := ⟨rfl⟩

/-- The actual finite completion attains the normalized uniformizer value. -/
theorem finiteCompletion_valuation_exp_neg_one_mem_range (v : FinitePlace) :
    WithZero.exp (-1 : ℤ) ∈ Set.range (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := by
  refine ⟨algebraMap K (v.adicCompletion K) (HTGeometry.placeUniformizer K v), ?_⟩
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)
    (HTGeometry.placeUniformizer K v)).trans (HTGeometry.placeUniformizer_valuation K v)

/-- The actual parameter at infinity has normalized uniformizer value. -/
theorem infinityCompletion_valuation_exp_neg_one_mem_range :
    WithZero.exp (-1 : ℤ) ∈ Set.range (Valued.v : Valuation InfinityCompletion ℤᵐ⁰) := by
  refine ⟨infinityEmbedding (x / y), ?_⟩
  rw [infinityEmbedding_valuation]
  exact infinityValuation_parameter

private theorem finiteCompletedResidue_gt_one (v : FinitePlace) :
    (1 : ℝ≥0) < Nat.card (Residue (v.adicCompletion K)) := by
  exact_mod_cast residue_card_gt_one (v.adicCompletion K)

private theorem infinityCompletedResidue_gt_one :
    (1 : ℝ≥0) < Nat.card (Residue InfinityCompletion) := by
  exact_mod_cast residue_card_gt_one InfinityCompletion

private theorem toNNReal_base_congr {q r : ℝ≥0} (hq : q ≠ 0) (hr : r ≠ 0)
    (h : q = r) (z : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal hq z = WithZeroMulInt.toNNReal hr z := by
  subst r
  rfl

private theorem finiteMagnitude_eq_completedResidue (v : FinitePlace) (z : v.adicCompletion K) :
    finiteCompletionMagnitude v z =
      WithZeroMulInt.toNNReal (finiteCompletedResidue_gt_one v).ne_zero (Valued.v z) := by
  have hcard : Nat.card (Residue (v.adicCompletion K)) =
      Nat.card (RingOfIntegers ⧸ v.asIdeal) := Nat.card_congr (finiteCompletionResidueEquiv v).toEquiv
  have hq₀ := (finiteCompletedResidue_gt_one v).ne_zero
  have hq : (Nat.card (RingOfIntegers ⧸ v.asIdeal) : ℝ≥0) ≠ 0 := by
    rwa [hcard] at hq₀
  change WithZeroMulInt.toNNReal hq (Valued.v z) =
    WithZeroMulInt.toNNReal (finiteCompletedResidue_gt_one v).ne_zero (Valued.v z)
  exact toNNReal_base_congr hq (finiteCompletedResidue_gt_one v).ne_zero
    (by exact_mod_cast hcard.symm) _

private theorem infinityMagnitude_eq_completedResidue (z : InfinityCompletion) :
    infinityCompletionMagnitude z =
      WithZeroMulInt.toNNReal infinityCompletedResidue_gt_one.ne_zero (Valued.v z) := by
  have hq : (3 : ℝ≥0) ≠ 0 := by norm_num
  change WithZeroMulInt.toNNReal hq (Valued.v z) =
    WithZeroMulInt.toNNReal infinityCompletedResidue_gt_one.ne_zero (Valued.v z)
  exact toNNReal_base_congr hq infinityCompletedResidue_gt_one.ne_zero
    (by exact_mod_cast infinityCompletionResidue_card.symm) _

/-- The radial spectral character in the actual finite-place magnitude. -/
def finiteCompletionSpectralKernel (v : FinitePlace) (s : ℂ) (z : v.adicCompletion K) : ℂ :=
  Complex.exp (-(s + 1) * (Real.log (max 1 (finiteCompletionMagnitude v z : ℝ)) : ℂ))

/-- The radial spectral character at the actual infinity completion. -/
def infinityCompletionSpectralKernel (s : ℂ) (z : InfinityCompletion) : ℂ :=
  Complex.exp (-(s + 1) * (Real.log (max 1 (infinityCompletionMagnitude z : ℝ)) : ℂ))

private theorem finiteCompletionSpectralKernel_eq (v : FinitePlace) (s : ℂ) :
    finiteCompletionSpectralKernel v s =
      valuationSpectralKernel (v.adicCompletion K) (Nat.card (Residue (v.adicCompletion K)))
        (finiteCompletedResidue_gt_one v) s := by
  funext z
  unfold finiteCompletionSpectralKernel valuationSpectralKernel
  rw [finiteMagnitude_eq_completedResidue]

private theorem infinityCompletionSpectralKernel_eq (s : ℂ) :
    infinityCompletionSpectralKernel s =
      valuationSpectralKernel InfinityCompletion (Nat.card (Residue InfinityCompletion))
        infinityCompletedResidue_gt_one s := by
  funext z
  unfold infinityCompletionSpectralKernel valuationSpectralKernel
  rw [infinityMagnitude_eq_completedResidue]

/-- Every actual finite-place radial character is absolutely integrable for positive real part. -/
theorem finiteCompletionSpectralKernel_integrable (v : FinitePlace) (s : ℂ) (hs : 0 < s.re) :
    Integrable (finiteCompletionSpectralKernel v s) (normalizedHaar (v.adicCompletion K)) := by
  rw [finiteCompletionSpectralKernel_eq]
  exact valuationSpectralKernel_integrable (v.adicCompletion K)
    (finiteCompletion_valuation_exp_neg_one_mem_range v) s hs

/-- The infinity radial character has the same absolute-convergence domain. -/
theorem infinityCompletionSpectralKernel_integrable (s : ℂ) (hs : 0 < s.re) :
    Integrable (infinityCompletionSpectralKernel s) (normalizedHaar InfinityCompletion) := by
  rw [infinityCompletionSpectralKernel_eq]
  exact valuationSpectralKernel_integrable InfinityCompletion
    infinityCompletion_valuation_exp_neg_one_mem_range s hs

/-- The finite local integral uses the cardinality of its actual prime residue ring. -/
theorem integral_finiteCompletionSpectralKernel (v : FinitePlace) (s : ℂ) (hs : 0 < s.re) :
    (∫ z, finiteCompletionSpectralKernel v s z ∂normalizedHaar (v.adicCompletion K)) =
      (1 - (Nat.card (RingOfIntegers ⧸ v.asIdeal) : ℂ)⁻¹ *
        localSpectralParameter (Nat.card (RingOfIntegers ⧸ v.asIdeal)) s) /
      (1 - localSpectralParameter (Nat.card (RingOfIntegers ⧸ v.asIdeal)) s) := by
  have hcard : Nat.card (Residue (v.adicCompletion K)) =
      Nat.card (RingOfIntegers ⧸ v.asIdeal) := Nat.card_congr (finiteCompletionResidueEquiv v).toEquiv
  rw [finiteCompletionSpectralKernel_eq]
  calc
    _ = (1 - (Nat.card (Residue (v.adicCompletion K)) : ℂ)⁻¹ *
          localSpectralParameter (Nat.card (Residue (v.adicCompletion K))) s) /
        (1 - localSpectralParameter (Nat.card (Residue (v.adicCompletion K))) s) :=
      integral_valuationSpectralKernel (v.adicCompletion K)
        (finiteCompletion_valuation_exp_neg_one_mem_range v) s hs
    _ = _ := by rw [hcard]

/-- The degree-one infinity factor has residue cardinality three. -/
theorem integral_infinityCompletionSpectralKernel (s : ℂ) (hs : 0 < s.re) :
    (∫ z, infinityCompletionSpectralKernel s z ∂normalizedHaar InfinityCompletion) =
      (1 - (3 : ℂ)⁻¹ * localSpectralParameter 3 s) / (1 - localSpectralParameter 3 s) := by
  rw [infinityCompletionSpectralKernel_eq]
  calc
    _ = (1 - (Nat.card (Residue InfinityCompletion) : ℂ)⁻¹ *
          localSpectralParameter (Nat.card (Residue InfinityCompletion)) s) /
        (1 - localSpectralParameter (Nat.card (Residue InfinityCompletion)) s) :=
      integral_valuationSpectralKernel InfinityCompletion
        infinityCompletion_valuation_exp_neg_one_mem_range s hs
    _ = _ := by rw [infinityCompletionResidue_card]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finiteCompletionSpectralKernel_integrable
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.infinityCompletionSpectralKernel_integrable
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.integral_finiteCompletionSpectralKernel
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.integral_infinityCompletionSpectralKernel
