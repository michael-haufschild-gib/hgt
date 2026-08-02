import GaloisForLFunctions.HTGeometry.PrimeResidueValuationExactSourceBoundary
import GaloisForLFunctions.RHTower.XiShiftAllValuationLayerBarrier

/-!
# The completed xi shift beyond residue--valuation fusion completion

The filtered von Mangoldt source is nonzero at every positive prime power. Hence the general
private-layer barrier applies not only to the scalar prime-zeta tower but to every finite
depth--residue fusion completion built from a cofinally tail-dense prime sampler. The rational
calibration relating this source to the uncorrected completed `+2` shift of `xi'/xi` lies in the
coordinate field, so it cannot remove the barrier.
-/

namespace RHTower

open Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

universe u

local instance xiResidueFusionUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiResidueFusionUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiResidueFusionUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The filtered von Mangoldt source is differentially independent over every complete finite
residue--valuation fusion field whose prime sampler is cofinally tail-dense. -/
theorem filteredVonMangoldtUpperEndCarrier_differentialIndependent_over_residueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    DifferentialIndependent
      (primeResidueValuationUpperEndCoordinateFusionCompletionField A y)
      (fun _ : Unit => filteredVonMangoldtUpperEndCarrier) := by
  exact
    analyticPrimeProfileCarrier_differentialIndependent_over_residueFusionCompletion
      A y hy filteredVonMangoldtFiniteAbscissaSource
      filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers
      filteredVonMangoldt_nonvanishing_layers_infinite

/-- The same source is hypertranscendental over the entire depth--residue fusion completion. -/
theorem filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver_residueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    HypertranscendentalOver
      (primeResidueValuationUpperEndCoordinateFusionCompletionField A y)
      filteredVonMangoldtUpperEndCarrier := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact
    filteredVonMangoldtUpperEndCarrier_differentialIndependent_over_residueFusionCompletion
      A y hy

/-- The uncorrected completed `+2` logarithmic Xi shift crosses the same boundary. Thus no
finite-residue local fusion completion, even after derivation and rational coordinate gauges,
contains a differential-algebraic explanation of this divisor-bearing current. -/
theorem xiLogDerivShiftTwoUncorrectedCarrier_hypertranscendentalOver_residueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    HypertranscendentalOver
      (primeResidueValuationUpperEndCoordinateFusionCompletionField A y)
      xiLogDerivShiftTwoUncorrectedCarrier := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact
    differentialIndependent_over_residueFusionCompletion_add_rationalCoordinate
      A y
      (filteredVonMangoldtUpperEndCarrier_differentialIndependent_over_residueFusionCompletion
        A y hy)
      (fun _ : Unit => xiShiftTwoRationalCorrectionMero)
      (fun _ => xiShiftTwoRationalCorrectionMero_mem_rationalCoordinate)

/-- The filtered von Mangoldt current remains differentially independent after adjoining the
genuine coordinate, every finite-prime Euler germ, and the complete residue--valuation fusion
family.  This is the exact analytic image of its nonzero primitive source-quotient class. -/
theorem filteredVonMangoldtUpperEndCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    DifferentialIndependent
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      (fun _ : Unit => filteredVonMangoldtUpperEndCarrier) := by
  exact
    analyticPrimeProfileCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
      A y hy filteredVonMangoldtFiniteAbscissaSource
      filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers
      filteredVonMangoldt_nonvanishing_layers_infinite

/-- The filtered von Mangoldt current is hypertranscendental over the local-Euler fusion
completion. -/
theorem filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    HypertranscendentalOver
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      filteredVonMangoldtUpperEndCarrier := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact
    filteredVonMangoldtUpperEndCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
      A y hy

/-- **Completed Xi exact source boundary.** The uncorrected completed `+2` logarithmic Xi shift
remains hypertranscendental over the local-Euler residue--valuation fusion completion.  Finite
Euler localization, arbitrary finite residue alphabets, all valuation depths, same-prime fusion,
derivation, and rational calibration together still cannot absorb the divisor-bearing primitive
current. -/
theorem xiLogDerivShiftTwoUncorrectedCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    HypertranscendentalOver
      (primeResidueValuationLocalEulerFusionCompletionField A y)
      xiLogDerivShiftTwoUncorrectedCarrier := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact
    differentialIndependent_over_localEulerResidueFusionCompletion_add_rationalCoordinate
      A y
      (filteredVonMangoldtUpperEndCarrier_differentialIndependent_over_localEulerResidueFusionCompletion
        A y hy)
      (fun _ : Unit => xiShiftTwoRationalCorrectionMero)
      (fun _ => xiShiftTwoRationalCorrectionMero_mem_rationalCoordinate)

end

end RHTower
