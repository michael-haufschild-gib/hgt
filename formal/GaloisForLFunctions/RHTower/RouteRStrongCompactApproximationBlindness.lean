import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff

/-!
# Route R strong compact-approximation blindness

Every bounded Hilbert-space operator is a pointwise strong limit of compact finite-basis
truncations.  Applying this to Route R's fixed Stokes--Sonin commutator gives, at every nonneutral
grade, an explicit noncompact operator approximated strongly by compact operators.

Thus weakening the missing Calkin-norm landing to strong (hence weak) operator convergence destroys
the compactness information.  Together with the norm/Calkin coefficient gap, this closes the
topology-only escape: norm convergence cannot erase the retained atom, while strong convergence
cannot detect compactness.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- Finite Hilbert-basis truncations of every bounded operator converge pointwise strongly to that
operator. -/
theorem tendsto_hsTruncation_apply_atTop
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (x : H) :
    Tendsto (fun s : Finset ι =>
      _root_.ContinuousLinearMap.hsTruncation b T s x) atTop (nhds (T x)) := by
  simpa [HasSum, SummationFilter.unconditional,
    _root_.ContinuousLinearMap.hsTruncation_apply] using
    (_root_.ContinuousLinearMap.hasSum_inner_smul b T x)

/-- Every bounded Hilbert-space operator has an explicit compact net converging to it strongly. -/
theorem exists_compactNet_tendsto_pointwise
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    ∃ K : Finset (exists_hilbertBasis ℂ H).choose → (H →L[ℂ] H),
      (∀ s, IsCompactOperator (K s)) ∧
        ∀ x, Tendsto (fun s => K s x) atTop (nhds (T x)) := by
  let b := _root_.ContinuousLinearMap.hsBasis ℂ H
  refine ⟨fun s => _root_.ContinuousLinearMap.hsTruncation b T s, ?_, ?_⟩
  · intro s
    exact _root_.ContinuousLinearMap.isCompactOperator_hsTruncation b T s
  · intro x
    exact tendsto_hsTruncation_apply_atTop b T x

/-- Explicit compact finite-basis approximation net for the fixed Route-R `(2,3)` commutator. -/
def routeRTwoThreeStokesStrongCompactApproximation (A a : ℝ)
    (s : Finset (exists_hilbertBasis ℂ ArchimedeanWeightedL2).choose) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  _root_.ContinuousLinearMap.hsTruncation
    (_root_.ContinuousLinearMap.hsBasis ℂ ArchimedeanWeightedL2)
    (routeRTwoThreeStokesSoninCommutator A a) s

theorem routeRTwoThreeStokesStrongCompactApproximation_isCompactOperator
    (A a : ℝ)
    (s : Finset (exists_hilbertBasis ℂ ArchimedeanWeightedL2).choose) :
    IsCompactOperator (routeRTwoThreeStokesStrongCompactApproximation A a s) := by
  exact _root_.ContinuousLinearMap.isCompactOperator_hsTruncation
    (_root_.ContinuousLinearMap.hsBasis ℂ ArchimedeanWeightedL2)
    (routeRTwoThreeStokesSoninCommutator A a) s

theorem routeRTwoThreeStokesStrongCompactApproximation_tendsto_pointwise
    (A a : ℝ) (x : ArchimedeanWeightedL2) :
    Tendsto (fun s => routeRTwoThreeStokesStrongCompactApproximation A a s x)
      atTop (nhds (routeRTwoThreeStokesSoninCommutator A a x)) := by
  exact tendsto_hsTruncation_apply_atTop
    (_root_.ContinuousLinearMap.hsBasis ℂ ArchimedeanWeightedL2)
    (routeRTwoThreeStokesSoninCommutator A a) x

/-- **Strong-topology blindness on the actual Route-R receiver.**  At every nonneutral grade the
fixed physical commutator is noncompact, yet it is the pointwise strong limit of the explicit net
of compact finite-basis truncations above. -/
theorem routeRTwoThreeStokes_noncompact_strongLimit_compact
    {A : ℝ} (hA : 0 < A) {a : ℝ} (ha : a ≠ 0) :
    (¬IsCompactOperator (routeRTwoThreeStokesSoninCommutator A a)) ∧
      (∀ s : Finset (exists_hilbertBasis ℂ ArchimedeanWeightedL2).choose,
        IsCompactOperator (routeRTwoThreeStokesStrongCompactApproximation A a s)) ∧
      ∀ x : ArchimedeanWeightedL2,
        Tendsto (fun s => routeRTwoThreeStokesStrongCompactApproximation A a s x)
          atTop (nhds (routeRTwoThreeStokesSoninCommutator A a x)) := by
  refine ⟨?_, routeRTwoThreeStokesStrongCompactApproximation_isCompactOperator A a, ?_⟩
  · rw [routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff hA]
    exact ha
  · exact routeRTwoThreeStokesStrongCompactApproximation_tendsto_pointwise A a

end

end RHTower
