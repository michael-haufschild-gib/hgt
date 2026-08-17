import GaloisForLFunctions.HTGeometry.HelsonStratumMeasurable
import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOneEquiv
import GaloisForLFunctions.HTGeometry.HelsonCubeRootNonContinuation

/-!
# The continuation stratum obeys a zero–one law

Continuability is unchanged by modifying finitely many prime phases, and the stratum is Borel, so
the finite-modification zero–one law applies: for every product probability measure on the phase
torus the stratum has measure `0` or `1`.

Both alternatives are compatible with the topology of the stratum, which is dense with dense
complement: the trivial phase and its finite modifications are continuable, while the constant
primitive cube root of unity and its finite modifications are not.
-/

open Complex Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The zero–one law for the continuation stratum.** -/
theorem measure_infinitePi_continuableStratum_eq_zero_or_one
    (μ : ∀ _p : Nat.Primes, Measure {z : ℂ // ‖z‖ = 1})
    [∀ p, IsProbabilityMeasure (μ p)] :
    Measure.infinitePi μ continuableStratum = 0 ∨
      Measure.infinitePi μ continuableStratum = 1 := by
  refine measure_infinitePi_primes_eq_zero_or_one_of_invariant μ trivialPhase
    measurableSet_continuableStratum ?_
  intro x y hfin
  have hcoe : {p : Nat.Primes | (x p : ℂ) ≠ (y p : ℂ)}.Finite := by
    refine hfin.subset fun p hp => ?_
    intro hcon
    exact hp (by rw [hcon])
  have hcoe' : {p : Nat.Primes | (y p : ℂ) ≠ (x p : ℂ)}.Finite := by
    have hset : {p : Nat.Primes | (y p : ℂ) ≠ (x p : ℂ)}
        = {p : Nat.Primes | (x p : ℂ) ≠ (y p : ℂ)} := by
      ext p
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hset]
    exact hcoe
  exact ⟨fun hx => mem_continuableStratum_of_finite_ne hx hcoe',
    fun hy => mem_continuableStratum_of_finite_ne hy hcoe⟩

/-- **The seam is a Borel set which is dense, has dense complement, and carries no intermediate
measure.** -/
theorem continuableStratum_dense_codense_measurable_zeroOne
    (μ : ∀ _p : Nat.Primes, Measure {z : ℂ // ‖z‖ = 1})
    [∀ p, IsProbabilityMeasure (μ p)] :
    Dense continuableStratum ∧ Dense (continuableStratumᶜ) ∧
      MeasurableSet continuableStratum ∧
      (Measure.infinitePi μ continuableStratum = 0 ∨
        Measure.infinitePi μ continuableStratum = 1) :=
  ⟨dense_continuableStratum, dense_compl_continuableStratum, measurableSet_continuableStratum,
    measure_infinitePi_continuableStratum_eq_zero_or_one μ⟩

end GaloisForLFunctions.HTGeometry

end
