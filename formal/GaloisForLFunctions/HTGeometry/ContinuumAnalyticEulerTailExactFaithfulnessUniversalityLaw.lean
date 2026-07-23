import GaloisForLFunctions.HTGeometry.AnalyticEulerTailExactFaithfulnessUniversalityLaw
import GaloisForLFunctions.HTGeometry.ContinuumAnalyticEulerTailFaithfulnessUniversalityLaw

/-!
# Continuum analytic Euler-tail exact faithfulness universality

The exact injectivity law discharges the span/kernel condition previously isolated for the sparse
coherent Boolean continuum. Its all-jet images are therefore unconditionally linearly
independent at every shift.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The sparse coherent Boolean continuum has unconditionally independent analytic all-jet
images; the earlier span/kernel condition is automatically satisfied. -/
theorem continuumSparsePrime_analyticAllJet_linearIndependent_exact
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) (a : ℂ) :
    LinearIndependent ℂ
      (fun z : ℕ → Bool =>
        analyticEulerTailAllJetRealization a
          (boundedPrimeOrientationTailClass
            (continuumSparsePrimeOrientation base e z))) := by
  exact linearIndependent_analyticEulerTailAllJetRealization a _
    (continuumSparsePrimeOrientation_boundedTailClass_linearIndependent base e)

/-- One sparse coherent Boolean continuum simultaneously witnesses source rank continuum and
unconditional analytic all-jet faithfulness at every shift. -/
theorem continuumPrime_analyticEulerTailExactFaithfulnessUniversality
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    LinearIndependent ℂ
        (fun z : ℕ → Bool =>
          boundedPrimeOrientationTailClass
            (continuumSparsePrimeOrientation base e z)) ∧
      Cardinal.continuum ≤ Module.rank ℂ BoundedPrimeTailSpace ∧
      ∀ a : ℂ,
        Function.Injective (analyticEulerTailAllJetRealization a) ∧
        LinearIndependent ℂ
          (fun z : ℕ → Bool =>
            analyticEulerTailAllJetRealization a
              (boundedPrimeOrientationTailClass
                (continuumSparsePrimeOrientation base e z))) := by
  exact ⟨
    continuumSparsePrimeOrientation_boundedTailClass_linearIndependent base e,
    continuum_le_rank_boundedPrimeTailSpace base e,
    fun a => ⟨
      analyticEulerTailAllJetRealization_injective a,
      continuumSparsePrime_analyticAllJet_linearIndependent_exact base e a⟩⟩

end

end GaloisForLFunctions.HTGeometry
