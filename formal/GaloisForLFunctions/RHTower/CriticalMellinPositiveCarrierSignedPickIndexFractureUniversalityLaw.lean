import GaloisForLFunctions.HTGeometry.MeasureCarrier
import GaloisForLFunctions.RHTower.CCMRawStieltjesPickKernelIndexInflationUniversalityLaw

/-!
# Critical-Mellin positive-carrier / signed-Pick index-fracture universality law

The critical-Mellin source separates sharply into two Pick phases.  Its finite positive polar
measure has positive-semidefinite Cauchy Pick Grams at every upper-half-plane packet.  Restoring
the actual signed prime-power atoms creates negative-definite chambers of arbitrarily large finite
index, at maximal chamber distance from positivity.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MeasureTheory
open MeasureTheory Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Matrix

/-- **Critical-Mellin positive-carrier / signed-Pick index-fracture universality law.**  The
positive polar carrier is Pick-positive at every finite rank, while the actual signed source has
unbounded finite negative Pick index. -/
theorem criticalMellinPositiveCarrier_signedPickIndexFracture_universality :
    (∀ (A : ℝ) {n : ℕ} (z : Fin n → ℂ), (∀ j, 0 < (z j).im) →
      (Matrix.of (fun j k =>
        ∫ lam, ((lam : ℂ) - z j)⁻¹ * star (((lam : ℂ) - z k)⁻¹)
          ∂(criticalMellinPolarMeasure A))).PosSemidef) ∧
      ∀ d : ℕ, ∃ A : ℝ,
        d ≤ (activeCriticalMellinAtoms A).card ∧
        hammingDist
          (signPattern
            (criticalMellinSelectedCoefficients (activeCriticalMellinAtom A)))
          (positiveChamber (activeCriticalMellinAtoms A).card) =
            (activeCriticalMellinAtoms A).card ∧
        (∀ᶠ y : ℝ in 𝓝[≠] 0,
          ∀ x : Fin (activeCriticalMellinAtoms A).card → ℂ, x ≠ 0 →
            (star x ⬝ᵥ
              (criticalMellinSelectedPickKernel
                A (activeCriticalMellinAtom A) y).mulVec x).re < 0) := by
  constructor
  · intro A n z hz
    letI : IsFiniteMeasure (criticalMellinPolarMeasure A) :=
      criticalMellinPolarMeasure_isFinite A
    exact GaloisForLFunctions.measure_pick_posSemidef
      (criticalMellinPolarMeasure A) z hz
  · exact exists_activeCriticalMellinPickKernel_chamber_grade_ge

end

end RHTower
