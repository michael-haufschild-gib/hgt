import GaloisForLFunctions.RHTower.WeilPaperSymmetricObservationCubes
import GaloisForLFunctions.RHTower.WeilPaperSpectralAffineContinuity

/-!
# Closed topological cubes in finite-observation fibers

The symmetric affine constructions are closed embeddings for the weak topology
of actual representing probabilities. Finite observations therefore miss entire
compact topological cubes, with no bound on their finite dimension.
-/

open MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Every finite observer has a fiber containing a closed embedded cube of every
finite dimension, realized by real tests and symmetric spectral probabilities. -/
theorem exists_closedEmbedding_symmetric_spectralRepresentingMeasure_cube (k n : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, T (c s).1.1 = T (c t).1.1) ∧
      (∀ t f, (c t).1.1 f ≠ 0 → ∀ y, (f.1 y).im = 0) ∧
      (∀ t, Measure.map (fun ξ : ℝ => -ξ) (spectralProbability (c t).1 : Measure ℝ) =
        (spectralProbability (c t).1 : Measure ℝ)) ∧
      (∀ t, Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace)) ∧
      Topology.IsClosedEmbedding (fun t => spectralRepresentingMeasure (c t)) := by
  obtain ⟨c, b, L, hL, haff, hT, hr, hs, ht, hinj⟩ :=
    exists_symmetric_spectralRepresentingMeasure_cube k n T
  exact ⟨c, b, L, hL, haff, hT, hr, hs, ht,
    (continuous_spectralRepresentingMeasure_affine_cube c b L haff).isClosedEmbedding hinj⟩

/-- A closed embedded symmetric cube survives fixing the full energy and any finite
list of complex samples. Every finite dimension occurs unconditionally. -/
theorem exists_closedEmbedding_symmetric_spectralRepresentingMeasure_cube_same_energy_samples
    (n : ℕ) {k : ℕ} (y : Fin k → ℝ) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, energy (c s).1.1 = energy (c t).1.1) ∧
      (∀ i s t, mixtureSample (c s).1.1 (y i) = mixtureSample (c t).1.1 (y i)) ∧
      (∀ t f, (c t).1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
      (∀ t, Measure.map (fun ξ : ℝ => -ξ) (spectralProbability (c t).1 : Measure ℝ) =
        (spectralProbability (c t).1 : Measure ℝ)) ∧
      (∀ t, Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace)) ∧
      Topology.IsClosedEmbedding (fun t => spectralRepresentingMeasure (c t)) := by
  obtain ⟨c, b, L, hL, haff, hE, hsamp, hr, hs, ht, hinj⟩ :=
    exists_symmetric_spectralRepresentingMeasure_cube_same_energy_samples n y
  exact ⟨c, b, L, hL, haff, hE, hsamp, hr, hs, ht,
    (continuous_spectralRepresentingMeasure_affine_cube c b L haff).isClosedEmbedding hinj⟩

/-- Full energy and any finite list of bounded continuous spectral expectations
are constant on a closed embedded symmetric cube of every finite dimension. -/
theorem exists_closedEmbedding_symmetric_spectralRepresentingMeasure_cube_same_expectations
    (n : ℕ) {k : ℕ} (F : Fin k → (ℝ →ᵇ ℝ)) :
    ∃ (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
      (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ)),
      Function.Injective L ∧ (∀ t, (c t).1.1 = b + L (fun i => (t i).1)) ∧
      (∀ s t, energy (c s).1.1 = energy (c t).1.1) ∧
      (∀ i s t, (∫ ξ, F i ξ ∂(spectralProbability (c s).1 : Measure ℝ)) =
        ∫ ξ, F i ξ ∂(spectralProbability (c t).1 : Measure ℝ)) ∧
      (∀ t f, (c t).1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
      (∀ t, Measure.map (fun ξ : ℝ => -ξ) (spectralProbability (c t).1 : Measure ℝ) =
        (spectralProbability (c t).1 : Measure ℝ)) ∧
      (∀ t, Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure (c t)).1 : Measure PrimePhaseSpace)) ∧
      Topology.IsClosedEmbedding (fun t => spectralRepresentingMeasure (c t)) := by
  let E := ℝ × (Fin k → ℝ)
  let Q : (WeilTestFn →₀ ℝ) →ₗ[ℝ] E :=
    energy.prod (LinearMap.pi fun i => paperSpectralIntegralObserver (F i))
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  obtain ⟨c, b, L, hL, haff, hT, hr, hs, ht, hemb⟩ :=
    exists_closedEmbedding_symmetric_spectralRepresentingMeasure_cube
      (Module.finrank ℝ E) n (e.toLinearMap.comp Q)
  have hQ s t : Q (c s).1.1 = Q (c t).1.1 := e.injective (hT s t)
  refine ⟨c, b, L, hL, haff, fun s t => congrArg Prod.fst (hQ s t), ?_, hr, hs, ht, hemb⟩
  intro i s t
  rw [integral_spectralProbability_eq_paperSpectralIntegralObserver,
    integral_spectralProbability_eq_paperSpectralIntegralObserver]
  exact congrFun (congrArg Prod.snd (hQ s t)) i

end RHTower.WeilWorkPBAP
