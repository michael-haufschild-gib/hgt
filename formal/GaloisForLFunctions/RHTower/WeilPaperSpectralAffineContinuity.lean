import GaloisForLFunctions.RHTower.WeilWorkPBAPSpectralMeasure

/-!
# Weak continuity of finite affine spectral families

Every bounded continuous spectral observable is a linear functional of the finite
mixture coefficients. Consequently affine finite-dimensional families vary
continuously in the weak topology of their actual spectral probabilities.
-/

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Origin-representing measures inherit the weak subspace topology. -/
instance instTopologicalSpaceRepresentingPhaseMeasure : TopologicalSpace RepresentingPhaseMeasure := by
  unfold RepresentingPhaseMeasure
  infer_instance

/-- Weakly distinct representing probabilities are topologically separated. -/
instance instT2SpaceRepresentingPhaseMeasure : T2Space RepresentingPhaseMeasure := by
  exact inferInstanceAs (T2Space {μ : ProbabilityMeasure PrimePhaseSpace //
    ∀ n : ℕ, 2 ≤ n → ∫ z, arithmeticPhase n z ∂(μ : Measure PrimePhaseSpace) = 0})

/-- The bounded spectral observable as a linear functional on signed test mixtures. -/
def paperSpectralIntegralObserver (F : ℝ →ᵇ ℝ) : (WeilTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun f => ∫ ξ, testSpectralDensity f ξ * F ξ)

/-- The finite coefficient functional equals integration against the signed density. -/
theorem paperSpectralIntegralObserver_apply (F : ℝ →ᵇ ℝ) (c : WeilTestFn →₀ ℝ) :
    paperSpectralIntegralObserver F c = ∫ ξ, mixtureSpectralDensity c ξ * F ξ := by
  classical
  have hint f : Integrable (fun ξ => testSpectralDensity f ξ * F ξ) :=
    (integrable_testSpectralDensity f).mul_bdd F.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall F.norm_coe_le_norm)
  simp only [paperSpectralIntegralObserver, Finsupp.linearCombination_apply,
    Finsupp.sum, smul_eq_mul]
  calc
    _ = ∑ f ∈ c.support, ∫ ξ, c f * (testSpectralDensity f ξ * F ξ) := by
      simp_rw [integral_const_mul]
    _ = ∫ ξ, ∑ f ∈ c.support, c f * (testSpectralDensity f ξ * F ξ) :=
      (integral_finsetSum _ fun f _ => (hint f).const_mul (c f)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp [mixtureSpectralDensity, Finsupp.sum, Finset.sum_mul, mul_assoc]

/-- Expectations under the actual probability are linear in mixture coefficients. -/
theorem integral_spectralProbability_eq_paperSpectralIntegralObserver
    (F : ℝ →ᵇ ℝ) (c : NormalizedMixture) :
    ∫ ξ, F ξ ∂(spectralProbability c : Measure ℝ) = paperSpectralIntegralObserver F c.1 := by
  rw [paperSpectralIntegralObserver_apply]
  change ∫ ξ, F ξ ∂volume.withDensity
    (fun ξ => ENNReal.ofReal (mixtureSpectralDensity c.1 ξ)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_mixtureSpectralDensity c.1).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [ENNReal.toReal_ofReal (mixtureSpectralDensity_nonneg c.1 c.2.1 ξ), smul_eq_mul]

/-- Every normalized affine cube has weakly continuous actual spectral probabilities. -/
theorem continuous_spectralProbability_affine_cube {n : ℕ}
    (c : (Fin n → Set.Icc (0 : ℝ) 1) → NormalizedMixture)
    (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ))
    (haff : ∀ t, (c t).1 = b + L (fun i => (t i).1)) :
    Continuous (fun t => spectralProbability (c t)) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro F
  have ht : Continuous (fun t : Fin n → Set.Icc (0 : ℝ) 1 => fun i => (t i).1) :=
    continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)
  have hcont : Continuous (fun t : Fin n → Set.Icc (0 : ℝ) 1 =>
      paperSpectralIntegralObserver F b +
      (paperSpectralIntegralObserver F).comp L (fun i => (t i).1)) :=
    continuous_const.add (((paperSpectralIntegralObserver F).comp L).continuous_of_finiteDimensional.comp ht)
  exact hcont.congr fun t => by
    rw [integral_spectralProbability_eq_paperSpectralIntegralObserver, haff, map_add]
    rfl

/-- The compact prime-torus laws inherit weak continuity from the real spectral laws. -/
theorem continuous_spectralTorusProbability_affine_cube {n : ℕ}
    (c : (Fin n → Set.Icc (0 : ℝ) 1) → NormalizedMixture)
    (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ))
    (haff : ∀ t, (c t).1 = b + L (fun i => (t i).1)) :
    Continuous (fun t => spectralTorusProbability (c t)) :=
  (ProbabilityMeasure.continuous_map continuous_primeSpectralPoint).comp
    (continuous_spectralProbability_affine_cube c b L haff)

/-- Continuity also holds in the subspace of origin-representing probabilities. -/
theorem continuous_spectralRepresentingMeasure_affine_cube {n : ℕ}
    (c : (Fin n → Set.Icc (0 : ℝ) 1) → ComplexNullMixture)
    (b : WeilTestFn →₀ ℝ) (L : (Fin n → ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ))
    (haff : ∀ t, (c t).1.1 = b + L (fun i => (t i).1)) :
    Continuous (fun t => spectralRepresentingMeasure (c t)) :=
  (continuous_spectralTorusProbability_affine_cube (fun t => (c t).1) b L haff).subtype_mk _

end RHTower.WeilWorkPBAP
