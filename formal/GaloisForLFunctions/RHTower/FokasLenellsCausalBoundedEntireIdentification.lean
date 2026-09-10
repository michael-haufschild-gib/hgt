import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedEntireOrbit
import GaloisForLFunctions.RHTower.FokasLenellsCausalGraphShift
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The bounded genuine derivative-shift exponential is the actual causal orbit.
Dissipativity closes the identification without any assumed uniqueness or orbit hypothesis. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance : InnerProductSpace ℝ (hardyL2ᗮ) := InnerProductSpace.rclikeToReal ℂ (hardyL2ᗮ)

private def realOrbitDomain (j : ℕ) (u : causalBoundedChain) (r : ℝ) : causalGeneratorDomain :=
  causalGeneratorGraphDomain (causalGeneratorGraphEvolution r.toNNReal
    (causalGeneratorDomainGraph (causalSmoothGraphDomainCoordinate j (causalBoundedChainToSmooth u))))

private theorem generator_realOrbitDomain (j : ℕ) (u : causalBoundedChain) (r : ℝ) :
    causalGenerator (realOrbitDomain j u r) =
      causalForwardOrbit (causalBoundedChainCoordinate (j+1) u) r := by
  have h := congrArg (fun p : causalGeneratorGraph => p.val.2)
    (causalGeneratorDomainGraph_graphDomain (causalGeneratorGraphEvolution r.toNNReal
      (causalGeneratorDomainGraph (causalSmoothGraphDomainCoordinate j (causalBoundedChainToSmooth u)))))
  change causalGenerator (realOrbitDomain j u r) =
    causalLowerCauchyEvolution r.toNNReal
      (causalGenerator (causalSmoothGraphDomainCoordinate j (causalBoundedChainToSmooth u))) at h
  rw [causalGenerator_smoothGraphCoordinate] at h
  exact h

private def boundedOrbitError (j : ℕ) (u : causalBoundedChain) (r : ℝ) : hardyL2ᗮ :=
  causalBoundedEntireOrbit j u (r : ℂ) - causalForwardOrbit (causalBoundedChainCoordinate j u) r

private theorem boundedOrbitError_continuous (j : ℕ) (u : causalBoundedChain) :
    Continuous (boundedOrbitError j u) := by
  exact ((show Continuous (fun r : ℝ => causalBoundedEntireOrbit j u (r : ℂ)) from
    continuous_iff_continuousAt.2 (fun r =>
      (causalBoundedEntireOrbit_hasRealDerivAt j u r).continuousAt))).sub
    (causalForwardOrbit_continuous _)

private theorem boundedOrbitError_hasDerivAt (j : ℕ) (u : causalBoundedChain)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (boundedOrbitError j u) (boundedOrbitError (j+1) u r) r := by
  have h := causalGenerator_positiveOrbit_hasDerivAt (Real.log r)
    (causalSmoothGraphDomainCoordinate j (causalBoundedChainToSmooth u))
  rw [Real.exp_log hr, causalGenerator_smoothGraphCoordinate] at h
  exact (causalBoundedEntireOrbit_hasRealDerivAt j u r).sub h

private theorem boundedOrbitError_energy_nonpos (j : ℕ) (u : causalBoundedChain)
    {r : ℝ} (hr : 0 < r) :
    deriv (fun t : ℝ => ‖boundedOrbitError j u t‖^2) r ≤ 0 := by
  have hd := causalGenerator_dissipative
    (causalBoundedEntireDomain j u (r : ℂ) - realOrbitDomain j u r)
  rw [map_sub, causalGenerator_boundedEntireDomain, generator_realOrbitDomain] at hd
  change inner ℝ (boundedOrbitError j u r) (boundedOrbitError (j+1) u r) ≤ 0 at hd
  rw [(boundedOrbitError_hasDerivAt j u hr).norm_sq.deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hd

/-- The entire bounded-shift curve agrees exactly with the original causal evolution at real time. -/
theorem causalBoundedEntireOrbit_eq_evolution (j : ℕ) (u : causalBoundedChain) (t : ℝ≥0) :
    causalBoundedEntireOrbit j u ((t : ℝ) : ℂ) =
      causalLowerCauchyEvolution t (causalBoundedChainCoordinate j u) := by
  have hc : Continuous (fun r : ℝ => ‖boundedOrbitError j u r‖^2) :=
    (boundedOrbitError_continuous j u).norm.pow 2
  have hm : AntitoneOn (fun r : ℝ => ‖boundedOrbitError j u r‖^2) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hc.continuousOn
    · intro r hr
      rw [interior_Ici] at hr
      exact (boundedOrbitError_hasDerivAt j u hr).norm_sq.differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      exact boundedOrbitError_energy_nonpos j u hr
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := by
    change (0 : ℝ) ≤ 0
    exact le_refl 0
  have h := hm h0 t.property t.property
  have hz : boundedOrbitError j u 0 = 0 := by
    simp only [boundedOrbitError, Complex.ofReal_zero, causalBoundedEntireOrbit_zero,
      causalForwardOrbit_zero, sub_self]
  change ‖boundedOrbitError j u (t : ℝ)‖^2 ≤ ‖boundedOrbitError j u 0‖^2 at h
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
  have he : boundedOrbitError j u (t : ℝ) = 0 := by
    apply norm_eq_zero.mp
    nlinarith only [h, norm_nonneg (boundedOrbitError j u (t : ℝ))]
  change causalBoundedEntireOrbit j u ((t : ℝ) : ℂ) -
    causalLowerCauchyEvolution (Real.toNNReal (t : ℝ)) (causalBoundedChainCoordinate j u) = 0 at he
  simpa only [Real.toNNReal_coe] using sub_eq_zero.mp he

/-- Every genuine bounded derivative coordinate has an entire extension of its actual causal orbit. -/
theorem causalBoundedChainCoordinate_entire_extension (j : ℕ) (u : causalBoundedChain) :
    ∃ f : ℂ → hardyL2ᗮ, (∀ z : ℂ, AnalyticAt ℂ f z) ∧
      ∀ t : ℝ≥0, f ((t : ℝ) : ℂ) = causalLowerCauchyEvolution t (causalBoundedChainCoordinate j u) :=
  ⟨causalBoundedEntireOrbit j u, causalBoundedEntireOrbit_analyticAt j u,
    causalBoundedEntireOrbit_eq_evolution j u⟩

end
end RHTower.FokasLenells
