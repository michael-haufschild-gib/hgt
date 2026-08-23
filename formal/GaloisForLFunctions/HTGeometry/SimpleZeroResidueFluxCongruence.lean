import GaloisForLFunctions.HTGeometry.FiniteJetQuotientCongruence
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- At a simple zero, the canonical residue-filled flux germ is the germ of the
regular logarithmic flux of its divided unit in the translated coordinate. -/
theorem fluxGerm_eventuallyEq_simpleZeroResidueFlux {f u : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hu : Differentiable ℂ u)
    (hfac : ∀ z, f z = (z - ρ) * u z) (hu0 : u ρ ≠ 0) :
    fluxGerm f ρ =ᶠ[𝓝 0] simpleZeroResidueFlux (fun x => u (x + ρ)) := by
  have hfun : f = fun z => (z - ρ) * u z := funext hfac
  have hroot : f ρ = 0 := by rw [hfac]; simp
  have hderiv : deriv f ρ = u ρ := by
    rw [hfun]
    change deriv ((fun z : ℂ => z - ρ) * u) ρ = u ρ
    simpa using (((hasDerivAt_id ρ).sub_const ρ).mul (hu ρ).hasDerivAt).deriv
  have hderivne : deriv f ρ ≠ 0 := by rwa [hderiv]
  have hord : analyticOrderAt f ρ = (1 : ℕ∞) :=
    hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hroot hderivne
  have hne : ∀ᶠ x : ℂ in 𝓝 0, u (x + ρ) ≠ 0 := by
    have hT : ContinuousAt (fun x : ℂ => x + ρ) 0 := by fun_prop
    have hUne : ∀ᶠ y in 𝓝 ρ, u y ≠ 0 :=
      (hu.continuous.continuousAt : ContinuousAt u ρ).eventually_ne hu0
    have hUne' : ∀ᶠ y in 𝓝 ((0 : ℂ) + ρ), u y ≠ 0 := by
      simpa using hUne
    exact hT.tendsto.eventually hUne'
  filter_upwards [hne] with x hx
  by_cases hx0 : x = 0
  · subst x
    rw [fluxGerm_zero, hord]
    simp [simpleZeroResidueFlux]
  · rw [fluxGerm_of_ne_zero f ρ hx0, hfac (ρ + x)]
    have hderivfac : deriv f (ρ + x) = u (ρ + x) + x * deriv u (ρ + x) := by
      rw [hfun]
      change deriv ((fun z : ℂ => z - ρ) * u) (ρ + x) = _
      have h := (((hasDerivAt_id (ρ + x)).sub_const ρ).mul
        (hu (ρ + x)).hasDerivAt).deriv
      simpa using h
    rw [hderivfac]
    have hshiftderiv : deriv (fun y => u (y + ρ)) x = deriv u (x + ρ) := by
      rw [← iteratedDeriv_one, iteratedDeriv_comp_add_const, iteratedDeriv_one]
    rw [simpleZeroResidueFlux, hshiftderiv]
    have hx' : u (ρ + x) = u (x + ρ) := by ring
    rw [hx']
    field_simp [hx0, hx]
    ring

end GaloisForLFunctions.HTGeometry
