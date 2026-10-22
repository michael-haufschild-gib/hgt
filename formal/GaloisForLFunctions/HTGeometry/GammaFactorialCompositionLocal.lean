import GaloisForLFunctions.HTGeometry.GammaFactorialComposition
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence

/-!
# Local factorial blow-up obstruction for compositions `u ∘ Γ`

Let `u` be analytic on the right half-plane `Re z > 0` and `h = u ∘ Γ`. Near the pole `-n` of `Γ`,
the zoom `x ↦ h(-n + ε_n x)` with `ε_n = (-1)^(n+1) / n!` converges to `x ↦ u(1 / (-x))` on
`Re x < 0`. This module shows that a nonzero polynomial differential relation for `h`, required
only eventually along these factorial blow-up points (not on an open set), passes to the limit and
then, via the Möbius change of variables `z = 1 / (-x)`, gives a nonzero polynomial jet relation
for `u` itself on the whole right half-plane. Under a local rigidity assumption on `u` at `1`, such
eventual relations are therefore impossible.

## Main results

- `exists_polynomialJet_relation_on_rightHalfPlane_of_eventual_differentialRelation_outer_comp_Gamma`:
  an eventual relation `P(w, h(w), …, h^(r)(w)) = 0` at `w = -n + ε_n x` for every `x` with
  `Re x < 0` yields a nonzero `G` with polynomial coefficients such that
  `G(z; u(z), …, u^(r)(z)) = 0` for all `Re z > 0`.
- `no_eventual_differential_relation_outer_comp_Gamma`: if moreover `u` is locally
  polynomial-jet rigid at `1`, no nonzero `P` satisfies such an eventual relation.

## Hypotheses

Both theorems assume `hu`: `u` is analytic at every point of the right half-plane. The second is
conditional on `hrigid : LocallyPolynomialJetRigidAt u 1`, the Prop-valued statement that no
nonzero polynomial relation with `ℂ[z]` coefficients among `u, u', …, u^(r)` holds on a
neighbourhood of `1`.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

/-- Assuming `u` is analytic on `Re z > 0`, a nonzero relation `P(w, h, h', …, h^(r)) = 0` for
`h = u ∘ Γ` holding eventually at `w = -n + ε_n x` (`ε_n = (-1)^(n+1) / n!`) for each `Re x < 0`
yields a nonzero jet polynomial `G` over `ℂ[z]` annihilating `u, …, u^(r)` on `Re z > 0`. -/
theorem exists_polynomialJet_relation_on_rightHalfPlane_of_eventual_differentialRelation_outer_comp_Gamma
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    {r : ℕ} (P : MvPolynomial (Fin (r + 2)) ℂ) (hP0 : P ≠ 0)
    (hrel : ∀ x ∈ gammaFactorialMicroscopeDomain, ∀ᶠ n : ℕ in atTop,
      MvPolynomial.eval
        (Fin.cons (-(n : ℂ) + reciprocalGammaFactorialScale n * x)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ)
            (fun z => u (Complex.Gamma z))
            (-(n : ℂ) + reciprocalGammaFactorialScale n * x))) P = 0) :
    ∃ G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      G ≠ 0 ∧ ∀ z ∈ rightHalfPlane,
        MvPolynomial.eval₂ (Polynomial.evalRingHom z)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) u z) G = 0 := by
  obtain ⟨Q, hQ0, hQvan⟩ :=
    exists_nonzero_factorialInitialForm_of_eventual_differentialRelation
      (h := fun z => u (Complex.Gamma z))
      (f := outerReciprocalLimit u) (U := gammaFactorialMicroscopeDomain) P hP0 hrel
      (fun x hx j => iteratedDeriv_outerGamma_factorialBlowUp_tendsto u hu hx j)
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := mobiusJetPullback r Q
  have hGne : G ≠ 0 := mobiusJetPullback_ne_zero hQ0
  refine ⟨G, hGne, ?_⟩
  intro z hz
  have hx : -z⁻¹ ∈ gammaFactorialMicroscopeDomain :=
    neg_inv_mem_gammaFactorialMicroscopeDomain_of_mem_rightHalfPlane hz
  have hvalue := hQvan (-z⁻¹) hx
  have hmv : mobiusJetValue r u z =
      fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (outerReciprocalLimit u) (-z⁻¹) := by
    funext j
    exact mobiusJetValue_outer_eq_limitJet u hu r z hz j
  rw [show G = mobiusJetPullback r Q from rfl, eval₂_mobiusJetPullback, hmv]
  exact hvalue

/-- Assuming `u` is analytic on `Re z > 0` and `hrigid : LocallyPolynomialJetRigidAt u 1`, no
nonzero polynomial `P` gives a differential relation for `u ∘ Γ` that holds eventually along all
factorial blow-up points `-n + ε_n x` with `Re x < 0`. -/
theorem no_eventual_differential_relation_outer_comp_Gamma
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    (hrigid : LocallyPolynomialJetRigidAt u 1)
    {r : ℕ} (P : MvPolynomial (Fin (r + 2)) ℂ) (hP0 : P ≠ 0) :
    ¬ ∀ x ∈ gammaFactorialMicroscopeDomain, ∀ᶠ n : ℕ in atTop,
      MvPolynomial.eval
        (Fin.cons (-(n : ℂ) + reciprocalGammaFactorialScale n * x)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ)
            (fun z => u (Complex.Gamma z))
            (-(n : ℂ) + reciprocalGammaFactorialScale n * x))) P = 0 := by
  intro hrel
  obtain ⟨G, hG, hGvan⟩ :=
    exists_polynomialJet_relation_on_rightHalfPlane_of_eventual_differentialRelation_outer_comp_Gamma
      u hu P hP0 hrel
  apply (hrigid r G hG)
  have honePos : (1 : ℂ) ∈ rightHalfPlane := by simp [rightHalfPlane]
  filter_upwards [isOpen_rightHalfPlane.mem_nhds honePos] with z hz
  exact hGvan z hz

end

end GaloisForLFunctions
