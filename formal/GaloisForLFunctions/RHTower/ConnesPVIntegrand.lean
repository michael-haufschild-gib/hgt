import GaloisForLFunctions.RHTower.ConnesPrincipalValueInverse

/-!
# The principal-value integrand as a single integrable function

Step 1b (continued) of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`connesPVinv` was defined as a sum of two set integrals.  For the Fubini/Riemann–Lebesgue argument
it is more convenient to have one globally integrable function whose integral is that sum:

  `H(u) = (G(u) − G(0)·1_{|u| ≤ 1}(u)) / u`.

This module constructs `H`, proves it integrable, and identifies `∫ H = PV ∫ G/u`.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The globally integrable principal-value integrand. -/
def connesPVintegrand (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  (G u - Set.indicator {v : ℝ | |v| ≤ 1} (fun _ => G 0) u) / u

theorem connes_unitBall_compl : ({v : ℝ | |v| ≤ 1} : Set ℝ)ᶜ = {v : ℝ | 1 < |v|} := by
  ext v
  simp [not_le]

theorem connes_pvIntegrand_on_ball {G : ℝ → ℂ} {u : ℝ} (hu : u ∈ {v : ℝ | |v| ≤ 1}) :
    connesPVintegrand G u = (G u - G 0) / u := by
  rw [connesPVintegrand, Set.indicator_of_mem hu]

theorem connes_pvIntegrand_off_ball {G : ℝ → ℂ} {u : ℝ} (hu : u ∉ {v : ℝ | |v| ≤ 1}) :
    connesPVintegrand G u = G u / u := by
  rw [connesPVintegrand, Set.indicator_of_notMem hu, sub_zero]

theorem connes_pvIntegrand_integrableOn_ball (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (connesPVintegrand (G : ℝ → ℂ)) {v : ℝ | |v| ≤ 1} volume := by
  refine (connes_pv_inner_integrable G).congr_fun ?_ connes_unitBall_measurable
  intro u hu
  exact (connes_pvIntegrand_on_ball hu).symm

theorem connes_pvIntegrand_integrableOn_compl (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (connesPVintegrand (G : ℝ → ℂ)) ({v : ℝ | |v| ≤ 1}ᶜ) volume := by
  rw [connes_unitBall_compl]
  refine (connes_pv_outer_integrable G).congr_fun ?_ connes_unitBallCompl_measurable
  intro u hu
  refine (connes_pvIntegrand_off_ball ?_).symm
  rw [← connes_unitBall_compl] at hu
  exact hu

theorem connes_pvIntegrand_integrable (G : 𝓢(ℝ, ℂ)) :
    Integrable (connesPVintegrand (G : ℝ → ℂ)) volume := by
  have huniv : (Set.univ : Set ℝ) = {v : ℝ | |v| ≤ 1} ∪ ({v : ℝ | |v| ≤ 1}ᶜ) :=
    (Set.union_compl_self _).symm
  rw [← MeasureTheory.integrableOn_univ, huniv]
  exact (connes_pvIntegrand_integrableOn_ball G).union
    (connes_pvIntegrand_integrableOn_compl G)

/-- **The principal value as a single integral.** -/
theorem connes_integral_pvIntegrand (G : 𝓢(ℝ, ℂ)) :
    (∫ u : ℝ, connesPVintegrand (G : ℝ → ℂ) u) = connesPVinv (G : ℝ → ℂ) := by
  have huniv : (Set.univ : Set ℝ) = {v : ℝ | |v| ≤ 1} ∪ ({v : ℝ | |v| ≤ 1}ᶜ) :=
    (Set.union_compl_self _).symm
  have hdisj : Disjoint ({v : ℝ | |v| ≤ 1}) (({v : ℝ | |v| ≤ 1}ᶜ)) :=
    disjoint_compl_right
  have hsplit : (∫ u : ℝ, connesPVintegrand (G : ℝ → ℂ) u)
      = (∫ u in {v : ℝ | |v| ≤ 1}, connesPVintegrand (G : ℝ → ℂ) u)
        + ∫ u in ({v : ℝ | |v| ≤ 1}ᶜ), connesPVintegrand (G : ℝ → ℂ) u := by
    rw [← MeasureTheory.setIntegral_univ, huniv,
      MeasureTheory.setIntegral_union hdisj (connes_unitBall_measurable.compl)
        (connes_pvIntegrand_integrableOn_ball G) (connes_pvIntegrand_integrableOn_compl G)]
  rw [hsplit, connesPVinv]
  congr 1
  · refine MeasureTheory.setIntegral_congr_fun connes_unitBall_measurable fun u hu => ?_
    exact connes_pvIntegrand_on_ball hu
  · rw [connes_unitBall_compl]
    refine MeasureTheory.setIntegral_congr_fun connes_unitBallCompl_measurable fun u hu => ?_
    refine connes_pvIntegrand_off_ball ?_
    rw [← connes_unitBall_compl] at hu
    exact hu

end

end GaloisForLFunctions.RHTower
