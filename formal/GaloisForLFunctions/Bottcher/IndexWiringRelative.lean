/-
# Relative-case wiring: analytic-coefficient branch + functional equation for the index route

The index obstruction endpoint `IndexResonance.false_of_branches_repelling_fixed` is coefficient-agnostic —
it consumes only an analytic branch `g` with `g z₀ = ζ ≠ 0`, the Böttcher functional equation, and
`deriv g z₀ ≠ 0`. So the **relative** hRigid case (the bivariate no-relation `hno`, with analytic
coefficients `a_i z = (Q_i)(z, φ_{c₂} z)`) reuses the same endpoint; only the branch + functional equation
must be produced from the *analytic-coefficient* relation rather than the polynomial one.

`exists_branch_with_FE_analytic` does exactly that, extracted from the `g`+`heq` derivation inside
`RelativeBranchFamily.false_of_repelling_branch_analytic`: the local algebraic branch `g`
(`exists_analyticAt_branch_analytic`) matches the basin Böttcher branch `β` on the basin side
(`branch_unique_within_analytic`), so it inherits the functional equation across the Julia point `z₀` by the
identity theorem (the analytic `D = g∘f^[p] − g^{2^p}` vanishes on the basin, hence on a full neighbourhood).
Unlike the absolute case (whose functional equation comes from polynomial divisibility), here it comes from
the genuine basin branch `β = φ_{c₁}` and `bottcherCoord_iterate`.

New file (hRigid / connected lane, relative index wiring). Consumes the relative branch spine.
-/
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.Bottcher.PeriodicPoints
import GaloisForLFunctions.Bottcher.RelativeRigidityCapstone
import GaloisForLFunctions.Bottcher.IndexResonance

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-- **Analytic-coefficient branch + Böttcher functional equation, from the basin branch.** At a fixed point
`z₀` of `f_{c₁}^[p]` on `J_{c₁}` (basin accumulating, `hNeBot`), given a simple root `(z₀, w₀)` of an
analytic-coefficient relation and a basin Böttcher branch `β` carrying the relation and the functional
equation on the basin side, the local algebraic branch `g` of the relation is analytic at `z₀`, has
`g z₀ = w₀`, and satisfies the Böttcher functional equation `g(f^[p] z) = (g z)^{2^p}` on a full
neighbourhood of `z₀`. (The branch matches `β` on the basin via `branch_unique_within_analytic`; the
analytic `g∘f^[p] − g^{2^p}` then vanishes on the basin, hence everywhere near `z₀` by the identity
theorem.) This is the relative analogue of `IndexWiring.exists_branch_with_FE`. -/
theorem exists_branch_with_FE_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hz₀ : z₀ ∈ filledJulia c₁) (hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot)
    (hFz : (quadratic c₁)^[p] z₀ = z₀)
    (hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβfe : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀,
        β ((quadratic c₁)^[p] z) = (β z) ^ (2 ^ p)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = w₀ ∧
      (∀ᶠ z in 𝓝 z₀, ∑ i ∈ s, a i z * (g z) ^ i = 0) ∧
      (fun z => g ((quadratic c₁)^[p] z)) =ᶠ[𝓝 z₀] (fun z => (g z) ^ (2 ^ p)) := by
  haveI := hNeBot
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_analytic ha hroot hpartial hd
  have hacont : ∀ i ∈ s, ContinuousAt (a i) z₀ := fun i hi => (ha i hi).continuousAt
  have hmatch : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, g z = β z :=
    branch_unique_within_analytic hacont hpartial hd hgAt.continuousAt hgz₀ hβlim
      (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
  obtain ⟨O, hOopen, hz₀O, hOsub⟩ := mem_nhdsWithin.mp hmatch
  have hfpAt : ContinuousAt ((quadratic c₁)^[p]) z₀ :=
    (analyticOnNhd_quadratic_iterate c₁ p z₀ (mem_univ _)).continuousAt
  have hfpO : ∀ᶠ z in 𝓝 z₀, (quadratic c₁)^[p] z ∈ O :=
    hfpAt.eventually (hOopen.mem_nhds (by rw [hFz]; exact hz₀O))
  have hgfe_basin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀,
      g ((quadratic c₁)^[p] z) = (g z) ^ (2 ^ p) := by
    filter_upwards [hmatch, hβfe, self_mem_nhdsWithin,
      hfpO.filter_mono nhdsWithin_le_nhds] with z hgz hβz hzbasin hfpOz
    have hfpbasin : (quadratic c₁)^[p] z ∉ filledJulia c₁ := not_mem_filledJulia_iterate hzbasin p
    have hgfp : g ((quadratic c₁)^[p] z) = β ((quadratic c₁)^[p] z) := hOsub ⟨hfpOz, hfpbasin⟩
    rw [hgfp, hβz, hgz]
  set D : ℂ → ℂ := fun z => g ((quadratic c₁)^[p] z) - (g z) ^ (2 ^ p) with hDdef
  have hDAt : AnalyticAt ℂ D z₀ := by
    apply AnalyticAt.sub
    · have hg' : AnalyticAt ℂ g ((quadratic c₁)^[p] z₀) := by rw [hFz]; exact hgAt
      exact hg'.comp (analyticOnNhd_quadratic_iterate c₁ p z₀ (mem_univ _))
    · exact hgAt.pow (2 ^ p)
  have hDbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, D z = 0 := by
    filter_upwards [hgfe_basin] with z hz; rw [hDdef]; simp only; rw [hz, sub_self]
  have hsubNE : 𝓝[(filledJulia c₁)ᶜ] z₀ ≤ 𝓝[≠] z₀ := by
    apply nhdsWithin_mono
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hx hz₀
  have hDfull : ∀ᶠ z in 𝓝 z₀, D z = 0 := by
    rcases hDAt.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exact absurd (hDbasin.frequently.and_eventually (h.filter_mono hsubNE)).exists
        (fun ⟨z, hz⟩ => hz.2 hz.1)
  have heq : (fun z => g ((quadratic c₁)^[p] z)) =ᶠ[𝓝 z₀] (fun z => (g z) ^ (2 ^ p)) := by
    filter_upwards [hDfull] with z hz; rw [← sub_eq_zero]; exact hz
  exact ⟨g, hgAt, hgz₀, hgrel, heq⟩

/-- **The index branch tuple from an analytic-coefficient relation + basin branch.** Relative analogue of
`IndexWiring.exists_index_branch_tuple`: packages `exists_branch_with_FE_analytic` (nonzero value `w₀` and
non-constant branch `deriv g z₀ ≠ 0` as genericity on the constructed branch) into exactly the existential
`IndexResonance.false_of_branches_repelling_fixed` consumes. -/
theorem exists_index_branch_tuple_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hz₀ : z₀ ∈ filledJulia c₁) (hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot)
    (hFz : (quadratic c₁)^[p] z₀ = z₀)
    (hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβfe : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β ((quadratic c₁)^[p] z) = (β z) ^ (2 ^ p))
    (hw0ne : w₀ ≠ 0)
    (hgen : ∀ g : ℂ → ℂ, AnalyticAt ℂ g z₀ → g z₀ = w₀ →
        (∀ᶠ z in 𝓝 z₀, ∑ i ∈ s, a i z * (g z) ^ i = 0) → deriv g z₀ ≠ 0) :
    ∃ (g : ℂ → ℂ) (ζ : ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ = ζ ∧ ζ ≠ 0 ∧
      (fun y => g ((quadratic c₁)^[p] y)) =ᶠ[𝓝 z₀] (fun y => g y ^ (2 ^ p)) ∧
      deriv g z₀ ≠ 0 := by
  obtain ⟨g, hgAt, hgz₀, hgrel, heq⟩ :=
    exists_branch_with_FE_analytic ha hroot hpartial hd hz₀ hNeBot hFz hβlim hβrel hβfe
  exact ⟨g, w₀, hgAt, hgz₀, hw0ne, heq, hgen g hgAt hgz₀ hgrel⟩

/-- **The relative connected obstruction from an analytic-coefficient relation (no-attracting-fixed-point).**
Relative analogue of `IndexWiring.false_of_relation_bulk_branches`: an analytic-coefficient relation
`∑ a_i(z)·w^i` (the cleared bivariate relation `a_i = (Q_i)(·, φ_{c₂})`) cannot coexist with `B` a set of
repelling fixed points of `f_{c₁}` and, at every period-`p` cycle point off `B`, the **relative branch
datum** — a simple root `(z, w₀)` with `w₀ ≠ 0`, a basin Böttcher branch `β` carrying the relation and the
functional equation on the basin side (`NeBot`, `hβlim`, `hβrel`, `hβfe`), and the non-constancy genericity
(`hgen`) — together with the small exceptional mass. `exists_index_branch_tuple_analytic` turns each datum
into the index branch tuple; `false_of_branches_repelling_fixed` (the coefficient-agnostic index
obstruction) closes it. This is the relative leg of the index route — the bivariate `hno` reduced to the
basin-branch datum on the cycle, no ergodic input. -/
theorem false_of_relative_bulk_branches {c₁ : ℂ} {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c₁ p).Separable)
    (a : ℕ → ℂ → ℂ) (s : Finset ℕ)
    (B : Finset ℂ) (hBfix : ∀ z ∈ B, quadratic c₁ z = z) (hBrep : ∀ z ∈ B, 1 < ‖2 * z‖)
    (hbulk : ∀ z ∈ (fixedPointPoly c₁ p).roots.toFinset \ B,
        ∃ (w₀ d : ℂ) (β : ℂ → ℂ),
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z) ∧
          (∑ i ∈ s, a i z * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ s, a i z * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (𝓝[(filledJulia c₁)ᶜ] z).NeBot ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z) (𝓝 w₀) ∧
          (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z, ∑ i ∈ s, a i y * (β y) ^ i = 0) ∧
          (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z, β ((quadratic c₁)^[p] y) = (β y) ^ (2 ^ p)) ∧
          w₀ ≠ 0 ∧
          (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
            (∀ᶠ y in 𝓝 z, ∑ i ∈ s, a i y * (g y) ^ i = 0) → deriv g z ≠ 0))
    (hsmall : ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
      < (((fixedPointPoly c₁ p).roots.toFinset \ B).card : ℝ)) :
    False := by
  refine false_of_branches_repelling_fixed c₁ hp hsep B hBfix hBrep ?_ hsmall
  intro z hz
  obtain ⟨w₀, d, β, ha, hroot, hpartial, hd, hNeBot, hβlim, hβrel, hβfe, hw0ne, hgen⟩ := hbulk z hz
  have hFz : (quadratic c₁)^[p] z = z := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c₁ hp)).mp
      (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1)
  have hz₀ : z ∈ filledJulia c₁ := mem_filledJulia_of_periodic hp hFz
  exact exists_index_branch_tuple_analytic ha hroot hpartial hd hz₀ hNeBot hFz hβlim hβrel hβfe hw0ne hgen

/-- **The hRigid connected-case rigidity input, via the index route (top-level).** The index analogue of
`RelativeRigidityCapstone.hrig_phiMero_of_repelling`: the E–vS rigidity input
`TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` is produced from `φ_{c₂}` transcendence (`hG`) and, per cleared
bivariate relation, the **index-route relative datum** — a period `p ≥ 1` with `f_{c₁}^[p] - X` separable, a
finite set `B` of repelling fixed points of `f_{c₁}`, the relative branch datum (basin Böttcher branch + the
simple-root + functional-equation data) at every period-`p` cycle point off `B`, and the small exceptional
mass. `noRelation_phiMero_of_no_function_relation` strips the meroField wrapping; `false_of_relative_bulk_branches`
(the index-formula obstruction) closes each relation; `transcendentalOverAdjoin_of_noRelation` repackages to
the hRigid input. This is the index route carried end-to-end on the *relative* side — `hno` reduced to the
basin-branch datum on the cycle + the repelling fixed-point geometry, with no ergodic input. -/
theorem hrig_phiMero_via_index {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (p : ℕ) (B : Finset ℂ), 1 ≤ p ∧ (fixedPointPoly c₁ p).Separable ∧
          (∀ z ∈ B, quadratic c₁ z = z) ∧ (∀ z ∈ B, 1 < ‖2 * z‖) ∧
          (∀ z ∈ (fixedPointPoly c₁ p).roots.toFinset \ B,
            ∃ (w₀ d : ℂ) (β : ℂ → ℂ),
              (∀ i ∈ s, ContDiffAt ℂ ⊤
                (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) z) ∧
              (∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * w₀ ^ i = 0) ∧
              HasDerivAt (fun w => ∑ i ∈ s,
                ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * w ^ i) d w₀ ∧ d ≠ 0 ∧
              (𝓝[(filledJulia c₁)ᶜ] z).NeBot ∧
              Tendsto β (𝓝[(filledJulia c₁)ᶜ] z) (𝓝 w₀) ∧
              (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z, ∑ i ∈ s,
                ((Q i).eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y)) * (β y) ^ i = 0) ∧
              (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z, β ((quadratic c₁)^[p] y) = (β y) ^ (2 ^ p)) ∧
              w₀ ≠ 0 ∧
              (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
                (∀ᶠ y in 𝓝 z, ∑ i ∈ s,
                  ((Q i).eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y)) * (g y) ^ i = 0) →
                deriv g z ≠ 0)) ∧
          ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
            < (((fixedPointPoly c₁ p).roots.toFinset \ B).card : ℝ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply transcendentalOverAdjoin_of_noRelation
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨p, B, hp, hsep, hBfix, hBrep, hbulk, hsmall⟩ := hinput Q s hnt hEqOn
  exact false_of_relative_bulk_branches hp hsep
    (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) s B hBfix hBrep hbulk hsmall

/-- **The hRigid connected-case rigidity input via the index route, with smallness chosen internally.**
This variant removes the explicit exceptional-mass inequality from `hrig_phiMero_via_index`.  For each
cleared relative relation, the caller supplies one finite exceptional set of repelling fixed points and
eventual separability/bulk branch data.  Lean intersects that eventual data with
`eventually_exceptional_mass_small_roots`, chooses a large period, and closes with
`false_of_relative_bulk_branches`. -/
theorem hrig_phiMero_via_index_eventual {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ B : Finset ℂ,
          (∀ z ∈ B, quadratic c₁ z = z) ∧
          (∀ z ∈ B, 1 < ‖2 * z‖) ∧
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c₁ p).Separable ∧
            B ⊆ (fixedPointPoly c₁ p).roots.toFinset ∧
            (∀ z ∈ (fixedPointPoly c₁ p).roots.toFinset \ B,
              ∃ (w₀ d : ℂ) (β : ℂ → ℂ),
                (∀ i ∈ s, ContDiffAt ℂ ⊤
                  (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) z) ∧
                (∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * w₀ ^ i = 0) ∧
                HasDerivAt (fun w => ∑ i ∈ s,
                  ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * w ^ i) d w₀ ∧
                d ≠ 0 ∧
                (𝓝[(filledJulia c₁)ᶜ] z).NeBot ∧
                Tendsto β (𝓝[(filledJulia c₁)ᶜ] z) (𝓝 w₀) ∧
                (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z, ∑ i ∈ s,
                  ((Q i).eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y)) * (β y) ^ i = 0) ∧
                (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z,
                  β ((quadratic c₁)^[p] y) = (β y) ^ (2 ^ p)) ∧
                w₀ ≠ 0 ∧
                (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
                  (∀ᶠ y in 𝓝 z, ∑ i ∈ s,
                    ((Q i).eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y)) * (g y) ^ i = 0) →
                  deriv g z ≠ 0)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply transcendentalOverAdjoin_of_noRelation
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨B, hBfix, hBrep, heventual⟩ := hinput Q s hnt hEqOn
  obtain ⟨p, hpdata, hsmallRoot⟩ :=
    (heventual.and (eventually_exceptional_mass_small_roots c₁ B hBrep)).exists
  rcases hpdata with ⟨hp, hsep, hBsub, hbulk⟩
  exact false_of_relative_bulk_branches hp hsep
    (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) s B hBfix hBrep
    hbulk (hsmallRoot hp hsep hBsub)

/-- **The hRigid connected-case rigidity input via the index route, with fixed exceptional roots
derived.**  This strengthens `hrig_phiMero_via_index_eventual`: the caller supplies a fixed finite
exceptional set of repelling fixed points and eventual bulk branch data, while Lean derives
`B ⊆ roots (f_c^[p] - X)` from fixedness and `1 ≤ p` and chooses the exceptional-mass smallness period
internally. -/
theorem hrig_phiMero_via_index_eventual_fixedB {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ B : Finset ℂ,
          (∀ z ∈ B, quadratic c₁ z = z) ∧
          (∀ z ∈ B, 1 < ‖2 * z‖) ∧
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c₁ p).Separable ∧
            (∀ z ∈ (fixedPointPoly c₁ p).roots.toFinset \ B,
              ∃ (w₀ d : ℂ) (β : ℂ → ℂ),
                (∀ i ∈ s, ContDiffAt ℂ ⊤
                  (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) z) ∧
                (∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * w₀ ^ i = 0) ∧
                HasDerivAt (fun w => ∑ i ∈ s,
                  ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * w ^ i) d w₀ ∧
                d ≠ 0 ∧
                (𝓝[(filledJulia c₁)ᶜ] z).NeBot ∧
                Tendsto β (𝓝[(filledJulia c₁)ᶜ] z) (𝓝 w₀) ∧
                (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z, ∑ i ∈ s,
                  ((Q i).eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y)) * (β y) ^ i = 0) ∧
                (∀ᶠ y in 𝓝[(filledJulia c₁)ᶜ] z,
                  β ((quadratic c₁)^[p] y) = (β y) ^ (2 ^ p)) ∧
                w₀ ≠ 0 ∧
                (∀ g : ℂ → ℂ, AnalyticAt ℂ g z → g z = w₀ →
                  (∀ᶠ y in 𝓝 z, ∑ i ∈ s,
                    ((Q i).eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y)) * (g y) ^ i = 0) →
                  deriv g z ≠ 0)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply transcendentalOverAdjoin_of_noRelation
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨B, hBfix, hBrep, heventual⟩ := hinput Q s hnt hEqOn
  obtain ⟨p, hpdata, hsmallRoot⟩ :=
    (heventual.and (eventually_exceptional_mass_small_roots c₁ B hBrep)).exists
  rcases hpdata with ⟨hp, hsep, hbulk⟩
  have hBsub : B ⊆ (fixedPointPoly c₁ p).roots.toFinset := by
    intro z hz
    exact fixed_mem_fixedPointPoly_roots hp (hBfix z hz)
  exact false_of_relative_bulk_branches hp hsep
    (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) s B hBfix hBrep
    hbulk (hsmallRoot hp hsep hBsub)

end Bottcher
