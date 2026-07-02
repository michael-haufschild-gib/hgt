/-
# Continuing the relative coefficients off the far field (A4)

The relative fibre coefficients are `aᵢ(z) = Qᵢ(z, φ_{c₂}(z))`, but `φ_{c₂} = bottcherCoord c₂` is a
priori defined only on the far field `escapeOpen c₂`.  The dendrite tip `z₀ ∈ J_{c₁} ∖ K_{c₂}`
(supplied by `JuliaSwapDichotomy`) lies in the *basin* `(filledJulia c₂)ᶜ` but generally outside the
far field, so the coefficients must be continued there before the branch machinery can read their
germ at `z₀`.

For a **connected** second parameter (`c₂ ∈ mandelbrot`) the Gap-2 global branch
`exists_global_branch_of_mem_mandelbrot` continues `φ_{c₂}` to an analytic `β₂` on the whole basin
`(filledJulia c₂)ᶜ`, agreeing with `bottcherCoord c₂` on the far field.  Substituting `β₂` for
`φ_{c₂}` in the coefficients then gives, on the entire basin, an **analytic** (hence `ContDiffAt ℂ ⊤`)
family that **agrees** with the original far-field coefficients on `escapeOpen c₂` — exactly the
coefficient data `noRelation_phiMero_of_basin_branch`'s `hinput` reads at the tip.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.RelativeFibreGeneric
import GaloisForLFunctions.Bottcher.RhoPathLift

open Polynomial Set

namespace Bottcher

/-- **A4: continued relative coefficients on the basin of a connected `c₂`.** For `c₂ ∈ mandelbrot`
there is a branch `β₂`, analytic on the whole basin `(filledJulia c₂)ᶜ` and equal to
`bottcherCoord c₂` on the far field, such that for every bivariate coefficient polynomial `q` the
substituted coefficient `z ↦ q(z, β₂ z)` is analytic on the basin (so `ContDiffAt ℂ ⊤` at every basin
point) and agrees with the far-field coefficient `z ↦ q(z, φ_{c₂}(z))` on `escapeOpen c₂`. -/
theorem exists_continued_coefficients_of_mem_mandelbrot (c₂ : ℂ) (hc₂M : c₂ ∈ mandelbrot) :
    ∃ β₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ ∧
      (∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z) ∧
      (∀ q : Polynomial (Polynomial ℂ),
        AnalyticOnNhd ℂ (fun z => q.eval₂ (Polynomial.evalRingHom z) (β₂ z)) (filledJulia c₂)ᶜ) ∧
      (∀ (q : Polynomial (Polynomial ℂ)) (z₀ : ℂ), z₀ ∈ (filledJulia c₂)ᶜ →
        ContDiffAt ℂ ⊤ (fun z => q.eval₂ (Polynomial.evalRingHom z) (β₂ z)) z₀) ∧
      (∀ (q : Polynomial (Polynomial ℂ)) (z : ℂ), z ∈ escapeOpen c₂ →
        q.eval₂ (Polynomial.evalRingHom z) (β₂ z)
          = q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) := by
  obtain ⟨β₂, hβan, hβesc⟩ := exists_global_branch_of_mem_mandelbrot c₂ hc₂M
  refine ⟨β₂, hβan, hβesc, ?_, ?_, ?_⟩
  · intro q
    exact analyticOnNhd_eval₂_of_analyticOnNhd hβan q
  · intro q z₀ hz₀
    exact ((analyticOnNhd_eval₂_of_analyticOnNhd hβan q) z₀ hz₀).contDiffAt
  · intro q z hz
    rw [hβesc z hz]

end Bottcher
