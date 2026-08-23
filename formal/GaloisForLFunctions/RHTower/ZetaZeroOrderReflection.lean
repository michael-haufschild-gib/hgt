import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.Reflection

/-!
# The order of a zeta zero is symmetric under `ρ ↦ 1 - ρ`

In the open critical strip the archimedean factor is a unit, so `ζ` and the completed `ξ` have the
same analytic order (`xi_analyticOrderAt_eq_riemannZeta_of_mem_strip`); and the orders of `ξ` at
`ρ` and `1 - ρ` agree (`xi_orderAt_one_sub`).

## Main results

* `analyticOrderAt_riemannZeta_one_sub`
-/

namespace RHTower

open Complex Filter Topology

noncomputable section

/-- **The order of `ζ` at a strip zero is symmetric under the functional equation.** -/
theorem analyticOrderAt_riemannZeta_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannZeta (1 - ρ) = analyticOrderAt riemannZeta ρ := by
  have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by
    rw [Complex.sub_re]
    simp
  have hstrip' : 0 < ((1 : ℂ) - ρ).re ∧ ((1 : ℂ) - ρ).re < 1 := by
    rw [hre]
    constructor <;> linarith
  have hxi1 : analyticOrderAt xi ((1 : ℂ) - ρ) = analyticOrderAt riemannZeta ((1 : ℂ) - ρ) :=
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip'
  have hxi2 : analyticOrderAt xi ρ = analyticOrderAt riemannZeta ρ :=
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩
  rw [← hxi1, ← hxi2]
  exact xi_orderAt_one_sub ρ

end

end RHTower
