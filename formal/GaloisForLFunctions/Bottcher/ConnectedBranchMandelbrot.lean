/-
# Connected Böttcher branch for `c ∈ mandelbrot`, with the sheet-swap winding discharged

Every connected-branch endpoint in `ConnectedBranchAssembly` takes two topological inputs: the
anti-period sheet-swap `hanti` and the path-lift `hlift`. The sheet-swap was the deep one — it is the
odd-winding statement `hodd`, now proven in `RhoWindingOne` (`hodd_of_mem_mandelbrot`) and packaged by
`rho_antiperiod_of_odd_shift_winding_all` into exactly `hanti`.

So for `c ∈ mandelbrot` the anti-period hypothesis is no longer an input: the theorems below produce it
internally. The single remaining topological input is the path-lift `hlift` (each loop in
`escapeLevel c (n+1)` lifts through `ρ_{n+1}`), i.e. the covering-space datum.
-/
import GaloisForLFunctions.Bottcher.ConnectedBranchAssembly
import GaloisForLFunctions.Bottcher.RhoWindingOne

open Topology unitInterval
open Pi1CMinusZero

namespace Bottcher

noncomputable section

/-- The anti-period sheet-swap, produced from the now-proven odd winding of the half-period
`ρ`-loop. For `c ∈ mandelbrot` this is a theorem, not a hypothesis. -/
theorem rho_antiperiod_of_mem_mandelbrot {c : ℂ} (hcM : c ∈ mandelbrot) :
    ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t :=
  rho_antiperiod_of_odd_shift_winding_all
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM) (hodd_of_mem_mandelbrot hcM)

/-- **Connected Böttcher branch for `c ∈ mandelbrot` from the path-lift alone.** The anti-period
sheet-swap is discharged internally (`rho_antiperiod_of_mem_mandelbrot`); only the `ρ` path-lift
`hlift` remains. -/
theorem exists_global_branch_of_mem_mandelbrot_of_rho_lifts (c : ℂ) (hcM : c ∈ mandelbrot)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_rho_lifts_antiperiod_of_mem_mandelbrot c hcM
    (rho_antiperiod_of_mem_mandelbrot hcM) hlift

/-- **Connected branch with full modulus/functional-equation data for `c ∈ mandelbrot` from the
path-lift alone.** As above, the sheet-swap is internal. -/
theorem exists_global_branch_modulus_of_mem_mandelbrot_of_rho_lifts (c : ℂ) (hcM : c ∈ mandelbrot)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  exists_global_branch_modulus_of_rho_lifts_antiperiod_of_mem_mandelbrot c hcM
    (rho_antiperiod_of_mem_mandelbrot hcM) hlift

/-- **Unconditional connected Böttcher branch for `c ∈ mandelbrot`.** Both remaining topological
inputs of the connected branch are now theorems: the anti-period sheet-swap
(`rho_antiperiod_of_mem_mandelbrot`) and the covering-map status of the explicit `ρ_n` tower
(`rho_isCoveringMap`, obtained from the covering-cancellation lemma). Feeding both into
`exists_global_branch_covering_bijective_of_rho_covering_antiperiod_of_mem_mandelbrot` discharges the
last hypotheses, so the analytic branch `β` on the connected basin `(filledJulia c)ᶜ` — extending the
Böttcher coordinate, with the modulus, functional-equation, covering and bijectivity data — exists with
no remaining hypothesis beyond `c ∈ mandelbrot`. This closes the connected-branch Gap 2. -/
theorem exists_global_branch_covering_bijective_of_mem_mandelbrot (c : ℂ) (hcM : c ∈ mandelbrot) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ∧
        Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  exists_global_branch_covering_bijective_of_rho_covering_antiperiod_of_mem_mandelbrot c hcM
    (rho_antiperiod_of_mem_mandelbrot hcM)
    (rho_isCoveringMap c (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM)
      (rho_antiperiod_of_mem_mandelbrot hcM))

end

end Bottcher
