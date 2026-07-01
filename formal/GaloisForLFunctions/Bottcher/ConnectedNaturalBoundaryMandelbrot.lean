import GaloisForLFunctions.Bottcher.ConnectedBranchMandelbrot
import GaloisForLFunctions.Bottcher.DendriteContinuesAcross

open Set Topology U0NaturalBoundary

namespace Bottcher

/-- **Natural boundary of the actual Böttcher coordinate, for empty-interior `c ∈ mandelbrot`.**
Combines the now-unconditional connected branch `β`
(`exists_global_branch_covering_bijective_of_mem_mandelbrot`, closing Gap 2) with the dendrite
modulus obstruction (`hnb_of_emptyInterior_modulus`): the branch `β` carries the Böttcher modulus
`‖β z‖ = exp(G_c z)`, and when the filled Julia set has empty interior every basin branch carrying
that modulus fails to continue across any frontier point. So the natural-boundary hypothesis `hnb`
consumed by the connected `q62` transcendence endpoints is, for this sub-case, no longer a hypothesis
but a theorem — the "wire the natural boundary to the real coordinate via `β`" step of Gap 3, for the
empty-interior (dendrite) connected parameters. The remaining connected input is the branch boundary
limit at the simple-root Julia point (the ray-landing datum), isolated in `phiMero_transcendental_of_dendrite_input`. -/
theorem exists_global_branch_naturalBoundary_of_emptyInterior_of_mem_mandelbrot
    (c : ℂ) (hcM : c ∈ mandelbrot) (hempty : interior (filledJulia c) = ∅) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z₀ ∈ frontier (filledJulia c),
        ¬ ContinuesAcross β (filledJulia c)ᶜ z₀) := by
  obtain ⟨β, hβan, hβesc, _hβne, hβmod, _hrest⟩ :=
    exists_global_branch_covering_bijective_of_mem_mandelbrot c hcM
  exact ⟨β, hβan, hβesc, hβmod, hnb_of_emptyInterior_modulus hempty hβmod⟩

end Bottcher
