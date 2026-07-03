/-
# The direct (non-reflection) one-sided smooth-piece discharge

Tracing the concrete smooth-piece configuration shows the `SmoothPieceRigidity` discharge does **not**
need Schwarz reflection.  A branch `wfam k` of the fibre polynomial is analytic on `ball z₁ ρ ∩ K₂ᶜ`,
and the frontier piece `S ⊆ K₂ᶜ`, so at a piece point `z₀` the branch is analytic *across* the Julia
frontier — a full 2-D neighbourhood.  In the **one-sided** case (the `{‖wfam k‖<1}` side is interior
`K₁`, so the local basin is exactly the `{‖wfam k‖>1}` side, where `β = wfam k`), the branch is
already the analytic continuation of `β`, giving `ContinuesAcross β z₀` directly and contradicting the
natural boundary `hnb`.  The **two-sided** case (basin on both sides = a smooth two-sided Julia arc) is
precisely `c ∈ {0,−2}`, excluded by the even-FE dichotomy `c_mem_of_even_holo_ball`.

This file records the direct one-sided core.  The reflection stack (`SchwarzReflection*.lean`) is not
used here.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.InteriorNonemptyHnb

open Filter Topology

namespace Bottcher

/-- **Direct one-sided discharge core.**  If a branch `g` is analytic at a frontier point `z₀` (i.e.
analytic *across* the Julia frontier there) and coincides with the Böttcher branch `β` on the local
basin `𝓝[K₁ᶜ] z₀`, then `g` witnesses `ContinuesAcross β z₀`, contradicting the natural boundary
`hnb`.  No reflection: the branch is already the analytic continuation of `β` in the one-sided case. -/
theorem false_of_branch_matching_at_frontier {c₁ : ℂ} {β g : ℂ → ℂ} {z₀ : ℂ}
    (hz₀ : z₀ ∈ frontier (filledJulia c₁))
    (hnb : ∀ w ∈ frontier (filledJulia c₁),
        ¬ U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ w)
    (hgAt : AnalyticAt ℂ g z₀)
    (hgβ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, g z = β z) :
    False :=
  hnb z₀ hz₀ ⟨g, hgAt, hgβ⟩

end Bottcher
