import GaloisForLFunctions.HTGeometry.NormalizedFamilyRatios
import GaloisForLFunctions.HTGeometry.RecurrenceCollapseAlmostPeriodic

/-!
# The recurrence collapse from normalized coefficient data

The projective boundary supplies exactly what the Bohr-return collapse consumes: coefficients
presented by a shape and a limit give a normalizing member that is eventually nonzero and a family
of ratio limits.  Feeding those in, a finite differential relation collapses along the return times
to an autonomous relation whose coefficient vector is explicit — the quotients of the residues,
normalized to `1` at the dominant member.

Together with the residue chain this is eq. (27) → (29) with no hypothesis on the coefficient data
beyond its presentation.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **The collapse from residues.**  A finite relation whose coefficients converge after division by
their shapes, with the shape ratios convergent and the normalizing residue nonzero, collapses to the
autonomous relation with coefficient vector the quotient of residues. -/
theorem recurrence_collapse_of_normalized {n : ℕ} {σ : ℝ} (F M : Fin n → ℂ → ℂ)
    (shape : Fin n → ℝ → ℂ) (c r : Fin n → ℂ) (β : Fin n) (hcβ : c β ≠ 0)
    (hs : ∀ α, ∀ᶠ t : ℝ in atTop, shape α t ≠ 0)
    (hF : ∀ α, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I) / shape α t) atTop (nhds (c α)))
    (hr : ∀ α, Tendsto (fun t : ℝ => shape α t / shape β t) atTop (nhds (r α)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * M α s = 0)
    (hMcont : ∀ α, Continuous fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hMap : ∀ α, IsBohrAlmostPeriodic fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    (∑ α, (c α * r α / c β) * M α (σ : ℂ) = 0) ∧ (c β * r β / c β) = 1 := by
  obtain ⟨hFβ, -, hcoeff⟩ := tendsto_family_ratio_of_normalized
    (F := fun α t => F α ((σ : ℂ) + (t : ℂ) * Complex.I)) (shape := shape) (c := c) (r := r)
    β hcβ hs hF hr
  exact recurrence_collapse_of_bohr_return F M β ((σ : ℂ)) (fun α => c α * r α / c β)
    hrel hMcont hMap hFβ hcoeff

end GaloisForLFunctions
