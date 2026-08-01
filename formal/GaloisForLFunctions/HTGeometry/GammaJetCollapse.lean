import GaloisForLFunctions.HTGeometry.GammaJetRatioFamily

/-!
# The collapse for Gamma-jet coefficient data

Putting the layers together: a finite family of Gamma-field coefficients, each presented by its
Gamma-jet datum and its residue, has a dominant member, hence a full family of shape-ratio limits,
hence — through the Bohr-return collapse — an autonomous relation with an explicit coefficient
vector, normalized to `1` at the dominant member.

No dominance hypothesis is chosen by hand: the datum order produces it.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {σ : ℝ}

/-- **The collapse from Gamma-jet data.**  A finite relation whose coefficients converge after
division by their Gamma-jet shapes, with nonzero residues, collapses along the Bohr return times to
an autonomous relation whose coefficient vector is explicit and equals `1` at the dominant datum. -/
theorem exists_collapse_of_gammaJet_data (hσ : 0 < σ) {N : ℕ} (hN : 0 < N)
    (F M : Fin N → ℂ → ℂ) (u a dP b : Fin N → ℕ) (c : Fin N → ℂ) (hc : ∀ α, c α ≠ 0)
    (hF : ∀ α, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaJetShape σ (u α) (a α) (dP α) (b α) t) atTop (nhds (c α)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * M α s = 0)
    (hMcont : ∀ α, Continuous fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hMap : ∀ α, IsBohrAlmostPeriodic fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    ∃ (β : Fin N) (d : Fin N → ℂ), (∑ α, d α * M α (σ : ℂ) = 0) ∧ d β = 1 := by
  obtain ⟨β, r, hr, hrβ⟩ := exists_dominant_with_shape_ratios hσ hN u a dP b
  refine ⟨β, fun α => c α * r α / c β, ?_⟩
  exact recurrence_collapse_of_normalized F M
    (fun α => gammaJetShape σ (u α) (a α) (dP α) (b α)) c r β (hc β)
    (fun α => eventually_gammaJetShape_ne_zero hσ (u α) (a α) (dP α) (b α)) hF hr
    hrel hMcont hMap

end GaloisForLFunctions
