import GaloisForLFunctions.HTGeometry.GammaJetCollapse

/-!
# Gamma-field elements converge against their own Gamma-jet shape

A Gamma polynomial whose coefficients converge against a common jet shape converges against the
Gamma-jet shape built from that jet shape and the lowest occurring Gamma power.  This is the
hypothesis the collapse from Gamma-jet data consumes, so the whole chain applies to a concrete
element of `ℂ(s)⟨Γ⟩` presented in normal form.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

theorem eventually_polyJetShape_ne_zero (_hσ : 0 < σ) (a dP b : ℕ) :
    ∀ᶠ t : ℝ in atTop, polyJetShape σ a dP b t ≠ 0 := by
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  rw [polyJetShape]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hs)) (pow_ne_zero _ hs)

/-- **A Gamma-field element against its own shape.**  A Gamma polynomial whose coefficients converge
against a common jet shape, and whose coefficients below the lowest index vanish, converges against
the Gamma-jet shape of that index — to the residue of the lowest coefficient. -/
theorem tendsto_gammaField_div_gammaJetShape (hσ : 0 < σ) {d : ℕ} (A : ℕ → ℝ → ℂ) (u : ℕ)
    (hu : u ≤ d) (a dP b : ℕ) (cs : ℕ → ℂ)
    (hconv : ∀ i, Tendsto (fun t : ℝ => A i t / polyJetShape σ a dP b t) atTop (nhds (cs i)))
    (hlow : ∀ i < u, A i = fun _ => 0) :
    Tendsto (fun t : ℝ => (∑ i ∈ Finset.range (d + 1), A i t * gammaLine σ t ^ i)
        / gammaJetShape σ u a dP b t) atTop (nhds (cs u)) := by
  have hmain := tendsto_gammaField_projective hσ A u hu (polyJetShape σ a dP b) cs
    (eventually_polyJetShape_ne_zero hσ a dP b) hconv hlow
  refine hmain.congr (fun t => ?_)
  rw [gammaJetShape]

end GaloisForLFunctions
