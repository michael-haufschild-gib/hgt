import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitLimitValue
import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitCauchy

/-!
# The orbit limit is within `O(1/‖s‖)` of the base point

The Cauchy estimate holds for every number of steps, so it passes to the limit.  This is the
quantitative form the vertical-decay hypothesis of `eq_zero_of_periodic_of_vertical_decay` is read
off from: combined with the tube limit for the monomial itself it makes `C − 1` small at large
height.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The orbit limit is within `O(1/‖s‖)` of the base point.** -/
theorem norm_gammaMonomialOrbitLimit_sub_le {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ A Rb : ℝ, 0 ≤ A ∧ 1 ≤ Rb ∧ ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re → Rb ≤ ‖s‖ →
      ‖gammaMonomialOrbitLimit lam g s - gammaMonomial lam g s‖
        ≤ A * ‖gammaMonomial lam g s‖ / ‖s‖ := by
  obtain ⟨A, Rb₀, hA0, hRb₀, hA⟩ := exists_norm_gammaMonomial_orbit_sub_le lam g hdeg hmom
  obtain ⟨Rb₁, hRb₁, htend⟩ := tendsto_gammaMonomial_orbit lam g hdeg hmom
  refine ⟨A, max Rb₀ Rb₁, hA0, le_trans hRb₀ (le_max_left _ _), fun s hs hsn => ?_⟩
  have hs0 : Rb₀ ≤ ‖s‖ := le_trans (le_max_left _ _) hsn
  have hs1 : Rb₁ ≤ ‖s‖ := le_trans (le_max_right _ _) hsn
  have hlim : Tendsto
      (fun n : ℕ => ‖gammaMonomial lam g (s + (n : ℂ)) - gammaMonomial lam g s‖) atTop
      (nhds ‖gammaMonomialOrbitLimit lam g s - gammaMonomial lam g s‖) :=
    ((htend s hs hs1).sub_const _).norm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall fun n => hA s hs hs0 n)

end

end GaloisForLFunctions.HTGeometry
