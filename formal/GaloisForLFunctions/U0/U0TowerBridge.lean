/-
# The U0 tower bridge: `u₀ ⟂ φ_b` from the Böttcher section tower

Instantiates the two-coordinate tower consumption theorem
`Bottcher.q62_disconnected_of_towerData` at the U0 carrier pair
`(a₁, a₂) = (phiAnalytic b, u0AnSub)`: the `φ_b ≠ 0` and `u₀`-transcendence inputs are proven
in-tree (`phiMero_ne_zero`, `u0Mero_transcendental`), so the all-parameters U0 card conclusion
`NoRelation ℂ(z) φ_b u₀` follows from the same deep-tower data (radicand + odd loop + `u₀`-germ
clause) that the q62 section tower produces — the single shared certificate of both programs.
-/
import GaloisForLFunctions.Bottcher.ExtendedNonSquare
import GaloisForLFunctions.U0.U0MeroCarrier

open Bottcher U0NaturalBoundary U0MeroCarrier

namespace U0TowerBridge

/-- **`u₀ ⟂ φ_b` from tower data.**  The all-parameters U0 independence conclusion, consuming
exactly the deep-tower certificate (per relation degree: an extension domain, the `2^k`-radicand
with its odd loop, and the `u₀`-germ compatibility clause). -/
theorem u0_phi_independence_of_towerData {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (towerdata : ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt GBExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (Filter.principal Ext) F) = (aExt : Filter.Germ (Filter.principal Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = (phiAnalytic b hU_esc) ^ (2 ^ k) ∧
        restrictAnalytic hUExt GBExt = u0AnSub hU_ext ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact Bottcher.q62_disconnected_of_towerData hUo hUc hUne hUinf
    (phiAnalytic b hU_esc) (u0AnSub hU_ext)
    (phiMero_ne_zero hUo hUc hUne hU_esc)
    (u0Mero_transcendental hUo hUc hUne hUinf hU_ext)
    towerdata

end U0TowerBridge
