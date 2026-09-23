/-
Tier (T2) closure at the general level (doc 53 §5): the pair peel.

Double application of the banked `exists_peel`: a carrier analytic on an
open U with exactly two simple zeros ρ₁ ≠ ρ₂ (and no others) factors
GLOBALLY as f = (s−ρ₁)(s−ρ₂)·h with h analytic and zero-free on ALL of U —
the order-preservation clause of the first peel carries the second zero to
the cofactor, and zero-freeness follows from the no-other-zeros hypothesis
plus order preservation. For the FE-real conjugate pair ±iη in the v-frame
this is the factored form Z = (v² + η²)·h consumed by
`pair_depth_eq_center_over_cofactor` and `depth_update_exact`: the exact
depth reading η² = Z(0)/h(0).

With this, tier (T2)'s general machinery is complete; what remains is
per-instance (the Rouché count "exactly two zeros in the disc" — doc 48 §2's
checkable hypothesis) and the analytic supply of the carrier data.
-/
import GaloisForLFunctions.HTGeometry.Peeling
import GaloisForLFunctions.RHTower.DepthUpdate

namespace RHTower

/-- **The pair peel**: two simple zeros and no others on an open U give the
global factored form with a zero-free analytic cofactor. -/
theorem pair_peel {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) {ρ₁ ρ₂ : ℂ} (h1 : ρ₁ ∈ U) (h2 : ρ₂ ∈ U)
    (hne : ρ₁ ≠ ρ₂)
    (ho1 : analyticOrderAt f ρ₁ = 1) (ho2 : analyticOrderAt f ρ₂ = 1)
    (hnz : ∀ σ ∈ U, σ ≠ ρ₁ → σ ≠ ρ₂ → f σ ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ σ ∈ U, h σ ≠ 0) ∧
      ∀ s ∈ U, f s = (s - ρ₁) * (s - ρ₂) * h s := by
  obtain ⟨g, hgan, hgρ, hgfac, hgord⟩ :=
    exists_peel hU hf h1 (m := 1) (by exact_mod_cast ho1)
  have hgo2 : analyticOrderAt g ρ₂ = 1 := by
    rw [hgord ρ₂ h2 hne.symm]
    exact ho2
  obtain ⟨h, hhan, hhρ, hhfac, hhord⟩ :=
    exists_peel hU hgan h2 (m := 1) (by exact_mod_cast hgo2)
  refine ⟨h, hhan, ?_, ?_⟩
  · intro σ hσ
    by_cases hσ2 : σ = ρ₂
    · subst hσ2
      exact hhρ
    by_cases hσ1 : σ = ρ₁
    · subst hσ1
      have hgo0 : analyticOrderAt g σ = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hgρ)
      have hho0 : analyticOrderAt h σ = 0 := by
        rw [hhord σ hσ hσ2]
        exact hgo0
      rcases analyticOrderAt_eq_zero.mp hho0 with hna | hval
      · exact absurd (hhan σ hσ) hna
      · exact hval
    · have hfo0 : analyticOrderAt f σ = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (hnz σ hσ hσ1 hσ2))
      have hgo0 : analyticOrderAt g σ = 0 := by
        rw [hgord σ hσ hσ1]
        exact hfo0
      have hho0 : analyticOrderAt h σ = 0 := by
        rw [hhord σ hσ hσ2]
        exact hgo0
      rcases analyticOrderAt_eq_zero.mp hho0 with hna | hval
      · exact absurd (hhan σ hσ) hna
      · exact hval
  · intro s hs
    have hf1 := hgfac s hs
    have hg1 := hhfac s hs
    rw [pow_one] at hf1 hg1
    rw [hf1, hg1]
    ring

/-- **The v-frame pair peel with exact depth**: the FE-real conjugate pair
±iη factors the carrier as Z = (v² + η²)·h with zero-free analytic h, and
the depth-squared reads off the center: η² = Z(0)/h(0). -/
theorem pair_peel_depth {Z : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hZ : AnalyticOnNhd ℂ Z U) {η : ℝ} (hη : 0 < η)
    (h1 : Complex.I * (η : ℂ) ∈ U) (h2 : -(Complex.I * (η : ℂ)) ∈ U)
    (ho1 : analyticOrderAt Z (Complex.I * (η : ℂ)) = 1)
    (ho2 : analyticOrderAt Z (-(Complex.I * (η : ℂ))) = 1)
    (hnz : ∀ σ ∈ U, σ ≠ Complex.I * (η : ℂ) → σ ≠ -(Complex.I * (η : ℂ)) →
      Z σ ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ σ ∈ U, h σ ≠ 0) ∧
      (∀ v ∈ U, Z v = (v ^ (2 : ℕ) + ((η : ℂ)) ^ (2 : ℕ)) * h v) ∧
      (0 ∈ U → ((η : ℂ)) ^ (2 : ℕ) = Z 0 / h 0) := by
  have hne : Complex.I * (η : ℂ) ≠ -(Complex.I * (η : ℂ)) := by
    intro hc
    have hη0 : ((η : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hη.ne'
    have hz : Complex.I * (η : ℂ) = 0 := by
      linear_combination hc / 2
    rcases mul_eq_zero.mp hz with h | h
    · exact Complex.I_ne_zero h
    · exact hη0 h
  obtain ⟨h, han, hnz', hfac⟩ := pair_peel hU hZ h1 h2 hne ho1 ho2 hnz
  have hquad : ∀ v ∈ U, Z v = (v ^ (2 : ℕ) + ((η : ℂ)) ^ (2 : ℕ)) * h v := by
    intro v hv
    rw [hfac v hv]
    have hexp : (v - Complex.I * (η : ℂ)) * (v - -(Complex.I * (η : ℂ)))
        = v ^ (2 : ℕ) + ((η : ℂ)) ^ (2 : ℕ) := by
      have h1' : (v - Complex.I * (η : ℂ)) * (v - -(Complex.I * (η : ℂ)))
          = v ^ (2 : ℕ) - Complex.I ^ (2 : ℕ) * ((η : ℂ)) ^ (2 : ℕ) := by
        ring
      rw [h1', Complex.I_sq]
      ring
    rw [← hexp]
  refine ⟨h, han, hnz', hquad, fun h0 => ?_⟩
  have hZ0 := hquad 0 h0
  rw [eq_div_iff (hnz' 0 h0)]
  simpa using hZ0.symm

end RHTower
