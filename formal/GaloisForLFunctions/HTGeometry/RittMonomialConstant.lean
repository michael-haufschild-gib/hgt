import GaloisForLFunctions.HTGeometry.RittLogDerivativeEigen
import GaloisForLFunctions.HTGeometry.RittLevelTwoClassification

/-!
# The monomial coefficient is a derivation constant

The monomial branch of the level classifications produces `V = κ·τ^{e₀}·(dτ)^{e₁}` with `κ` only
known to be fixed by the base map.  That is not the whole story: a shift-fixed base element whose
derivative does not vanish has a logarithmic derivative that is an eigenvector of the base map with
eigenvalue `ρ^{−1}`, an exponent pair which is never trivial.  So either the classification's
coefficient is a constant of the derivation, or Ritt's order-one form already follows.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The classification at jet order two, with a constant monomial coefficient.** -/
theorem level_two_classification_const (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c α β₀ g : K} (hc : c ≠ 0) {i k : ℤ} (hcik : c = q ^ i * Fr.ρ ^ k)
    (hrel : Fr.σ V = algebraMap K L c * V
      + (algebraMap K L α * Fr.d τ + (algebraMap K L β₀ * τ + algebraMap K L g))) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (¬(α = 0 ∧ β₀ = 0 ∧ g = 0) ∧
      ∃ (u c' h : K), u ≠ 0 ∧ c' ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ u = c' * u + h) ∨
    (∃ (κ : K) (e₀ e₁ : ℤ), κ ≠ 0 ∧ Fr.ψ κ = κ ∧ Fr.dK κ = 0 ∧
      α = 0 ∧ β₀ = 0 ∧ g = 0 ∧
      V = algebraMap K L κ * τ ^ e₀ * (Fr.d τ) ^ e₁ ∧ i = e₀ + e₁ ∧ k = -e₁) := by
  rcases level_two_classification Fr hqconst hshift hq htr0 htr1 hV0 hV hc hcik hrel with
      hritt | haff | ⟨κ, e₀, e₁, hκ0, hψκ, hα, hβ, hg, hform, hi, hk⟩
  · exact Or.inl hritt
  · exact Or.inr (Or.inl haff)
  · rcases psi_fixed_dichotomy Fr (q := q) hκ0 hψκ with hd | hritt
    · exact Or.inr (Or.inr ⟨κ, e₀, e₁, hκ0, hψκ, hd, hα, hβ, hg, hform, hi, hk⟩)
    · exact Or.inl hritt

end GaloisForLFunctions.HTGeometry
