/-
# The deck σ-step with a general carried coordinate (mixed-pair wiring, step 1)

`DeckAnnulus.monoF_step_from_inverse` carries the second Böttcher coordinate along the dyadic
cover through its FAR-FIELD form `bottcherCoord c₂ ∘ ψ₁`, forcing the containment
`ψ₁(ξ^{2ⁿ}) ∈ escapeOpen c₂` — the clause the level-compatibility hypothesis of the
both-disconnected capstone exists to guarantee.  For MIXED pairs the carried coordinate is the
**connected** parameter, which has a global single-valued basin branch (Gap 2): the tower's deep
points need only avoid `K₁`, not reach the far field.  This file generalizes the σ-step to an
arbitrary analytic carried function `h` on an arbitrary carrier `Ω` — the deck-invariance of the
carried germ is automatic (it enters through the deck-invariant `ξ^{2ⁿ}` only), so the proof is
verbatim.  Instantiating `h := β₁` (global branch), `Ω := (filledJulia c₁)ᶜ` turns the
level-compatibility clause into plain `K₁`-avoidance of the tower — free for `‖c₂‖` large by the
two-cell geometry of `CantorFilledJulia`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.DeckAnnulus

open Complex Filter Set

namespace Bottcher

/-- **The carried germ, general form.**  Any function `h` analytic on a carrier `Ω` hit by the
tower base points `ψ₁(ξ^{2ⁿ})` defines an element of the cover's analytic subring. -/
theorem exists_rotInvariant_carried {h : ℂ → ℂ} {Ω : Set ℂ}
    (hhan : AnalyticOnNhd ℂ h Ω)
    {U : Set ℂ} {ψ₁ : ℂ → ℂ} {n : ℕ}
    (hψan : ∀ ξ ∈ U, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ U, ψ₁ (ξ ^ (2 ^ n)) ∈ Ω) :
    ∃ a₂ : analyticSubring U,
      (a₂ : Germ (𝓟 U) ℂ) = ↑(fun ξ => h (ψ₁ (ξ ^ (2 ^ n)))) := by
  set pw : ℂ → ℂ := fun ξ => ξ ^ (2 ^ n) with hpw
  set F : ℂ → ℂ := fun ξ => h (ψ₁ (pw ξ)) with hF
  have han : AnalyticOnNhd ℂ F U := by
    intro ξ hξ
    have h1 : AnalyticAt ℂ pw ξ := analyticAt_id.pow (2 ^ n)
    have h2 : AnalyticAt ℂ ψ₁ (pw ξ) := hψan ξ hξ
    have h3 : AnalyticAt ℂ h (ψ₁ (pw ξ)) := hhan _ (hcont ξ hξ)
    have h32 : AnalyticAt ℂ (fun w => h (ψ₁ w)) (pw ξ) := h3.comp h2
    exact h32.comp h1
  exact ⟨⟨(↑F : Germ (𝓟 U) ℂ), F, han, rfl⟩, rfl⟩

/-- **Per-depth σ-step with a general carried coordinate.**  Verbatim
`monoF_step_from_inverse` with the carried far-field composite `bottcherCoord c₂ ∘ ψ₁` replaced
by `h ∘ ψ₁` for any `h` analytic on a carrier the tower base points hit: a `K`-algebra
automorphism `σ` of `meroField U` scaling the tower germ `a₁` by a dyadic root of order `> d`
while fixing the carried germ `a₂(ξ) = h(ψ₁(ξ^{2ⁿ}))` — the fixing is automatic since the carried
germ factors through the deck-invariant `ξ^{2ⁿ}`. -/
theorem monoF_step_from_inverse_carried {h : ℂ → ℂ} {Ω : Set ℂ}
    (hhan : AnalyticOnNhd ℂ h Ω)
    {U : Set ℂ} {ψ₁ : ℂ → ℂ} {ζ₀ : ℂ} {n : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (hrot : Set.MapsTo (rotation ζ₀) U U) (hrot' : Set.MapsTo (rotation ζ₀⁻¹) U U)
    (hζ0 : ζ₀ ≠ 0) (hζpow : ζ₀ ^ (2 ^ n) = 1) (d : ℕ) (hord : d < orderOf ζ₀)
    (hψan : ∀ ξ ∈ U, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ U, ψ₁ (ξ ^ (2 ^ n)) ∈ Ω)
    (a₁ : analyticSubring U) (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(id : ℂ → ℂ))
    (hK : ∀ k : K, precompMeroEquiv
        (analyticOnNhd_deckRot (liftUniformization_id U) hrot)
        (analyticOnNhd_deckRot (liftUniformization_id U) hrot')
        (mapsTo_deckRot (liftUniformization_id U) hrot)
        (mapsTo_deckRot (liftUniformization_id U) hrot')
        (eqOn_deckRot_comp hζ0 (liftUniformization_id U) hrot')
        (eqOn_deckRot_comp' hζ0 (liftUniformization_id U) hrot)
        hUo hUc hUne (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    ∃ (a₂ : analyticSubring U) (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U) (m : ℕ),
      (a₂ : Germ (𝓟 U) ℂ) = ↑(fun ξ => h (ψ₁ (ξ ^ (2 ^ n)))) ∧
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₂)
        = algebraMap (analyticSubring U) (meroField U) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₁)
        = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_carried hhan hψan hcont
  have hbfix : ∀ y ∈ U, (fun ξ => h (ψ₁ (ξ ^ (2 ^ n)))) (rotation ζ₀ y)
      = (fun ξ => h (ψ₁ (ξ ^ (2 ^ n)))) y :=
    pow_comp_rotation_invariant (h := fun w => h (ψ₁ w)) hζpow U
  obtain ⟨σ, ζ, m, hm, hord', hfix, hζfix, hscale⟩ :=
    monoF_step_trivial (b₂ := fun ξ => h (ψ₁ (ξ ^ (2 ^ n))))
      hUo hUc hUne hrot hrot' hζ0 d hord hbfix a₁ a₂ ha₁ ha₂ hK
  exact ⟨a₂, σ, ζ, m, ha₂, hm, hord', hfix, hζfix, hscale⟩

end Bottcher
