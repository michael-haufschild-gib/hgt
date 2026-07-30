/-
# hDisc loop/deck bridge

This file joins the two sides of the disconnected monodromy construction:

* `LiftExists.exists_circle_lift_period_order_gt` gives the actual lifted loop whose
  Böttcher logarithmic period is `2πi/2ⁿ`, with multiplier order above any bound.
* `CylinderDeck.dyadic_verticalStrip_zfixing_deck_data` gives the matching z-fixing
  deck on the log-cover carrier: a self-biholomorphism with inverse, fixing the
  projection and scaling `exp ∘ φ`.

The result is not another abstraction: it is the checked handoff object saying that
the monodromy loop and the z-fixing deck can be requested together at the same
dyadic depth.
-/
import GaloisForLFunctions.Bottcher.CylinderDeck
import GaloisForLFunctions.Bottcher.BottcherTowerData
import GaloisForLFunctions.Bottcher.DeckAnnulusData
import GaloisForLFunctions.Bottcher.LiftExists
import GaloisForLFunctions.Bottcher.ProductCover
import Mathlib.Order.Filter.Germ.Basic

open Complex Filter

namespace Bottcher

/-- **Loop plus z-fixing deck at one dyadic depth.**  For a depth `d`, the lifted circle loop has
period `2πi/2ᵈ` and the vertical-strip log cover has the concrete deck
`ψ ∘ (w ↦ w + 2πi/2ᵈ) ∘ φ`, with inverse, fixing the base projection and scaling `exp ∘ φ` by the
same dyadic multiplier. -/
theorem dyadic_verticalStrip_loop_and_zfixing_deck_data
    (c : ℂ) {U : Set ℂ} {a b : ℝ} {φ ψ π q : ℂ → ℂ}
    (H : LiftUniformization U {w : ℂ | a < w.re ∧ w.re < b} φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (hqFactor : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | a < w.re ∧ w.re < b},
        q y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y)))
    (d : ℕ) :
    ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ) (g z) = ζ₀ * (Complex.exp ∘ φ) z) := by
  obtain ⟨R, γ, γ', hR, hperiod⟩ := exists_circle_lift_period c d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hζ, hπfix, hscale⟩ :=
    dyadic_verticalStrip_zfixing_deck_data H hπfactor hqFactor d
  refine ⟨R, γ, γ', ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g,
    hord, hR, hperiod, ?_, hπfix, hscale⟩
  exact hζ

/-- **Unbounded loop plus z-fixing deck tower.**  For every degree bound `d`, choose the same
dyadic depth `d`: the lifted monodromy loop has period `2πi/2ᵈ`, and the log-cover deck fixes the
projection while scaling the lift by the associated multiplier of order `> d`. -/
theorem dyadic_verticalStrip_loop_and_zfixing_deck_tower
    (c : ℂ) {U : Set ℂ} {a b : ℝ} {φ ψ π q : ℂ → ℂ}
    (H : LiftUniformization U {w : ℂ | a < w.re ∧ w.re < b} φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (hqFactor : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | a < w.re ∧ w.re < b},
        q y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    ∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ) (g z) = ζ₀ * (Complex.exp ∘ φ) z) :=
  fun d => dyadic_verticalStrip_loop_and_zfixing_deck_data c H hπfactor hqFactor d

/-- **Product-cover loop plus z-fixing deck tower.**  On a product-cover carrier, the concrete deck
`deckMap₁ ζ : (z,v₁,v₂) ↦ (z, ζ v₁, v₂)` is visibly z-fixing and branch-scaling.  This theorem pairs
any unbounded product-cover `deckMap₁` tower with the actual lifted circle loop at the same bound. -/
theorem productCover_loop_and_deckMap₁_tower
    (c : ℂ) {U : Set (ℂ × ℂ × ℂ)}
    (deckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀) :
    ∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ),
      ζ₀ ≠ 0 ∧
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ₀) U ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ₀⁻¹) U ∧
      Set.MapsTo (deckMap₁ ζ₀) U U ∧
      Set.MapsTo (deckMap₁ ζ₀⁻¹) U U ∧
      Set.EqOn (deckMap₁ ζ₀ ∘ deckMap₁ ζ₀⁻¹) id U ∧
      Set.EqOn (deckMap₁ ζ₀⁻¹ ∘ deckMap₁ ζ₀) id U ∧
      (∀ p ∈ U, (deckMap₁ ζ₀ p).1 = p.1) ∧
      (∀ p ∈ U, (deckMap₁ ζ₀ p).2.1 = ζ₀ * p.2.1) ∧
      (∀ p ∈ U, (deckMap₁ ζ₀ p).2.2 = p.2.2) := by
  intro d
  obtain ⟨R, γ, γ', hR, hperiod⟩ := exists_circle_lift_period c d
  obtain ⟨ζ₀, hζ₀, hmaps, hmaps', hord⟩ := deckF d
  refine ⟨R, γ, γ', ζ₀, hζ₀, hord, hR, hperiod,
    analyticOnNhd_deckMap₁ ζ₀ U, analyticOnNhd_deckMap₁ ζ₀⁻¹ U,
    hmaps, hmaps', deckMap₁_comp_inv_eqOn hζ₀ U, deckMap₁_inv_comp_eqOn hζ₀ U,
    ?_, ?_, ?_⟩
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

/-- **Product-cover hdisc close with the lifted loop attached.**  For a connected open product-cover
piece inside the common pullback, the existing `ProductCover` deck-map theorem gives the disconnected
`NoRelation` close; this theorem additionally records the actual lifted monodromy loop paired with the
`deckMap₁` z-fixing deck tower. -/
theorem hDisc_productCover_loop_and_deckMaps_of_commonPullback
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ : ℂ} {n m : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hzInf : ((fun p : ℂ × ℂ × ℂ => p.1) '' U).Infinite)
    (hsub : U ⊆ commonPullback c₁ c₂ n m)
    (deckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀)
    (deckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U),
        d < orderOf ζ₀) :
    (∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ),
      ζ₀ ≠ 0 ∧
      d < orderOf ζ₀ ∧
      max 2 ‖c₁‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ₀) U ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ₀⁻¹) U ∧
      Set.MapsTo (deckMap₁ ζ₀) U U ∧
      Set.MapsTo (deckMap₁ ζ₀⁻¹) U U ∧
      Set.EqOn (deckMap₁ ζ₀ ∘ deckMap₁ ζ₀⁻¹) id U ∧
      Set.EqOn (deckMap₁ ζ₀⁻¹ ∘ deckMap₁ ζ₀) id U ∧
      (∀ p ∈ U, (deckMap₁ ζ₀ p).1 = p.1) ∧
      (∀ p ∈ U, (deckMap₁ ζ₀ p).2.1 = ζ₀ * p.2.1) ∧
      (∀ p ∈ U, (deckMap₁ ζ₀ p).2.2 = p.2.2)) ∧
    (letI : IsDomain (analyticSubringGen U) := isDomain_analyticSubringGen U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
       (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
        rfl hzInf hUo hUc hUne).toAlgebra
     NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U))) := by
  refine ⟨productCover_loop_and_deckMap₁_tower c₁ deckF, ?_⟩
  exact noRelation_productCover_projectionBase_of_commonPullback_deckMaps
    hUo hUc hUne hzInf hsub deckF deckG

/-- **Finite common-pullback levels have bounded `deckMap₁` order.**  If a nonempty carrier lies
inside the fixed finite common pullback level `(n,m)` and is mapped into itself by `deckMap₁ ζ`, then
`ζ` must already be a `2^n`-th root of unity.  Thus a fixed finite product-cover level cannot by
itself supply the unbounded hdisc monodromy tower; the unbounded tower has to live on a varying-depth
or inverse-limit/log-cover carrier. -/
theorem deckMap₁_mapsTo_subset_commonPullback_pow_eq_one
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ ζ : ℂ} {n m : ℕ}
    (hUne : U.Nonempty) (hsub : U ⊆ commonPullback c₁ c₂ n m)
    (hmaps : Set.MapsTo (deckMap₁ ζ) U U) :
    ζ ^ (2 ^ n) = 1 := by
  obtain ⟨p, hpU⟩ := hUne
  rcases p with ⟨z, v₁, v₂⟩
  obtain ⟨h1, h10, _h2, _h20⟩ := hsub hpU
  obtain ⟨h1', _h10', _h2', _h20'⟩ := hsub (hmaps hpU)
  have hsame : (ζ * v₁) ^ (2 ^ n) = v₁ ^ (2 ^ n) := by
    exact h1'.trans h1.symm
  have hvpow : v₁ ^ (2 ^ n) ≠ 0 := pow_ne_zero _ h10
  apply mul_right_cancel₀ hvpow
  simpa [mul_pow] using hsame

/-- **Finite common-pullback levels have bounded `deckMap₂` order.**  Symmetric to
`deckMap₁_mapsTo_subset_commonPullback_pow_eq_one`. -/
theorem deckMap₂_mapsTo_subset_commonPullback_pow_eq_one
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ ζ : ℂ} {n m : ℕ}
    (hUne : U.Nonempty) (hsub : U ⊆ commonPullback c₁ c₂ n m)
    (hmaps : Set.MapsTo (deckMap₂ ζ) U U) :
    ζ ^ (2 ^ m) = 1 := by
  obtain ⟨p, hpU⟩ := hUne
  rcases p with ⟨z, v₁, v₂⟩
  obtain ⟨_h1, _h10, h2, h20⟩ := hsub hpU
  obtain ⟨_h1', _h10', h2', _h20'⟩ := hsub (hmaps hpU)
  have hsame : (ζ * v₂) ^ (2 ^ m) = v₂ ^ (2 ^ m) := by
    exact h2'.trans h2.symm
  have hvpow : v₂ ^ (2 ^ m) ≠ 0 := pow_ne_zero _ h20
  apply mul_right_cancel₀ hvpow
  simpa [mul_pow] using hsame

/-- A fixed finite common-pullback level cannot carry an unbounded `deckMap₁` tower. -/
theorem not_unbounded_deckMap₁_tower_on_finite_commonPullback
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ : ℂ} {n m : ℕ}
    (hUne : U.Nonempty) (hsub : U ⊆ commonPullback c₁ c₂ n m) :
    ¬ (∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀) := by
  intro deckF
  obtain ⟨ζ₀, _hζ₀, hmaps, _hmaps', hord⟩ := deckF (2 ^ n)
  have hpow : ζ₀ ^ (2 ^ n) = 1 :=
    deckMap₁_mapsTo_subset_commonPullback_pow_eq_one hUne hsub hmaps
  have hle : orderOf ζ₀ ≤ 2 ^ n := orderOf_le_of_pow_eq_one (by positivity) hpow
  exact (not_lt_of_ge hle) hord

/-- A fixed finite common-pullback level cannot carry an unbounded `deckMap₂` tower. -/
theorem not_unbounded_deckMap₂_tower_on_finite_commonPullback
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ : ℂ} {n m : ℕ}
    (hUne : U.Nonempty) (hsub : U ⊆ commonPullback c₁ c₂ n m) :
    ¬ (∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U),
        d < orderOf ζ₀) := by
  intro deckG
  obtain ⟨ζ₀, _hζ₀, hmaps, _hmaps', hord⟩ := deckG (2 ^ m)
  have hpow : ζ₀ ^ (2 ^ m) = 1 :=
    deckMap₂_mapsTo_subset_commonPullback_pow_eq_one hUne hsub hmaps
  have hle : orderOf ζ₀ ≤ 2 ^ m := orderOf_le_of_pow_eq_one (by positivity) hpow
  exact (not_lt_of_ge hle) hord

/-- **Product-cover decks produce the actual disconnected `hDisc` tuple.**  On a connected open
common-pullback piece, the concrete z-fixing deck towers `deckMap₁` and `deckMap₂` give the precise
`q62_independence` disconnected hypothesis: `v₂` is transcendental by its own unbounded monodromy,
`v₁` is nonzero on the common pullback, and `deckMap₁` supplies the unbounded tower scaling `v₁` while
fixing `v₂` and the projection base. -/
theorem hDisc_tuple_productCover_projectionBase_of_commonPullback_deckMaps
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ : ℂ} {n m : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hzInf : ((fun p : ℂ × ℂ × ℂ => p.1) '' U).Infinite)
    (hsub : U ⊆ commonPullback c₁ c₂ n m)
    (deckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀)
    (deckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U),
        d < orderOf ζ₀) :
    letI : IsDomain (analyticSubringGen U) := isDomain_analyticSubringGen U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
      (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
        rfl hzInf hUo hUc hUne).toAlgebra
    Transcendental (RatFunc ℂ)
        (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U)) ∧
      algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) ≠ 0 ∧
      ∀ d : ℕ, ∃ (σ : meroFieldGen U ≃ₐ[RatFunc ℂ] meroFieldGen U)
          (ζ : meroFieldGen U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧
        σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U))
          = algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ∧
        σ ζ = ζ ∧
        σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
          = ζ * algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
    (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hUo hUc hUne).toAlgebra
  have hF :
      algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) ≠ 0 :=
    v1CoordGen_algebraMap_ne_zero_of_subset_commonPullback hUo hUc hUne hsub
  have hG0 :
      algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ≠ 0 :=
    v2CoordGen_algebraMap_ne_zero_of_subset_commonPullback hUo hUc hUne hsub
  refine ⟨?_, hF, ?_⟩
  · refine transcendental_of_monodromy _ hG0 ?_
    intro d
    obtain ⟨ζ₀, hζ₀, hmaps, hmaps', hord⟩ := deckG d
    refine monoG_witness_product_deckMap₂ hUo hUc hUne d ζ₀ hζ₀ hmaps hmaps' hord ?_
    intro k
    have hfix : precompAnalyticGen U (analyticOnNhd_deckMap₂ ζ₀ U) hmaps (zCoordGen U)
        = zCoordGen U := by
      apply Subtype.ext
      rw [precompAnalyticGen_coe]
      exact zCoordGen_deckMap₂ hmaps
    exact precompMeroEquivGen_ratfuncToMeroViaGen_fix U
      (analyticOnNhd_deckMap₂ ζ₀ U) (analyticOnNhd_deckMap₂ ζ₀⁻¹ U)
      hmaps hmaps' (deckMap₂_comp_inv_eqOn hζ₀ U) (deckMap₂_inv_comp_eqOn hζ₀ U)
      hUo hUc hUne (p₀ := zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hfix k
  · intro d
    obtain ⟨ζ₀, hζ₀, hmaps, hmaps', hord⟩ := deckF d
    refine monoF_witness_product_deckMap₁ hUo hUc hUne d ζ₀ hζ₀ hmaps hmaps' hord ?_
    intro k
    have hfix : precompAnalyticGen U (analyticOnNhd_deckMap₁ ζ₀ U) hmaps (zCoordGen U)
        = zCoordGen U := by
      apply Subtype.ext
      rw [precompAnalyticGen_coe]
      exact zCoordGen_deckMap₁ hmaps
    exact precompMeroEquivGen_ratfuncToMeroViaGen_fix U
      (analyticOnNhd_deckMap₁ ζ₀ U) (analyticOnNhd_deckMap₁ ζ₀⁻¹ U)
      hmaps hmaps' (deckMap₁_comp_inv_eqOn hζ₀ U) (deckMap₁_inv_comp_eqOn hζ₀ U)
      hUo hUc hUne (p₀ := zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hfix k

/-- **`q62_independence` disconnected branch on the product-cover carrier.**  This routes the
concrete product-cover z-fixing deck maps through the top `q62_independence` case split: the
disconnected hypothesis is supplied by
`hDisc_tuple_productCover_projectionBase_of_commonPullback_deckMaps`, and the rigid branch is vacuous
because this theorem is the both-disconnected carrier close. -/
theorem q62_independence_productCover_projectionBase_of_commonPullback_deckMaps
    {U : Set (ℂ × ℂ × ℂ)} {c₁ c₂ : ℂ} {n m : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hzInf : ((fun p : ℂ × ℂ × ℂ => p.1) '' U).Infinite)
    (hsub : U ⊆ commonPullback c₁ c₂ n m)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (deckF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U),
        d < orderOf ζ₀)
    (deckG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (_hζ₀ : ζ₀ ≠ 0)
        (_hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
        (_hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U),
        d < orderOf ζ₀) :
    letI : IsDomain (analyticSubringGen U) := isDomain_analyticSubringGen U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
      (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
        rfl hzInf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
      (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U)) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
    (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hUo hUc hUne).toAlgebra
  have htuple :=
    hDisc_tuple_productCover_projectionBase_of_commonPullback_deckMaps
      hUo hUc hUne hzInf hsub deckF deckG
  have key := q62_independence (K := RatFunc ℂ)
    (fun c => if c = c₂
      then algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U)
      else algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
    (fun _ => True) c₁ c₂ hne hx₁ hx₂
    (fun _ _ => by
      simp only [if_neg hne]
      exact htuple)
    (fun h => absurd trivial (h.elim id id))
  simp only [if_neg hne] at key
  exact key

/-- **The vertical-strip z-fixing deck as `hliftF`.**  This is the exact lift-data shape consumed by
`Q62Assembly`: every dyadic depth gives a self-biholomorphic deck that scales `a₁ = exp ∘ φ`, fixes
`a₂` because it is pulled back from the projection base, and fixes the projection-base copy of
`ℂ(z)`. -/
theorem hliftF_of_dyadic_verticalStrip_zfixing_deck
    {U : Set ℂ} {a b : ℝ} {φ ψ π q base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U {w : ℂ | a < w.re ∧ w.re < b} φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (a₁ a₂ : analyticSubring U) {f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hF2base : ∀ z ∈ U, f₂ z = base (π z))
    (hqFactor : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | a < w.re ∧ w.re < b},
        q y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (a₁ : Germ (𝓟 U) ℂ) ∧
      (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 U) ℂ) ∧
      ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (RatFunc ℂ) (meroField U) k)
          = algebraMap (RatFunc ℂ) (meroField U) k := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, _hζ, hπfix, hscale⟩ :=
    dyadic_verticalStrip_zfixing_deck_data H hπfactor hqFactor d
  have hscale_germ :
      (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (a₁ : Germ (𝓟 U) ℂ) := by
    rw [ha₁]
    exact compTendsto_germ_scaling ζ₀ hmaps hscale
  have hinv_germ :
      (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 U) ℂ) := by
    rw [ha₂]
    refine compTendsto_germ_fixed hmaps ?_
    intro z hz
    calc
      f₂ (g z) = base (π (g z)) := hF2base (g z) (hmaps hz)
      _ = base (π z) := by rw [hπfix z hz]
      _ = f₂ z := (hF2base z hz).symm
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπfix z hz)
  refine ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale_germ, hinv_germ, ?_⟩
  intro k
  simpa using! precompMeroEquiv_ratfuncToMeroVia_fix hg hg' hmaps hmaps' hgg' hg'g
    hUo hUc hUne hp0 hπinf hpfix k

/-- **The vertical-strip z-fixing deck as `hliftG`.**  A dyadic vertical-strip deck that scales
`A = exp ∘ φ` and fixes the projection gives the symmetric lift-data tower used to prove
transcendence of that coordinate. -/
theorem hliftG_of_dyadic_verticalStrip_zfixing_deck
    {U : Set ℂ} {a b : ℝ} {φ ψ π q : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U {w : ℂ | a < w.re ∧ w.re < b} φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (A : analyticSubring U)
    (hA : (A : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (hqFactor : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | a < w.re ∧ w.re < b},
        q y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      (A : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (A : Germ (𝓟 U) ℂ) ∧
      ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (RatFunc ℂ) (meroField U) k)
          = algebraMap (RatFunc ℂ) (meroField U) k := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, _hζ, hπfix, hscale⟩ :=
    dyadic_verticalStrip_zfixing_deck_data H hπfactor hqFactor d
  have hscale_germ :
      (A : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (A : Germ (𝓟 U) ℂ) := by
    rw [hA]
    exact compTendsto_germ_scaling ζ₀ hmaps hscale
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπfix z hz)
  refine ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale_germ, ?_⟩
  intro k
  simpa using! precompMeroEquiv_ratfuncToMeroVia_fix hg hg' hmaps hmaps' hgg' hg'g
    hUo hUc hUne hp0 hπinf hpfix k

/-- **Vertical-strip z-fixing decks imply transcendence of the scaled coordinate.**  If `a` is
represented by the log-cover coordinate `exp ∘ φ`, then the dyadic z-fixing deck tower scales `a` by
roots of unbounded order while fixing the projection base `p₀ = π`.  This is exactly the `monoG`
criterion for transcendence over the projection-base copy of `ℂ(z)`. -/
theorem transcendental_of_dyadic_verticalStrip_zfixing_deck
    {U : Set ℂ} {a b : ℝ} {φ ψ π q : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U {w : ℂ | a < w.re ∧ w.re < b} φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (A : analyticSubring U)
    (hA : (A : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (hqFactor : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | a < w.re ∧ w.re < b},
        q y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  refine transcendental_of_monodromy _
    (exp_comp_algebraMap_ne_zero hUo hUc hUne A hA) ?_
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, _hζ, hπfix, hscale⟩ :=
    dyadic_verticalStrip_zfixing_deck_data H hπfactor hqFactor d
  have hscale_germ :
      (A : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (A : Germ (𝓟 U) ℂ) := by
    rw [hA]
    exact compTendsto_germ_scaling ζ₀ hmaps hscale
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπfix z hz)
  exact monoG_witness_projection_base hUo hUc hUne hp0 hπinf A d ζ₀
    hg hg' hmaps hmaps' hgg' hg'g hpfix hord hscale_germ

/-- **Vertical-strip z-fixing decks produce the actual disconnected `hDisc` tuple.**  This is the
interface used by `q62_independence`: the dyadic vertical-strip deck fixes the projection base
`p₀ = π`, fixes any second coordinate pulled back from that base, and scales the first coordinate
`exp ∘ φ` by an unbounded-order dyadic multiplier.  Thus the pointwise loop/deck construction gives
the `Transcendental ∧ nonzero ∧ monoF` tuple for the projection-base carrier. -/
theorem hDisc_tuple_of_dyadic_verticalStrip_zfixing_deck
    {U : Set ℂ} {a b : ℝ} {φ ψ π q base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U {w : ℂ | a < w.re ∧ w.re < b} φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (a₁ a₂ : analyticSubring U) {f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hGtr :
      letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
      Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (hF2base : ∀ z ∈ U, f₂ z = base (π z))
    (hqFactor : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | a < w.re ∧ w.re < b},
        q y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂) ∧
      algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0 ∧
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧
        σ (algebraMap (analyticSubring U) (meroField U) a₂)
          = algebraMap (analyticSubring U) (meroField U) a₂ ∧
        σ ζ = ζ ∧
        σ (algebraMap (analyticSubring U) (meroField U) a₁)
          = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  refine ⟨hGtr, exp_comp_algebraMap_ne_zero hUo hUc hUne a₁ ha₁, fun d => ?_⟩
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, _hζ, hπfix, hscale⟩ :=
    dyadic_verticalStrip_zfixing_deck_data H hπfactor hqFactor d
  have hscale_germ :
      (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (a₁ : Germ (𝓟 U) ℂ) := by
    rw [ha₁]
    exact compTendsto_germ_scaling ζ₀ hmaps hscale
  have hinv_germ :
      (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 U) ℂ) := by
    rw [ha₂]
    refine compTendsto_germ_fixed hmaps ?_
    intro z hz
    calc
      f₂ (g z) = base (π (g z)) := hF2base (g z) (hmaps hz)
      _ = base (π z) := by rw [hπfix z hz]
      _ = f₂ z := (hF2base z hz).symm
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπfix z hz)
  exact monoF_witness_projection_base hUo hUc hUne hp0 hπinf a₁ a₂ d ζ₀
    hg hg' hmaps hmaps' hgg' hg'g hpfix hord hscale_germ hinv_germ

/-- **Two vertical-strip z-fixing decks discharge the disconnected tuple.**  The first deck scales
`A₁ = exp ∘ φ₁` while fixing `A₂` because `A₂` is pulled back from the projection base.  The second
deck scales `A₂ = exp ∘ φ₂`, giving its transcendence over the same projection-base field.  Together
these are exactly `q62_independence`'s both-disconnected `hDisc` tuple on the projection-base
carrier. -/
theorem hDisc_tuple_of_dyadic_verticalStrip_two_zfixing_decks
    {U : Set ℂ} {r₁ s₁ r₂ s₂ : ℝ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U {w : ℂ | r₁ < w.re ∧ w.re < s₁} φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U {w : ℂ | r₂ < w.re ∧ w.re < s₂} φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (hqFactor₁ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₁ < w.re ∧ w.re < s₁},
        q₁ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y)))
    (hqFactor₂ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₂ < w.re ∧ w.re < s₂},
        q₂ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₂) ∧
      algebraMap (analyticSubring U) (meroField U) A₁ ≠ 0 ∧
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧
        σ (algebraMap (analyticSubring U) (meroField U) A₂)
          = algebraMap (analyticSubring U) (meroField U) A₂ ∧
        σ ζ = ζ ∧
        σ (algebraMap (analyticSubring U) (meroField U) A₁)
          = ζ * algebraMap (analyticSubring U) (meroField U) A₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  have hGtr :
      Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₂) :=
    transcendental_of_dyadic_verticalStrip_zfixing_deck hUo hUc hUne hp0 hπinf
      H₂ hπfactor₂ A₂ hA₂ hqFactor₂
  exact hDisc_tuple_of_dyadic_verticalStrip_zfixing_deck
    (φ := φ₁) (ψ := ψ₁) (π := π) (q := q₁) (base := base) (f₂ := Complex.exp ∘ φ₂)
    hUo hUc hUne hp0 hπinf H₁ hπfactor₁ A₁ A₂ hA₁ hA₂ hGtr hA₂base hqFactor₁

/-- **Two vertical-strip z-fixing decks imply the disconnected `NoRelation` close.**  This is the
projection-base hdisc close with the second coordinate's transcendence supplied by its own
z-fixing deck rather than assumed separately. -/
theorem hDisc_of_dyadic_verticalStrip_two_zfixing_decks
    {U : Set ℂ} {r₁ s₁ r₂ s₂ : ℝ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U {w : ℂ | r₁ < w.re ∧ w.re < s₁} φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U {w : ℂ | r₂ < w.re ∧ w.re < s₂} φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (hqFactor₁ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₁ < w.re ∧ w.re < s₁},
        q₁ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y)))
    (hqFactor₂ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₂ < w.re ∧ w.re < s₂},
        q₂ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₁)
      (algebraMap (analyticSubring U) (meroField U) A₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  obtain ⟨hGtr, hF0, monoF⟩ :=
    hDisc_tuple_of_dyadic_verticalStrip_two_zfixing_decks hUo hUc hUne hp0 hπinf
      H₁ hπfactor₁ H₂ hπfactor₂ A₁ A₂ hA₁ hA₂ hA₂base hqFactor₁ hqFactor₂
  exact q62_disconnected _ _ hGtr hF0 monoF

/-- **`q62_independence` disconnected branch from two vertical-strip decks.**  This theorem routes
the constructed z-fixing decks through the existing `q62_independence_disconnected_of_lifts`
interface: `hliftF` comes from the first deck, `hliftG` from the second deck, and nonvanishing of both
coordinates is automatic from their `exp ∘ φᵢ` representatives. -/
theorem q62_independence_disconnected_of_dyadic_verticalStrip_two_zfixing_decks
    {U : Set ℂ} {r₁ s₁ r₂ s₂ : ℝ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U {w : ℂ | r₁ < w.re ∧ w.re < s₁} φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U {w : ℂ | r₂ < w.re ∧ w.re < s₂} φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U) (c₁ c₂ : ℂ)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (hqFactor₁ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₁ < w.re ∧ w.re < s₁},
        q₁ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y)))
    (hqFactor₂ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₂ < w.re ∧ w.re < s₂},
        q₂ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₁)
      (algebraMap (analyticSubring U) (meroField U) A₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  exact q62_independence_disconnected_of_lifts hUo hUc hUne A₁ A₂ c₁ c₂ hne hx₁ hx₂
    (exp_comp_algebraMap_ne_zero hUo hUc hUne A₁ hA₁)
    (exp_comp_algebraMap_ne_zero hUo hUc hUne A₂ hA₂)
    (hliftF_of_dyadic_verticalStrip_zfixing_deck
      (φ := φ₁) (ψ := ψ₁) (π := π) (q := q₁) (base := base) (f₂ := Complex.exp ∘ φ₂)
      hUo hUc hUne hp0 hπinf H₁ hπfactor₁ A₁ A₂ hA₁ hA₂ hA₂base hqFactor₁)
    (hliftG_of_dyadic_verticalStrip_zfixing_deck
      (φ := φ₂) (ψ := ψ₂) (π := π) (q := q₂)
      hUo hUc hUne hp0 hπinf H₂ hπfactor₂ A₂ hA₂ hqFactor₂)

/-- **Loop/deck tower plus the `q62_independence` disconnected close.**  The first vertical-strip
cover supplies the concrete lifted monodromy loop and z-fixing deck tower; the pair of vertical-strip
decks supplies the `q62_independence_disconnected_of_lifts` proof of `NoRelation`. -/
theorem q62_independence_disconnected_of_dyadic_verticalStrip_loop_and_two_zfixing_decks
    (c : ℂ) {U : Set ℂ} {r₁ s₁ r₂ s₂ : ℝ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U {w : ℂ | r₁ < w.re ∧ w.re < s₁} φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U {w : ℂ | r₂ < w.re ∧ w.re < s₂} φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U) (c₁ c₂ : ℂ)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (hqFactor₁ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₁ < w.re ∧ w.re < s₁},
        q₁ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y)))
    (hqFactor₂ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₂ < w.re ∧ w.re < s₂},
        q₂ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    (∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ₁) (g z) = ζ₀ * (Complex.exp ∘ φ₁) z)) ∧
    (letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroField U) :=
       (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
     NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₁)
       (algebraMap (analyticSubring U) (meroField U) A₂)) := by
  refine ⟨dyadic_verticalStrip_loop_and_zfixing_deck_tower c H₁ hπfactor₁ hqFactor₁, ?_⟩
  exact q62_independence_disconnected_of_dyadic_verticalStrip_two_zfixing_decks hUo hUc hUne
    hp0 hπinf H₁ hπfactor₁ H₂ hπfactor₂ A₁ A₂ c₁ c₂ hne hx₁ hx₂
    hA₁ hA₂ hA₂base hqFactor₁ hqFactor₂

/-- **Loop/deck hdisc close with the second deck supplying transcendence.**  This is the current
hdisc-side capstone for the vertical-strip interface: the first log-cover supplies the concrete
lifted loop plus z-fixing deck tower and scales `A₁`; the second log-cover supplies the unbounded
monodromy proving transcendence of `A₂`. -/
theorem hDisc_of_dyadic_verticalStrip_loop_and_two_zfixing_decks
    (c : ℂ) {U : Set ℂ} {r₁ s₁ r₂ s₂ : ℝ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U {w : ℂ | r₁ < w.re ∧ w.re < s₁} φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U {w : ℂ | r₂ < w.re ∧ w.re < s₂} φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (hqFactor₁ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₁ < w.re ∧ w.re < s₁},
        q₁ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y)))
    (hqFactor₂ : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | r₂ < w.re ∧ w.re < s₂},
        q₂ y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    (∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ₁) (g z) = ζ₀ * (Complex.exp ∘ φ₁) z)) ∧
    (letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroField U) :=
       (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
     NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₁)
       (algebraMap (analyticSubring U) (meroField U) A₂)) := by
  refine ⟨dyadic_verticalStrip_loop_and_zfixing_deck_tower c H₁ hπfactor₁ hqFactor₁, ?_⟩
  exact hDisc_of_dyadic_verticalStrip_two_zfixing_decks hUo hUc hUne hp0 hπinf
    H₁ hπfactor₁ H₂ hπfactor₂ A₁ A₂ hA₁ hA₂ hA₂base hqFactor₁ hqFactor₂

/-- **hDisc from the constructed loop plus z-fixing deck tower.**  This is the hdisc-facing package:
the same vertical-strip hypotheses give both (i) the unbounded lifted monodromy-loop/z-fixing-deck
tower and (ii) the projection-base `NoRelation` close.  The `NoRelation` proof is still the
`CylinderDeck` monodromy obstruction; this theorem records that its deck input is the concrete
dyadic loop/deck construction above. -/
theorem hDisc_of_dyadic_verticalStrip_loop_and_zfixing_deck
    (c : ℂ) {U : Set ℂ} {a b : ℝ} {φ ψ π q base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U {w : ℂ | a < w.re ∧ w.re < b} φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (a₁ a₂ : analyticSubring U) {f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hGtr :
      letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
      Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (hF2base : ∀ z ∈ U, f₂ z = base (π z))
    (hqFactor : ∀ d : ℕ, ∃ Qd : ℂ → ℂ,
      ∀ y ∈ {w : ℂ | a < w.re ∧ w.re < b},
        q y = Qd (Complex.exp (((2 ^ d : ℕ) : ℂ) * y))) :
    (∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ) (g z) = ζ₀ * (Complex.exp ∘ φ) z)) ∧
    (letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroField U) :=
       (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
     NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
       (algebraMap (analyticSubring U) (meroField U) a₂)) := by
  refine ⟨dyadic_verticalStrip_loop_and_zfixing_deck_tower c H hπfactor hqFactor, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  exact hDisc_of_dyadic_verticalStrip_expPower_projection_base_tower_auto_nonzero hUo hUc hUne
    hp0 hπinf H hπfactor a₁ a₂ ha₁ ha₂ hGtr hF2base hqFactor

end Bottcher

namespace Bottcher

/-- **Dyadic additive z-fixing deck on any translation-stable log cover.**  At depth `d`, the deck is
`g = ψ ∘ (w ↦ w + 2πi/2^d) ∘ φ`.  The hypotheses are exactly the geometric content: the dyadic
translation and its inverse preserve the uniformizing region `V`, and the projection factor `q` is
invariant under that translation.  The multiplier order is proved here from `orderOf_dyadicRoot`. -/
theorem dyadic_additive_zfixing_deck_data {U V : Set ℂ} {φ ψ π q : ℂ → ℂ}
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (dyadicPeriod : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y))
    (d : ℕ) :
    ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ) (g z) = ζ₀ * (Complex.exp ∘ φ) z) := by
  let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
  have hτdata : Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y) := by
    dsimp [τ]
    exact dyadicPeriod d
  obtain ⟨hadd, hsub, hqfix⟩ := hτdata
  obtain ⟨g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hπfix, hscale⟩ :=
    additive_zfixing_deck_data (H := H) hπfactor hadd hsub hqfix
  refine ⟨Complex.exp τ, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, ?_, ?_, hπfix, ?_⟩
  · dsimp [τ]
    rw [orderOf_dyadicRoot]
    exact Nat.lt_two_pow_self
  · rfl
  · exact hscale

/-- **Dyadic additive loop plus z-fixing deck at one depth.**  The circle-lift theorem supplies the
actual Böttcher monodromy loop with period `2πi/2^d`; `dyadic_additive_zfixing_deck_data` supplies the
matching z-fixing deck on the log-cover carrier with the same dyadic multiplier. -/
theorem dyadic_additive_loop_and_zfixing_deck_data
    (c : ℂ) {U V : Set ℂ} {φ ψ π q : ℂ → ℂ}
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (dyadicPeriod : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y))
    (d : ℕ) :
    ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ) (g z) = ζ₀ * (Complex.exp ∘ φ) z) := by
  obtain ⟨R, γ, γ', hR, hperiod⟩ := exists_circle_lift_period c d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hζ, hπfix, hscale⟩ :=
    dyadic_additive_zfixing_deck_data H hπfactor dyadicPeriod d
  exact ⟨R, γ, γ', ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g,
    hord, hR, hperiod, hζ, hπfix, hscale⟩

/-- **Unbounded dyadic additive loop plus z-fixing deck tower.** -/
theorem dyadic_additive_loop_and_zfixing_deck_tower
    (c : ℂ) {U V : Set ℂ} {φ ψ π q : ℂ → ℂ}
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (dyadicPeriod : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y)) :
    ∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ) (g z) = ζ₀ * (Complex.exp ∘ φ) z) :=
  fun d => dyadic_additive_loop_and_zfixing_deck_data c H hπfactor dyadicPeriod d

/-- **Dyadic additive z-fixing decks imply transcendence of the scaled coordinate.** -/
theorem transcendental_of_dyadic_additive_zfixing_deck
    {U V : Set ℂ} {φ ψ π q : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (A : analyticSubring U)
    (hA : (A : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (dyadicPeriod : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y)) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  refine transcendental_of_monodromy _
    (exp_comp_algebraMap_ne_zero hUo hUc hUne A hA) ?_
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, _hζ, hπfix, hscale⟩ :=
    dyadic_additive_zfixing_deck_data H hπfactor dyadicPeriod d
  have hscale_germ :
      (A : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (A : Germ (𝓟 U) ℂ) := by
    rw [hA]
    exact compTendsto_germ_scaling ζ₀ hmaps hscale
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπfix z hz)
  exact monoG_witness_projection_base hUo hUc hUne hp0 hπinf A d ζ₀
    hg hg' hmaps hmaps' hgg' hg'g hpfix hord hscale_germ

/-- **Generic dyadic additive loop/deck hdisc close.**  This is the z-fixing deck interface without
specializing the uniformizing region to a vertical strip: the deck construction only needs dyadic
translation stability of `V` and dyadic invariance of the projection factor `q`. -/
theorem hDisc_of_dyadic_additive_loop_and_zfixing_deck
    (c : ℂ) {U V : Set ℂ} {φ ψ π q base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (a₁ a₂ : analyticSubring U) {f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hGtr :
      letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
      Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (hF2base : ∀ z ∈ U, f₂ z = base (π z))
    (dyadicPeriod : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y)) :
    (∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ) (g z) = ζ₀ * (Complex.exp ∘ φ) z)) ∧
    (letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroField U) :=
       (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
     NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
       (algebraMap (analyticSubring U) (meroField U) a₂)) := by
  refine ⟨dyadic_additive_loop_and_zfixing_deck_tower c H hπfactor dyadicPeriod, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  exact hDisc_of_dyadic_additive_uniformized_projection_base_tower hUo hUc hUne hp0 hπinf
    H hπfactor a₁ a₂ ha₁ ha₂
    (exp_comp_algebraMap_ne_zero hUo hUc hUne a₁ ha₁) hGtr hF2base dyadicPeriod

/-- **Generic dyadic additive loop/deck hdisc close with the second deck supplying transcendence.**
The first deck gives the loop-paired z-fixing monodromy for `A₁`; the second dyadic additive deck gives
transcendence of `A₂` over the same projection-base field. -/
theorem hDisc_of_dyadic_additive_loop_and_two_zfixing_decks
    (c : ℂ) {U V₁ V₂ : Set ℂ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U V₁ φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U V₂ φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (dyadicPeriod₁ : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V₁ V₁ ∧
      Set.MapsTo (fun w : ℂ => w - τ) V₁ V₁ ∧
      (∀ y ∈ V₁, q₁ (y + τ) = q₁ y))
    (dyadicPeriod₂ : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V₂ V₂ ∧
      Set.MapsTo (fun w : ℂ => w - τ) V₂ V₂ ∧
      (∀ y ∈ V₂, q₂ (y + τ) = q₂ y)) :
    (∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ₁) (g z) = ζ₀ * (Complex.exp ∘ φ₁) z)) ∧
    (letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroField U) :=
       (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
     NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₁)
       (algebraMap (analyticSubring U) (meroField U) A₂)) := by
  have hGtr :
      letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
      Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₂) :=
    transcendental_of_dyadic_additive_zfixing_deck hUo hUc hUne hp0 hπinf
      H₂ hπfactor₂ A₂ hA₂ dyadicPeriod₂
  exact hDisc_of_dyadic_additive_loop_and_zfixing_deck
    (φ := φ₁) (ψ := ψ₁) (π := π) (q := q₁) (base := base) (f₂ := Complex.exp ∘ φ₂)
    c hUo hUc hUne hp0 hπinf H₁ hπfactor₁ A₁ A₂ hA₁ hA₂ hGtr hA₂base dyadicPeriod₁

end Bottcher

namespace Bottcher

/-- **Generic dyadic additive z-fixing deck as `hliftF`.**  This is the additive/log-cover analogue of
`hliftF_of_dyadic_verticalStrip_zfixing_deck`: dyadic translation stability plus projection invariance
produce the exact lift-data tower consumed by `Q62Assembly`. -/
theorem hliftF_of_dyadic_additive_zfixing_deck
    {U V : Set ℂ} {φ ψ π q base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (a₁ a₂ : analyticSubring U) {f₂ : ℂ → ℂ}
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑f₂)
    (hF2base : ∀ z ∈ U, f₂ z = base (π z))
    (dyadicPeriod : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y)) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (a₁ : Germ (𝓟 U) ℂ) ∧
      (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 U) ℂ) ∧
      ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (RatFunc ℂ) (meroField U) k)
          = algebraMap (RatFunc ℂ) (meroField U) k := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, _hζ, hπfix, hscale⟩ :=
    dyadic_additive_zfixing_deck_data H hπfactor dyadicPeriod d
  have hscale_germ :
      (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (a₁ : Germ (𝓟 U) ℂ) := by
    rw [ha₁]
    exact compTendsto_germ_scaling ζ₀ hmaps hscale
  have hinv_germ :
      (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 U) ℂ) := by
    rw [ha₂]
    refine compTendsto_germ_fixed hmaps ?_
    intro z hz
    calc
      f₂ (g z) = base (π (g z)) := hF2base (g z) (hmaps hz)
      _ = base (π z) := by rw [hπfix z hz]
      _ = f₂ z := (hF2base z hz).symm
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπfix z hz)
  refine ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale_germ, hinv_germ, ?_⟩
  intro k
  simpa using! precompMeroEquiv_ratfuncToMeroVia_fix hg hg' hmaps hmaps' hgg' hg'g
    hUo hUc hUne hp0 hπinf hpfix k

/-- **Generic dyadic additive z-fixing deck as `hliftG`.** -/
theorem hliftG_of_dyadic_additive_zfixing_deck
    {U V : Set ℂ} {φ ψ π q : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H : LiftUniformization U V φ ψ)
    (hπfactor : ∀ z ∈ U, π z = q (φ z))
    (A : analyticSubring U)
    (hA : (A : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ))
    (dyadicPeriod : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V V ∧
      Set.MapsTo (fun w : ℂ => w - τ) V V ∧
      (∀ y ∈ V, q (y + τ) = q y)) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      (A : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (A : Germ (𝓟 U) ℂ) ∧
      ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (RatFunc ℂ) (meroField U) k)
          = algebraMap (RatFunc ℂ) (meroField U) k := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, _hζ, hπfix, hscale⟩ :=
    dyadic_additive_zfixing_deck_data H hπfactor dyadicPeriod d
  have hscale_germ :
      (A : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ)
          * (A : Germ (𝓟 U) ℂ) := by
    rw [hA]
    exact compTendsto_germ_scaling ζ₀ hmaps hscale
  have hpfix : precompAnalytic hg hmaps p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun z hz => hπfix z hz)
  refine ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale_germ, ?_⟩
  intro k
  simpa using! precompMeroEquiv_ratfuncToMeroVia_fix hg hg' hmaps hmaps' hgg' hg'g
    hUo hUc hUne hp0 hπinf hpfix k

/-- **Generic dyadic additive `q62_independence` disconnected close.**  The two additive z-fixing
decks are converted into the exact `hliftF`/`hliftG` data consumed by
`q62_independence_disconnected_of_lifts`; no vertical-strip quotient specialization is used here. -/
theorem q62_independence_disconnected_of_dyadic_additive_two_zfixing_decks
    {U V₁ V₂ : Set ℂ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U V₁ φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U V₂ φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U) (c₁ c₂ : ℂ)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (dyadicPeriod₁ : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V₁ V₁ ∧
      Set.MapsTo (fun w : ℂ => w - τ) V₁ V₁ ∧
      (∀ y ∈ V₁, q₁ (y + τ) = q₁ y))
    (dyadicPeriod₂ : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V₂ V₂ ∧
      Set.MapsTo (fun w : ℂ => w - τ) V₂ V₂ ∧
      (∀ y ∈ V₂, q₂ (y + τ) = q₂ y)) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₁)
      (algebraMap (analyticSubring U) (meroField U) A₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
  exact q62_independence_disconnected_of_lifts hUo hUc hUne A₁ A₂ c₁ c₂ hne hx₁ hx₂
    (exp_comp_algebraMap_ne_zero hUo hUc hUne A₁ hA₁)
    (exp_comp_algebraMap_ne_zero hUo hUc hUne A₂ hA₂)
    (hliftF_of_dyadic_additive_zfixing_deck
      (φ := φ₁) (ψ := ψ₁) (π := π) (q := q₁) (base := base) (f₂ := Complex.exp ∘ φ₂)
      hUo hUc hUne hp0 hπinf H₁ hπfactor₁ A₁ A₂ hA₁ hA₂ hA₂base dyadicPeriod₁)
    (hliftG_of_dyadic_additive_zfixing_deck
      (φ := φ₂) (ψ := ψ₂) (π := π) (q := q₂)
      hUo hUc hUne hp0 hπinf H₂ hπfactor₂ A₂ hA₂ dyadicPeriod₂)

/-- **Generic dyadic additive loop/deck tower plus `q62_independence` close.**  This is the hdisc
capstone at the additive z-fixing-deck level: the first cover supplies the actual lifted monodromy loop
and matching z-fixing deck, while the two deck towers supply the disconnected `q62_independence` proof. -/
theorem q62_independence_disconnected_of_dyadic_additive_loop_and_two_zfixing_decks
    (c : ℂ) {U V₁ V₂ : Set ℂ}
    {φ₁ ψ₁ q₁ φ₂ ψ₂ q₂ π base : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑π) (hπinf : (π '' U).Infinite)
    (H₁ : LiftUniformization U V₁ φ₁ ψ₁)
    (hπfactor₁ : ∀ z ∈ U, π z = q₁ (φ₁ z))
    (H₂ : LiftUniformization U V₂ φ₂ ψ₂)
    (hπfactor₂ : ∀ z ∈ U, π z = q₂ (φ₂ z))
    (A₁ A₂ : analyticSubring U) (c₁ c₂ : ℂ)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hA₁ : (A₁ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₁))
    (hA₂ : (A₂ : Germ (𝓟 U) ℂ) = ↑(Complex.exp ∘ φ₂))
    (hA₂base : ∀ z ∈ U, (Complex.exp ∘ φ₂) z = base (π z))
    (dyadicPeriod₁ : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V₁ V₁ ∧
      Set.MapsTo (fun w : ℂ => w - τ) V₁ V₁ ∧
      (∀ y ∈ V₁, q₁ (y + τ) = q₁ y))
    (dyadicPeriod₂ : ∀ d : ℕ,
      let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)
      Set.MapsTo (fun w : ℂ => w + τ) V₂ V₂ ∧
      Set.MapsTo (fun w : ℂ => w - τ) V₂ V₂ ∧
      (∀ y ∈ V₂, q₂ (y + τ) = q₂ y)) :
    (∀ d : ℕ, ∃ (R : ℝ) (γ γ' : ℝ → ℂ) (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (_ : AnalyticOnNhd ℂ g U) (_ : AnalyticOnNhd ℂ g' U)
        (_ : Set.MapsTo g U U) (_ : Set.MapsTo g' U U)
        (_ : Set.EqOn (g ∘ g') id U) (_ : Set.EqOn (g' ∘ g) id U),
      d < orderOf ζ₀ ∧
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ d ∧
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)) ∧
      (∀ z ∈ U, π (g z) = π z) ∧
      (∀ z ∈ U, (Complex.exp ∘ φ₁) (g z) = ζ₀ * (Complex.exp ∘ φ₁) z)) ∧
    (letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroField U) :=
       (ratfuncToMeroVia p₀ hp0 hπinf hUo hUc hUne).toAlgebra
     NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) A₁)
       (algebraMap (analyticSubring U) (meroField U) A₂)) := by
  refine ⟨dyadic_additive_loop_and_zfixing_deck_tower c H₁ hπfactor₁ dyadicPeriod₁, ?_⟩
  exact q62_independence_disconnected_of_dyadic_additive_two_zfixing_decks hUo hUc hUne
    hp0 hπinf H₁ hπfactor₁ H₂ hπfactor₂ A₁ A₂ c₁ c₂ hne hx₁ hx₂
    hA₁ hA₂ hA₂base dyadicPeriod₁ dyadicPeriod₂

end Bottcher

namespace Bottcher

/-- **Constructed disconnected loop plus the two z-fixing cover-germ decks.**  For every degree bound
`d`, choose the genuine finite dyadic level `k = d + 1`.  The already-proved circle-lift theorem gives
actual Böttcher monodromy loops for both parameters with period `2πi/2^k`, and the explicit
`commonPullback` deck automorphisms give z-fixing decks on the same carrier
`coverGerm c₁ c₂ k k`: the first scales `v₁` and fixes `z,v₂`, while the second scales `v₂` and fixes
`z,v₁`.  No analytic deck existence is assumed here; the deck maps and multiplier are constructed. -/
theorem coverGerm_loop_and_two_zfixing_decks_datum (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (k : ℕ) (R₁ : ℝ) (γ₁ γ₁' : ℝ → ℂ) (R₂ : ℝ) (γ₂ γ₂' : ℝ → ℂ)
        (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : coverGerm c₁ c₂ k k)) ∧
      max 2 ‖c₁‖ < R₁ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ₁ θ) * γ₁' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      max 2 ‖c₂‖ < R₂ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ₂ θ) * γ₂' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      ζ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ)) ∧
      deckGermEquiv hζ hpow (zGerm : coverGerm c₁ c₂ k k) = zGerm ∧
      deckGermEquiv hζ hpow (v2Germ : coverGerm c₁ c₂ k k) = v2Germ ∧
      deckGermEquiv hζ hpow ((ζ : coverGerm c₁ c₂ k k)) = (ζ : coverGerm c₁ c₂ k k) ∧
      deckGermEquiv hζ hpow (v1Germ : coverGerm c₁ c₂ k k)
        = (ζ : coverGerm c₁ c₂ k k) * v1Germ ∧
      deckGermEquiv₂ hζ hpow (zGerm : coverGerm c₁ c₂ k k) = zGerm ∧
      deckGermEquiv₂ hζ hpow (v1Germ : coverGerm c₁ c₂ k k) = v1Germ ∧
      deckGermEquiv₂ hζ hpow ((ζ : coverGerm c₁ c₂ k k)) = (ζ : coverGerm c₁ c₂ k k) ∧
      deckGermEquiv₂ hζ hpow (v2Germ : coverGerm c₁ c₂ k k)
        = (ζ : coverGerm c₁ c₂ k k) * v2Germ := by
  let k : ℕ := d + 1
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ))
  obtain ⟨R₁, γ₁, γ₁', hR₁, hperiod₁⟩ := exists_circle_lift_period c₁ k
  obtain ⟨R₂, γ₂, γ₂', hR₂, hperiod₂⟩ := exists_circle_lift_period c₂ k
  have hordζ : orderOf ζ = 2 ^ k := by
    dsimp [ζ]
    exact orderOf_dyadicRoot k
  have hζ : ζ ≠ 0 := by
    dsimp [ζ]
    exact Complex.exp_ne_zero _
  have hpow : ζ ^ (2 ^ k) = 1 := by
    calc
      ζ ^ (2 ^ k) = ζ ^ orderOf ζ := by rw [hordζ]
      _ = 1 := pow_orderOf_eq_one ζ
  have hcarrier : orderOf ((ζ : coverGerm c₁ c₂ k k)) = 2 ^ k := by
    rw [orderOf_const_coverGerm]
    exact hordζ
  refine ⟨k, R₁, γ₁, γ₁', R₂, γ₂, γ₂', ζ, hζ, hpow, ?_, hR₁, hperiod₁,
    hR₂, hperiod₂, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcarrier]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  · exact deckGermEquiv_z hζ hpow
  · exact deckGermEquiv_v2 hζ hpow
  · exact deckGermEquiv_const hζ hpow ζ
  · exact deckGermEquiv_v1 hζ hpow
  · exact deckGermEquiv₂_z hζ hpow
  · exact deckGermEquiv₂_v1 hζ hpow
  · exact deckGermEquiv₂_const hζ hpow ζ
  · exact deckGermEquiv₂_v2 hζ hpow

/-- **The constructed finite-level disconnected loop/deck tower.**  This is just
`coverGerm_loop_and_two_zfixing_decks_datum` exposed in tower form: every order bound has a constructed
finite dyadic level, monodromy loops for both coordinates, and the two z-fixing deck automorphisms. -/
theorem coverGerm_loop_and_two_zfixing_decks_tower (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
    ∃ (k : ℕ) (R₁ : ℝ) (γ₁ γ₁' : ℝ → ℂ) (R₂ : ℝ) (γ₂ γ₂' : ℝ → ℂ)
        (ζ : ℂ) (hζ : ζ ≠ 0) (hpow : ζ ^ (2 ^ k) = 1),
      d < orderOf ((ζ : coverGerm c₁ c₂ k k)) ∧
      max 2 ‖c₁‖ < R₁ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ₁ θ) * γ₁' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      max 2 ‖c₂‖ < R₂ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ₂ θ) * γ₂' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      ζ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ)) ∧
      deckGermEquiv hζ hpow (zGerm : coverGerm c₁ c₂ k k) = zGerm ∧
      deckGermEquiv hζ hpow (v2Germ : coverGerm c₁ c₂ k k) = v2Germ ∧
      deckGermEquiv hζ hpow ((ζ : coverGerm c₁ c₂ k k)) = (ζ : coverGerm c₁ c₂ k k) ∧
      deckGermEquiv hζ hpow (v1Germ : coverGerm c₁ c₂ k k)
        = (ζ : coverGerm c₁ c₂ k k) * v1Germ ∧
      deckGermEquiv₂ hζ hpow (zGerm : coverGerm c₁ c₂ k k) = zGerm ∧
      deckGermEquiv₂ hζ hpow (v1Germ : coverGerm c₁ c₂ k k) = v1Germ ∧
      deckGermEquiv₂ hζ hpow ((ζ : coverGerm c₁ c₂ k k)) = (ζ : coverGerm c₁ c₂ k k) ∧
      deckGermEquiv₂ hζ hpow (v2Germ : coverGerm c₁ c₂ k k)
        = (ζ : coverGerm c₁ c₂ k k) * v2Germ :=
  coverGerm_loop_and_two_zfixing_decks_datum c₁ c₂

end Bottcher

namespace Bottcher

/-- **Constructed finite product-cover loop plus two z-fixing deck maps.**  For every bound `d`, choose
`k = d + 1` and the primitive dyadic multiplier `ζ = exp(2πi/2^k)`.  The lifted Böttcher loops for
`c₁` and `c₂` are constructed by `exists_circle_lift_period`, while the product-cover deck maps are the
actual coordinate maps `deckMap₁ ζ` and `deckMap₂ ζ` on the concrete finite carrier
`commonPullback c₁ c₂ k k`.  Their maps-to, inverse, z-fixing, and coordinate-scaling properties are
proved here, not assumed. -/
theorem commonPullback_loop_and_two_zfixing_deckMaps_datum (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (k : ℕ) (R₁ : ℝ) (γ₁ γ₁' : ℝ → ℂ) (R₂ : ℝ) (γ₂ γ₂' : ℝ → ℂ) (ζ : ℂ),
      ζ ≠ 0 ∧ d < orderOf ζ ∧ ζ ^ (2 ^ k) = 1 ∧
      max 2 ‖c₁‖ < R₁ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ₁ θ) * γ₁' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      max 2 ‖c₂‖ < R₂ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ₂ θ) * γ₂' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      ζ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ)) ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ) (commonPullback c₁ c₂ k k) ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ⁻¹) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₁ ζ) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₁ ζ⁻¹) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₁ ζ ∘ deckMap₁ ζ⁻¹) id (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₁ ζ⁻¹ ∘ deckMap₁ ζ) id (commonPullback c₁ c₂ k k) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₁ ζ p).1 = p.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₁ ζ p).2.1 = ζ * p.2.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₁ ζ p).2.2 = p.2.2) ∧
      AnalyticOnNhd ℂ (deckMap₂ ζ) (commonPullback c₁ c₂ k k) ∧
      AnalyticOnNhd ℂ (deckMap₂ ζ⁻¹) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₂ ζ) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₂ ζ⁻¹) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₂ ζ ∘ deckMap₂ ζ⁻¹) id (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₂ ζ⁻¹ ∘ deckMap₂ ζ) id (commonPullback c₁ c₂ k k) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₂ ζ p).1 = p.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₂ ζ p).2.1 = p.2.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₂ ζ p).2.2 = ζ * p.2.2) := by
  let k : ℕ := d + 1
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ))
  obtain ⟨R₁, γ₁, γ₁', hR₁, hperiod₁⟩ := exists_circle_lift_period c₁ k
  obtain ⟨R₂, γ₂, γ₂', hR₂, hperiod₂⟩ := exists_circle_lift_period c₂ k
  have hordζ : orderOf ζ = 2 ^ k := by
    dsimp [ζ]
    exact orderOf_dyadicRoot k
  have hζ : ζ ≠ 0 := by
    dsimp [ζ]
    exact Complex.exp_ne_zero _
  have hpow : ζ ^ (2 ^ k) = 1 := by
    calc
      ζ ^ (2 ^ k) = ζ ^ orderOf ζ := by rw [hordζ]
      _ = 1 := pow_orderOf_eq_one ζ
  have hpow_inv : ζ⁻¹ ^ (2 ^ k) = 1 := inv_pow_eq_one (n := k) hpow
  refine ⟨k, R₁, γ₁, γ₁', R₂, γ₂, γ₂', ζ, hζ, ?_, hpow, hR₁, hperiod₁,
    hR₂, hperiod₂, rfl,
    analyticOnNhd_deckMap₁ ζ (commonPullback c₁ c₂ k k),
    analyticOnNhd_deckMap₁ ζ⁻¹ (commonPullback c₁ c₂ k k),
    deckMap₁_mapsTo (c₁ := c₁) (c₂ := c₂) (n := k) (m := k) hpow,
    deckMap₁_mapsTo (c₁ := c₁) (c₂ := c₂) (n := k) (m := k) hpow_inv,
    deckMap₁_comp_inv_eqOn hζ (commonPullback c₁ c₂ k k),
    deckMap₁_inv_comp_eqOn hζ (commonPullback c₁ c₂ k k),
    ?_, ?_, ?_,
    analyticOnNhd_deckMap₂ ζ (commonPullback c₁ c₂ k k),
    analyticOnNhd_deckMap₂ ζ⁻¹ (commonPullback c₁ c₂ k k),
    deckMap₂_mapsTo (c₁ := c₁) (c₂ := c₂) (n := k) (m := k) hpow,
    deckMap₂_mapsTo (c₁ := c₁) (c₂ := c₂) (n := k) (m := k) hpow_inv,
    deckMap₂_comp_inv_eqOn hζ (commonPullback c₁ c₂ k k),
    deckMap₂_inv_comp_eqOn hζ (commonPullback c₁ c₂ k k),
    ?_, ?_, ?_⟩
  · rw [hordζ]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

/-- **Constructed finite product-cover loop/deck-map tower.**  Every order bound has a constructed
finite common-pullback level, concrete monodromy loops for both coordinates, and the two coordinate
z-fixing deck maps with inverse data. -/
theorem commonPullback_loop_and_two_zfixing_deckMaps_tower (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
    ∃ (k : ℕ) (R₁ : ℝ) (γ₁ γ₁' : ℝ → ℂ) (R₂ : ℝ) (γ₂ γ₂' : ℝ → ℂ) (ζ : ℂ),
      ζ ≠ 0 ∧ d < orderOf ζ ∧ ζ ^ (2 ^ k) = 1 ∧
      max 2 ‖c₁‖ < R₁ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ₁ θ) * γ₁' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      max 2 ‖c₂‖ < R₂ ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ₂ θ) * γ₂' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ k ∧
      ζ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ)) ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ) (commonPullback c₁ c₂ k k) ∧
      AnalyticOnNhd ℂ (deckMap₁ ζ⁻¹) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₁ ζ) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₁ ζ⁻¹) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₁ ζ ∘ deckMap₁ ζ⁻¹) id (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₁ ζ⁻¹ ∘ deckMap₁ ζ) id (commonPullback c₁ c₂ k k) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₁ ζ p).1 = p.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₁ ζ p).2.1 = ζ * p.2.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₁ ζ p).2.2 = p.2.2) ∧
      AnalyticOnNhd ℂ (deckMap₂ ζ) (commonPullback c₁ c₂ k k) ∧
      AnalyticOnNhd ℂ (deckMap₂ ζ⁻¹) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₂ ζ) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.MapsTo (deckMap₂ ζ⁻¹) (commonPullback c₁ c₂ k k) (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₂ ζ ∘ deckMap₂ ζ⁻¹) id (commonPullback c₁ c₂ k k) ∧
      Set.EqOn (deckMap₂ ζ⁻¹ ∘ deckMap₂ ζ) id (commonPullback c₁ c₂ k k) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₂ ζ p).1 = p.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₂ ζ p).2.1 = p.2.1) ∧
      (∀ p ∈ commonPullback c₁ c₂ k k, (deckMap₂ ζ p).2.2 = ζ * p.2.2) :=
  commonPullback_loop_and_two_zfixing_deckMaps_datum c₁ c₂

end Bottcher

namespace Bottcher

/-- **Product-cover `c₁` deck as a projection-base `monoF` witness.**  This removes the last
base-fixing parameter from the one-step product-cover deck interface: because `deckMap₁ ζ₀` fixes
`zCoordGen`, it fixes the whole embedded `ℂ(z)` base from `ratfuncToMeroViaGen`, and the concrete
coordinate action supplies the `monoF` tuple over that base. -/
theorem monoF_witness_product_deckMap₁_projectionBase {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hzInf : ((fun p : ℂ × ℂ × ℂ => p.1) '' U).Infinite)
    (d : ℕ) (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0)
    (hmaps : Set.MapsTo (deckMap₁ ζ₀) U U)
    (hmaps' : Set.MapsTo (deckMap₁ ζ₀⁻¹) U U)
    (hord : d < orderOf ζ₀) :
    letI : IsDomain (analyticSubringGen U) := isDomain_analyticSubringGen U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
      (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
        rfl hzInf hUo hUc hUne).toAlgebra
    ∃ (σ : meroFieldGen U ≃ₐ[RatFunc ℂ] meroFieldGen U) (ζ : meroFieldGen U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U))
        = algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U))
        = ζ * algebraMap (analyticSubringGen U) (meroFieldGen U) (v1CoordGen U) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
    (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hUo hUc hUne).toAlgebra
  refine monoF_witness_product_deckMap₁ hUo hUc hUne d ζ₀ hζ₀ hmaps hmaps' hord ?_
  intro k
  have hfix : precompAnalyticGen U (analyticOnNhd_deckMap₁ ζ₀ U) hmaps (zCoordGen U)
      = zCoordGen U := by
    apply Subtype.ext
    rw [precompAnalyticGen_coe]
    exact zCoordGen_deckMap₁ hmaps
  exact precompMeroEquivGen_ratfuncToMeroViaGen_fix U
    (analyticOnNhd_deckMap₁ ζ₀ U) (analyticOnNhd_deckMap₁ ζ₀⁻¹ U)
    hmaps hmaps' (deckMap₁_comp_inv_eqOn hζ₀ U) (deckMap₁_inv_comp_eqOn hζ₀ U)
    hUo hUc hUne (p₀ := zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
    rfl hzInf hfix k

/-- **Product-cover `c₂` deck as a projection-base `monoG` witness.**  Symmetric to
`monoF_witness_product_deckMap₁_projectionBase`: `deckMap₂ ζ₀` fixes `zCoordGen`, hence fixes the
embedded `ℂ(z)` base, and scales the second branch coordinate by the constant multiplier. -/
theorem monoG_witness_product_deckMap₂_projectionBase {U : Set (ℂ × ℂ × ℂ)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hzInf : ((fun p : ℂ × ℂ × ℂ => p.1) '' U).Infinite)
    (d : ℕ) (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0)
    (hmaps : Set.MapsTo (deckMap₂ ζ₀) U U)
    (hmaps' : Set.MapsTo (deckMap₂ ζ₀⁻¹) U U)
    (hord : d < orderOf ζ₀) :
    letI : IsDomain (analyticSubringGen U) := isDomain_analyticSubringGen U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
      (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
        rfl hzInf hUo hUc hUne).toAlgebra
    ∃ (σ : meroFieldGen U ≃ₐ[RatFunc ℂ] meroFieldGen U) (ζ : meroFieldGen U),
      d < orderOf ζ ∧ σ ζ = ζ ∧
      σ (algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U))
        = ζ * algebraMap (analyticSubringGen U) (meroFieldGen U) (v2CoordGen U) := by
  haveI := isDomain_analyticSubringGen U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroFieldGen U) :=
    (ratfuncToMeroViaGen U (zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
      rfl hzInf hUo hUc hUne).toAlgebra
  refine monoG_witness_product_deckMap₂ hUo hUc hUne d ζ₀ hζ₀ hmaps hmaps' hord ?_
  intro k
  have hfix : precompAnalyticGen U (analyticOnNhd_deckMap₂ ζ₀ U) hmaps (zCoordGen U)
      = zCoordGen U := by
    apply Subtype.ext
    rw [precompAnalyticGen_coe]
    exact zCoordGen_deckMap₂ hmaps
  exact precompMeroEquivGen_ratfuncToMeroViaGen_fix U
    (analyticOnNhd_deckMap₂ ζ₀ U) (analyticOnNhd_deckMap₂ ζ₀⁻¹ U)
    hmaps hmaps' (deckMap₂_comp_inv_eqOn hζ₀ U) (deckMap₂_inv_comp_eqOn hζ₀ U)
    hUo hUc hUne (p₀ := zCoordGen U) (f₀ := fun p : ℂ × ℂ × ℂ => p.1)
    rfl hzInf hfix k

end Bottcher

namespace Bottcher

/-- **Concrete exterior-annulus z-fixing deck data.**  This exposes the actual disconnected deck map on
`U = {ξ | R' < ‖ξ‖}`: the literal rotation `ξ ↦ ζ₀ ξ` at dyadic level `n`.  It fixes the projection
`p₀(ξ)=ψ₁(ξ^(2^n))`, fixes the second coordinate `φ_{c₂}(ψ₁(ξ^(2^n)))`, has an explicit inverse
rotation, and still carries the constructed `RatFunc ℂ`-linear `monoF` output. -/
def concreteAnnulusZFixingDeckOutput (c₂ : ℂ) (n d : ℕ) (R' : ℝ) (hR'pos : 0 < R') : Prop :=
  ∃ (ψ₁ : ℂ → ℂ)
    (_hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (_hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (ζ₀ : ℂ),
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)) ∧
      ζ₀ ≠ 0 ∧ d < orderOf ζ₀ ∧ ζ₀ ^ (2 ^ n) = 1 ∧ ‖ζ₀‖ = 1 ∧
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
      AnalyticOnNhd ℂ (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} ∧
      AnalyticOnNhd ℂ (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖} ∧
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
        (fun η => ψ₁ (η ^ (2 ^ n))) (rotation ζ₀ ξ) = (fun η => ψ₁ (η ^ (2 ^ n))) ξ) ∧
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
        (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) (rotation ζ₀ ξ) =
          (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) ξ) ∧
      concreteAnnulusMonoFOutput c₂ n d R' hR'pos

/-- **Constructed exterior-annulus z-fixing deck, with no radius or multiplier hypotheses.**  The
radii are chosen by `exists_cover_annulus_radii`, and the multiplier is the primitive dyadic root at
level `d+1`; the map is the explicit annulus rotation `ξ ↦ ζ₀ ξ`. -/
theorem exists_constructed_cover_annulus_zfixing_deck_data (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' ∧
      concreteAnnulusZFixingDeckOutput c₂ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, hineq, hmonoOut⟩ := exists_constructed_cover_annulus_monoF_step c₁ c₂ d
  obtain ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hmono⟩ := hmonoOut
  let n : ℕ := d + 1
  let ζ₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))
  have hζnorm : ‖ζ₀‖ = 1 := by
    dsimp [ζ₀]
    have hprim := Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact hprim.norm'_eq_one (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  have hζ0 : ζ₀ ≠ 0 := by
    dsimp [ζ₀]
    exact Complex.exp_ne_zero _
  have hζpow : ζ₀ ^ (2 ^ n) = 1 := by
    have horder : orderOf ζ₀ = 2 ^ n := by
      dsimp [ζ₀]
      exact orderOf_dyadicRoot n
    calc
      ζ₀ ^ (2 ^ n) = ζ₀ ^ orderOf ζ₀ := by rw [horder]
      _ = 1 := pow_orderOf_eq_one ζ₀
  have hord : d < orderOf ζ₀ := by
    dsimp [ζ₀, n]
    rw [orderOf_dyadicRoot]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  have hζinvnorm : ‖ζ₀⁻¹‖ = 1 := by
    rw [norm_inv, hζnorm, inv_one]
  have hrot : Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} :=
    mapsTo_rotation_exterior hζnorm
  have hrot' : Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} :=
    mapsTo_rotation_exterior hζinvnorm
  have hcomp : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖} := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hcomp' : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖} := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hpfix : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
        (fun η => ψ₁ (η ^ (2 ^ n))) (rotation ζ₀ ξ) = (fun η => ψ₁ (η ^ (2 ^ n))) ξ :=
    p0_rotation_invariant (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n) hζpow
  have ha₂fix : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
        (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) (rotation ζ₀ ξ) =
          (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) ξ :=
    a2_rotation_invariant (c₂ := c₂) (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n) hζpow
  refine ⟨R, B, R', hR'pos, hineq, ?_⟩
  refine ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ζ₀, rfl, hζ0, hord, hζpow, hζnorm,
    ha₁, ha₂, analyticOnNhd_rotation ζ₀ _, analyticOnNhd_rotation ζ₀⁻¹ _,
    hrot, hrot', hcomp, hcomp', hpfix, ha₂fix, ?_⟩
  exact ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hmono⟩

/-- **Constructed exterior-annulus loop plus z-fixing deck.**  For every degree bound `d`, this
chooses the dyadic level `n=d+1`, constructs the actual lifted Böttcher monodromy loop for `c₁`, and
constructs the matching z-fixing annulus deck `ξ ↦ ζ₀ ξ` whose projection and second coordinate are
fixed.  This is the visible disconnected monodromy loop / z-fixing deck object with no extra
hypotheses. -/
theorem exteriorAnnulus_loop_and_zfixing_deck_data (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
      n = d + 1 ∧
      max 2 ‖c₁‖ < Rloop ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
      coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
      concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos := by
  let n : ℕ := d + 1
  obtain ⟨Rloop, γ, γ', hRloop, hperiod⟩ := exists_circle_lift_period c₁ n
  obtain ⟨R, B, R', hR'pos, hineq, hdeck⟩ := exists_constructed_cover_annulus_zfixing_deck_data c₁ c₂ d
  refine ⟨n, Rloop, γ, γ', R, B, R', hR'pos, rfl, hRloop, hperiod, ?_, ?_⟩
  · exact hineq
  · exact hdeck

end Bottcher

namespace Bottcher

/-- **Concrete exterior-annulus `hliftF` data from the explicit rotation deck.**  This is the
`q62_independence_disconnected_of_lifts` input shape for the first coordinate: the actual deck map is
`rotation ζ₀`, its inverse is `rotation ζ₀⁻¹`, it scales `a₁ = ξ`, fixes
`a₂ = φ_{c₂}(ψ₁(ξ^(2^n)))`, and fixes the projection-base copy of `RatFunc ℂ`. -/
def concreteAnnulusHLiftFOutput (c₂ : ℂ) (n d : ℕ) (R' : ℝ) (hR'pos : 0 < R') : Prop :=
  ∃ (ψ₁ : ℂ → ℂ)
    (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (ζ₀ : ℂ)
    (hg : AnalyticOnNhd ℂ (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖})
    (hg' : AnalyticOnNhd ℂ (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖})
    (hmaps : Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hmaps' : Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hgg' : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖})
    (hg'g : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖}),
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)) ∧
      ζ₀ ≠ 0 ∧ d < orderOf ζ₀ ∧ ζ₀ ^ (2 ^ n) = 1 ∧ ‖ζ₀‖ = 1 ∧
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
      (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
        isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic {ξ : ℂ | R' < ‖ξ‖} ζ₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :
            Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) * (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       ∀ k : RatFunc ℂ,
        precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          (algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)
        = algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)

/-- **Constructed exterior-annulus `hliftF` data, with no radius, multiplier, or base-fixing
hypotheses.**  This is the explicit rotation-deck lift datum used by the disconnected branch: radii,
projection, deck, inverse deck, scaling, fixing, and `RatFunc ℂ`-linearity are all constructed. -/
theorem exists_constructed_cover_annulus_hliftF_data (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' ∧
      concreteAnnulusHLiftFOutput c₂ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, hineq, hmonoOut⟩ := exists_constructed_cover_annulus_monoF_step c₁ c₂ d
  obtain ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, _hmono⟩ := hmonoOut
  let n : ℕ := d + 1
  let ζ₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))
  have hζnorm : ‖ζ₀‖ = 1 := by
    dsimp [ζ₀]
    have hprim := Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact hprim.norm'_eq_one (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  have hζ0 : ζ₀ ≠ 0 := by
    dsimp [ζ₀]
    exact Complex.exp_ne_zero _
  have hζpow : ζ₀ ^ (2 ^ n) = 1 := by
    have horder : orderOf ζ₀ = 2 ^ n := by
      dsimp [ζ₀]
      exact orderOf_dyadicRoot n
    calc
      ζ₀ ^ (2 ^ n) = ζ₀ ^ orderOf ζ₀ := by rw [horder]
      _ = 1 := pow_orderOf_eq_one ζ₀
  have hord : d < orderOf ζ₀ := by
    dsimp [ζ₀, n]
    rw [orderOf_dyadicRoot]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  have hζinvnorm : ‖ζ₀⁻¹‖ = 1 := by
    rw [norm_inv, hζnorm, inv_one]
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  have hrot : Set.MapsTo (rotation ζ₀) U U := mapsTo_rotation_exterior hζnorm
  have hrot' : Set.MapsTo (rotation ζ₀⁻¹) U U := mapsTo_rotation_exterior hζinvnorm
  have hcomp : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id U := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hcomp' : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id U := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hscale : (a₁ : Germ (𝓟 U) ℂ).compTendsto (rotation ζ₀)
        (tendsto_principal_principal.mpr hrot)
      = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) := by
    rw [ha₁]
    exact compTendsto_germ_scaling ζ₀ hrot (fun z _hz => by simp [rotation])
  have ha₂fix_pt : ∀ ξ ∈ U,
        (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) (rotation ζ₀ ξ) =
          (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) ξ :=
    a2_rotation_invariant (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n) hζpow
  have hinv : (a₂ : Germ (𝓟 U) ℂ).compTendsto (rotation ζ₀)
        (tendsto_principal_principal.mpr hrot)
      = (a₂ : Germ (𝓟 U) ℂ) := by
    rw [ha₂]
    exact compTendsto_germ_fixed hrot ha₂fix_pt
  have hpfix : precompAnalytic (analyticOnNhd_rotation ζ₀ U) hrot p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun y hy => by
      simpa [U] using p0_rotation_invariant (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n)
        hζpow y hy)
  haveI : IsDomain (analyticSubring U) :=
    isDomain_analyticSubring U isOpen_exterior (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
  have hK : ∀ k : RatFunc ℂ,
        precompMeroEquiv (analyticOnNhd_rotation ζ₀ U) (analyticOnNhd_rotation ζ₀⁻¹ U)
          hrot hrot' hcomp hcomp' isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          (algebraMap (RatFunc ℂ) (meroField U) k)
        = algebraMap (RatFunc ℂ) (meroField U) k := by
    intro k
    simpa using! precompMeroEquiv_ratfuncToMeroVia_fix
      (analyticOnNhd_rotation ζ₀ U) (analyticOnNhd_rotation ζ₀⁻¹ U)
      hrot hrot' hcomp hcomp' isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
      hp0 hpInf hpfix k
  refine ⟨R, B, R', hR'pos, hineq, ?_⟩
  refine ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ζ₀,
    analyticOnNhd_rotation ζ₀ U, analyticOnNhd_rotation ζ₀⁻¹ U,
    hrot, hrot', hcomp, hcomp', rfl, hζ0, hord, hζpow, hζnorm, ha₁, ha₂, ?_⟩
  exact ⟨hscale, hinv, hK⟩

end Bottcher

namespace Bottcher

/-- **Constructed exterior-annulus loop plus explicit `hliftF` deck data.**  This is the usable hdisc
handoff object: at level `n=d+1` it gives the genuine lifted Böttcher loop for `c₁` and the concrete
rotation deck on the exterior annulus, including its germ scaling/fixing and automatic projection-base
`RatFunc ℂ` linearity. -/
theorem exteriorAnnulus_loop_and_hliftF_data (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
      n = d + 1 ∧
      max 2 ‖c₁‖ < Rloop ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
      coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
      concreteAnnulusHLiftFOutput c₂ n d R' hR'pos := by
  let n : ℕ := d + 1
  obtain ⟨Rloop, γ, γ', hRloop, hperiod⟩ := exists_circle_lift_period c₁ n
  obtain ⟨R, B, R', hR'pos, hineq, hdeck⟩ := exists_constructed_cover_annulus_hliftF_data c₁ c₂ d
  refine ⟨n, Rloop, γ, γ', R, B, R', hR'pos, rfl, hRloop, hperiod, ?_, ?_⟩
  · exact hineq
  · exact hdeck

end Bottcher

namespace Bottcher

/-- **Constructed exterior-annulus `hliftF` tower.**  For each depth bound `d`, this chooses the
level `n=d+1`, constructs the lifted Böttcher loop, chooses radii, and returns the explicit rotation
`hliftF` data on the corresponding exterior annulus.  No radius, multiplier, base-fixing, or analytic
lift hypotheses are left to the caller. -/
theorem exteriorAnnulus_loop_and_hliftF_tower (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
        concreteAnnulusHLiftFOutput c₂ n d R' hR'pos :=
  fun d => exteriorAnnulus_loop_and_hliftF_data c₁ c₂ d

/-- **Constructed exterior-annulus z-fixing deck tower.**  This is the pointwise deck-map version of
`exteriorAnnulus_loop_and_hliftF_tower`: for every depth it constructs the actual annulus rotation
`ξ ↦ ζ₀ ξ`, its inverse, projection fixing, and second-coordinate fixing. -/
theorem exteriorAnnulus_loop_and_zfixing_deck_tower (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
        concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos :=
  fun d => exteriorAnnulus_loop_and_zfixing_deck_data c₁ c₂ d

end Bottcher

namespace Bottcher

/-- **Concrete exterior-annulus `hliftG` data from the explicit rotation deck.**  This is the
symmetric annulus lift shape: the projection comes from the inverse Böttcher coordinate for `c₂`, the
first coordinate `a₁ = φ_{c₁}(ψ₂(ξ^(2^n)))` is fixed by the rotation deck, while the second coordinate
`a₂ = ξ` is scaled by the dyadic multiplier. -/
def concreteAnnulusHLiftGOutput (c₁ : ℂ) (n d : ℕ) (R' : ℝ) (hR'pos : 0 < R') : Prop :=
  ∃ (ψ₂ : ℂ → ℂ)
    (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₂ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (ζ₀ : ℂ)
    (hg : AnalyticOnNhd ℂ (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖})
    (hg' : AnalyticOnNhd ℂ (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖})
    (hmaps : Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hmaps' : Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hgg' : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖})
    (hg'g : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖}),
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)) ∧
      ζ₀ ≠ 0 ∧ d < orderOf ζ₀ ∧ ζ₀ ^ (2 ^ n) = 1 ∧ ‖ζ₀‖ = 1 ∧
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ n)))) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
        isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic {ξ : ℂ | R' < ‖ξ‖} ζ₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :
            Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) * (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       ∀ k : RatFunc ℂ,
        precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          (algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)
        = algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)

/-- **Constructed exterior-annulus `hliftG` data.**  This is obtained by applying the concrete
`hliftF` construction to the swapped pair `(c₂,c₁)` and then exposing the witnesses with the
coordinate roles reversed: `a₁` is fixed and `a₂` is scaled. -/
theorem exists_constructed_cover_annulus_hliftG_data (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R' ∧
      concreteAnnulusHLiftGOutput c₁ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, hineq, hF⟩ := exists_constructed_cover_annulus_hliftF_data c₂ c₁ d
  obtain ⟨ψ₂, hpInf, p₀, hp0, b₂, b₁, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, hb₂, hb₁, hscale, hfix, hK⟩ := hF
  refine ⟨R, B, R', hR'pos, hineq, ?_⟩
  refine ⟨ψ₂, hpInf, p₀, hp0, b₁, b₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, hb₁, hb₂, ?_⟩
  exact ⟨hfix, hscale, hK⟩

/-- **Constructed exterior-annulus loop plus explicit `hliftG` deck data.**  At level `n=d+1`, this
constructs the genuine lifted Böttcher loop for `c₂` and the concrete rotation deck on the exterior
annulus that fixes the pulled-back `c₁` coordinate while scaling the `c₂` coordinate. -/
theorem exteriorAnnulus_loop_and_hliftG_data (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
      n = d + 1 ∧
      max 2 ‖c₂‖ < Rloop ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
      coverAnnulusRadiusIneqs c₂ c₁ n R B R' ∧
      concreteAnnulusHLiftGOutput c₁ n d R' hR'pos := by
  let n : ℕ := d + 1
  obtain ⟨Rloop, γ, γ', hRloop, hperiod⟩ := exists_circle_lift_period c₂ n
  obtain ⟨R, B, R', hR'pos, hineq, hdeck⟩ := exists_constructed_cover_annulus_hliftG_data c₁ c₂ d
  refine ⟨n, Rloop, γ, γ', R, B, R', hR'pos, rfl, hRloop, hperiod, ?_, ?_⟩
  · exact hineq
  · exact hdeck

/-- **Constructed exterior-annulus `hliftG` tower.**  Symmetric to
`exteriorAnnulus_loop_and_hliftF_tower`, this supplies the second coordinate's disconnected monodromy
loop and z-fixing rotation deck for every depth bound. -/
theorem exteriorAnnulus_loop_and_hliftG_tower (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₂ c₁ n R B R' ∧
        concreteAnnulusHLiftGOutput c₁ n d R' hR'pos :=
  fun d => exteriorAnnulus_loop_and_hliftG_data c₁ c₂ d

/-- **Constructed exterior-annulus `hliftF`/`hliftG` towers.**  This packages both directions of the
annulus monodromy construction: the first tower scales the `c₁` cover coordinate while fixing the
pulled-back `c₂` coordinate, and the second tower scales the `c₂` cover coordinate while fixing the
pulled-back `c₁` coordinate. -/
theorem exteriorAnnulus_loop_and_hliftFG_towers (c₁ c₂ : ℂ) :
    (∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
        concreteAnnulusHLiftFOutput c₂ n d R' hR'pos) ∧
    (∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₂ c₁ n R B R' ∧
        concreteAnnulusHLiftGOutput c₁ n d R' hR'pos) := by
  exact ⟨exteriorAnnulus_loop_and_hliftF_tower c₁ c₂, exteriorAnnulus_loop_and_hliftG_tower c₁ c₂⟩

end Bottcher

namespace Bottcher

/-- **Constructed exterior-annulus z-fixing deck towers in both directions.**  The first tower is the
`c₁` monodromy loop with a deck fixing the pulled-back `c₂` coordinate; the second is the symmetric
`c₂` monodromy loop with a deck fixing the pulled-back `c₁` coordinate. -/
theorem exteriorAnnulus_loop_and_two_zfixing_deck_towers (c₁ c₂ : ℂ) :
    (∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
        concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos) ∧
    (∀ d : ℕ,
      ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₂ c₁ n R B R' ∧
        concreteAnnulusZFixingDeckOutput c₁ n d R' hR'pos) := by
  exact ⟨exteriorAnnulus_loop_and_zfixing_deck_tower c₁ c₂,
    exteriorAnnulus_loop_and_zfixing_deck_tower c₂ c₁⟩

end Bottcher

namespace Bottcher

/-- **Concrete annulus `monoF` witness extracted from the explicit `hliftF` deck.**  The raw analytic
rotation data in `concreteAnnulusHLiftFOutput` is already exactly the input to `monoF_witness`; this
turns it into the algebraic automorphism witness over the projection base. -/
theorem concreteAnnulusMonoFOutput_of_hliftFOutput {c₂ : ℂ} {n d : ℕ} {R' : ℝ}
    {hR'pos : 0 < R'}
    (h : concreteAnnulusHLiftFOutput c₂ n d R' hR'pos) :
    concreteAnnulusMonoFOutput c₂ n d R' hR'pos := by
  obtain ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    _hζeq, _hζ0, hord, _hζpow, _hζnorm, ha₁, ha₂, hscale, hinv, hK⟩ := h
  refine ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, ?_⟩
  haveI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
    isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
  letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
    (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
  exact monoF_witness isOpen_exterior (isPreconnected_exterior hR'pos)
    (nonempty_exterior hR'pos) a₁ a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hinv hK

/-- The constructed `monoG` output on a positive exterior annulus. -/
def concreteAnnulusMonoGOutput (c₁ : ℂ) (n d : ℕ) (R' : ℝ) (hR'pos : 0 < R') : Prop :=
  ∃ (ψ₂ : ℂ → ℂ)
    (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₂ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ n)))) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
        isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
          (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}),
        d < orderOf ζ ∧ σ ζ = ζ ∧
        σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
          = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)

/-- **Concrete annulus `monoG` witness extracted from the explicit `hliftG` deck.**  The symmetric
analytic rotation data gives the field automorphism witness used to prove transcendence of the second
coordinate over the projection base. -/
theorem concreteAnnulusMonoGOutput_of_hliftGOutput {c₁ : ℂ} {n d : ℕ} {R' : ℝ}
    {hR'pos : 0 < R'}
    (h : concreteAnnulusHLiftGOutput c₁ n d R' hR'pos) :
    concreteAnnulusMonoGOutput c₁ n d R' hR'pos := by
  obtain ⟨ψ₂, hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    _hζeq, _hζ0, hord, _hζpow, _hζnorm, ha₁, ha₂, _hfix, hscale, hK⟩ := h
  refine ⟨ψ₂, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, ?_⟩
  haveI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
    isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
  letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
    (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
  exact monoG_witness isOpen_exterior (isPreconnected_exterior hR'pos)
    (nonempty_exterior hR'pos) a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hK

/-- **Constructed exterior-annulus `monoG` step.**  No radius, multiplier, base-fixing, or analytic
lift hypotheses are left: the symmetric annulus deck gives the algebraic `monoG` witness directly. -/
theorem exists_constructed_cover_annulus_monoG_step (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R' ∧
      concreteAnnulusMonoGOutput c₁ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, hineq, hdeck⟩ := exists_constructed_cover_annulus_hliftG_data c₁ c₂ d
  exact ⟨R, B, R', hR'pos, hineq, concreteAnnulusMonoGOutput_of_hliftGOutput hdeck⟩

/-- **Constructed exterior-annulus `monoF`/`monoG` steps.**  For every degree bound, both algebraic
monodromy witnesses are produced from concrete rotation decks on exterior annuli, one for each
coordinate direction. -/
theorem exists_constructed_cover_annulus_monoFG_steps (c₁ c₂ : ℂ) (d : ℕ) :
    (∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' ∧
      concreteAnnulusMonoFOutput c₂ (d + 1) d R' hR'pos) ∧
    (∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R' ∧
      concreteAnnulusMonoGOutput c₁ (d + 1) d R' hR'pos) := by
  exact ⟨exists_constructed_cover_annulus_monoF_step c₁ c₂ d,
    exists_constructed_cover_annulus_monoG_step c₁ c₂ d⟩

end Bottcher

namespace Bottcher

/-- **Constructed exterior-annulus loops plus algebraic `monoF`/`monoG` witnesses.**  For every degree
bound, this packages the genuine Böttcher loop together with the field-automorphism monodromy witness
produced by the corresponding z-fixing annulus deck, in both coordinate directions. -/
theorem exteriorAnnulus_loop_and_monoFG_steps (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
      (∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
        concreteAnnulusMonoFOutput c₂ n d R' hR'pos) ∧
      (∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₂ c₁ n R B R' ∧
        concreteAnnulusMonoGOutput c₁ n d R' hR'pos) := by
  intro d
  constructor
  · obtain ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hdeck⟩ :=
      exteriorAnnulus_loop_and_hliftF_data c₁ c₂ d
    exact ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq,
      concreteAnnulusMonoFOutput_of_hliftFOutput hdeck⟩
  · obtain ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hdeck⟩ :=
      exteriorAnnulus_loop_and_hliftG_data c₁ c₂ d
    exact ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq,
      concreteAnnulusMonoGOutput_of_hliftGOutput hdeck⟩

end Bottcher

namespace Bottcher

/-- **The exterior-annulus identity coordinate is nonzero in `meroField`.**  On
`U = {ξ | R' < ‖ξ‖}` with `R' > 0`, every point has nonzero norm, so the identity germ cannot vanish
in the meromorphic field. -/
theorem exterior_id_algebraMap_ne_zero {R' : ℝ} (hR'pos : 0 < R')
    (a : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (ha : (a : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ)) :
    haveI := isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
    algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a ≠ 0 := by
  haveI := isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
    (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
  intro hzero
  have ha0 : a = 0 :=
    (meroField_algebraMap_eq_zero_iff {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos) a).mp hzero
  have hgerm : (a : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = 0 := congrArg Subtype.val ha0
  rw [ha, ← Germ.coe_zero, Germ.coe_eq] at hgerm
  obtain ⟨ξ, hξ⟩ := nonempty_exterior hR'pos
  have hξ0 : ξ ≠ 0 := by
    intro h
    have hξnorm : R' < ‖ξ‖ := by simpa using hξ
    rw [h, norm_zero] at hξnorm
    linarith
  exact hξ0 (by simpa using eventually_principal.mp hgerm ξ hξ)

/-- **A constructed annulus `monoG` output has a nonzero scaling coordinate.**  This is the
single-depth datum the symmetric z-fixing deck supplies: `a₂ = ξ` is nonzero on the exterior annulus
and carries the constructed `monoG` automorphism witness over the projection base. -/
theorem concreteAnnulusMonoGOutput_with_neZero {c₁ : ℂ} {n d : ℕ} {R' : ℝ}
    {hR'pos : 0 < R'}
    (h : concreteAnnulusMonoGOutput c₁ n d R' hR'pos) :
    ∃ (ψ₂ : ℂ → ℂ)
      (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
      (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
      (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₂ (ξ ^ (2 ^ n))))
      (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
        (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
          ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ n)))) ∧
        (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
        (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
          isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
         letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
          (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
         algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ≠ 0 ∧
         ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
            (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}),
          d < orderOf ζ ∧ σ ζ = ζ ∧
          σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
            = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂) := by
  obtain ⟨ψ₂, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hmono⟩ := h
  refine ⟨ψ₂, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, ?_⟩
  haveI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
    isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
  letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
    (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
  exact ⟨exterior_id_algebraMap_ne_zero hR'pos a₂ ha₂, hmono⟩

/-- **Constructed exterior-annulus `monoG` with nonzero scaling coordinate.** -/
theorem exists_constructed_cover_annulus_monoG_step_with_neZero (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R' ∧
      ∃ (ψ₂ : ℂ → ℂ)
        (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
        (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
        (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))))
        (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
          (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ (d + 1))))) ∧
          (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
          (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
            isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
           letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
            (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
           algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ≠ 0 ∧
           ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
              (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}),
            d < orderOf ζ ∧ σ ζ = ζ ∧
            σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
              = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                  (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂) := by
  obtain ⟨R, B, R', hR'pos, hineq, hmonoG⟩ := exists_constructed_cover_annulus_monoG_step c₁ c₂ d
  exact ⟨R, B, R', hR'pos, hineq, concreteAnnulusMonoGOutput_with_neZero hmonoG⟩

end Bottcher

namespace Bottcher

/-- **A constructed annulus `monoF` output has a nonzero scaling coordinate.**  This is the first
coordinate analogue of `concreteAnnulusMonoGOutput_with_neZero`: `a₁ = ξ` is nonzero on the exterior
annulus and carries the constructed `monoF` automorphism witness over the projection base. -/
theorem concreteAnnulusMonoFOutput_with_neZero {c₂ : ℂ} {n d : ℕ} {R' : ℝ}
    {hR'pos : 0 < R'}
    (h : concreteAnnulusMonoFOutput c₂ n d R' hR'pos) :
    ∃ (ψ₁ : ℂ → ℂ)
      (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
      (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
      (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
      (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
        (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
        (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
          ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
        (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
          isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
         letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
          (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
         algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁ ≠ 0 ∧
         ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
            (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}) (m : ℕ),
          d < m ∧ orderOf ζ = m ∧
          σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
            = algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ∧
          σ ζ = ζ ∧
          σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁)
            = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁) := by
  obtain ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hmono⟩ := h
  refine ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, ?_⟩
  haveI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
    isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
  letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
    (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
  exact ⟨exterior_id_algebraMap_ne_zero hR'pos a₁ ha₁, hmono⟩

/-- **Constructed exterior-annulus `monoF` with nonzero scaling coordinate.** -/
theorem exists_constructed_cover_annulus_monoF_step_with_neZero (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' ∧
      ∃ (ψ₁ : ℂ → ℂ)
        (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
        (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
        (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
        (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
          (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
          (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
          (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
            isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
           letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
            (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
           algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁ ≠ 0 ∧
           ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
              (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}) (m : ℕ),
            d < m ∧ orderOf ζ = m ∧
            σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
              = algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ∧
            σ ζ = ζ ∧
            σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁)
              = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                  (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁) := by
  obtain ⟨R, B, R', hR'pos, hineq, hmonoF⟩ := exists_constructed_cover_annulus_monoF_step c₁ c₂ d
  exact ⟨R, B, R', hR'pos, hineq, concreteAnnulusMonoFOutput_with_neZero hmonoF⟩

/-- **Constructed exterior-annulus `monoF`/`monoG` steps with nonzero scaling coordinates.** -/
theorem exists_constructed_cover_annulus_monoFG_steps_with_neZero (c₁ c₂ : ℂ) (d : ℕ) :
    (∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' ∧
      ∃ (ψ₁ : ℂ → ℂ)
        (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
        (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
        (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
        (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
          (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
          (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
          (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
            isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
           letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
            (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
           algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁ ≠ 0)) ∧
    (∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R' ∧
      ∃ (ψ₂ : ℂ → ℂ)
        (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
        (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
        (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))))
        (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
          (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ (d + 1))))) ∧
          (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
          (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
            isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
           letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
            (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
              (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
           algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ≠ 0)) := by
  constructor
  · obtain ⟨R, B, R', hR'pos, hineq, ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hne, _hmono⟩ :=
      exists_constructed_cover_annulus_monoF_step_with_neZero c₁ c₂ d
    exact ⟨R, B, R', hR'pos, hineq, ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hne⟩
  · obtain ⟨R, B, R', hR'pos, hineq, ψ₂, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hne, _hmono⟩ :=
      exists_constructed_cover_annulus_monoG_step_with_neZero c₁ c₂ d
    exact ⟨R, B, R', hR'pos, hineq, ψ₂, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hne⟩

end Bottcher

namespace Bottcher

/-- **Constructed exterior-annulus loop/mono witnesses with nonzero moving coordinates.**  For every
order bound, the annulus construction returns the actual lifted loop, the projection-base `monoF` or
`monoG` field-automorphism witness, and the nonvanishing of the identity cover coordinate that is
scaled by the deck.  No radius, multiplier, deck-fixing, nonzero, or transcendence hypothesis is left
to the caller here; this is the fully constructed per-depth hdisc datum. -/
theorem exteriorAnnulus_loop_and_monoFG_steps_with_nonzero_identity_coordinates (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
      (∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
        concreteAnnulusMonoFOutput c₂ n d R' hR'pos ∧
        ∀ a₁ : analyticSubring {ξ : ℂ | R' < ‖ξ‖},
          (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) →
          haveI := isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
            (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁ ≠ 0) ∧
      (∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₂ c₁ n R B R' ∧
        concreteAnnulusMonoGOutput c₁ n d R' hR'pos ∧
        ∀ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖},
          (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) →
          haveI := isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
            (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ≠ 0) := by
  intro d
  constructor
  · obtain ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hmono⟩ :=
      (exteriorAnnulus_loop_and_monoFG_steps c₁ c₂ d).1
    refine ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hmono, ?_⟩
    intro a₁ ha₁
    exact exterior_id_algebraMap_ne_zero hR'pos a₁ ha₁
  · obtain ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hmono⟩ :=
      (exteriorAnnulus_loop_and_monoFG_steps c₁ c₂ d).2
    refine ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hmono, ?_⟩
    intro a₂ ha₂
    exact exterior_id_algebraMap_ne_zero hR'pos a₂ ha₂

end Bottcher

namespace Bottcher

/-- **Raw z-fixing deck extracted from the explicit `hliftF` datum.**  The `hliftF` package already
contains the annulus rotation, inverse rotation, multiplier order, and germ-level scaling/fixing; this
forgets to the pointwise z-fixing deck statement on the same carrier and same witnesses. -/
theorem concreteAnnulusZFixingDeckOutput_of_hliftFOutput {c₂ : ℂ} {n d : ℕ} {R' : ℝ}
    {hR'pos : 0 < R'}
    (h : concreteAnnulusHLiftFOutput c₂ n d R' hR'pos) :
    concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos := by
  have hmono : concreteAnnulusMonoFOutput c₂ n d R' hR'pos :=
    concreteAnnulusMonoFOutput_of_hliftFOutput h
  obtain ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, ha₁, ha₂, _hscale, _hinv, _hK⟩ := h
  refine ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ζ₀, hζeq, hζ0, hord, hζpow, hζnorm,
    ha₁, ha₂, hg, hg', hmaps, hmaps', hgg', hg'g, ?_, ?_, hmono⟩
  · exact p0_rotation_invariant (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₁) (ζ₀ := ζ₀)
      (n := n) hζpow
  · exact a2_rotation_invariant (c₂ := c₂) (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₁)
      (ζ₀ := ζ₀) (n := n) hζpow

/-- **Raw z-fixing deck extracted from the explicit `hliftG` datum.**  This is the symmetric direction,
reordered into the existing `concreteAnnulusZFixingDeckOutput` shape: the identity coordinate is the
moving coordinate and the pulled-back `c₁` Böttcher coordinate is fixed by the same annulus rotation. -/
theorem concreteAnnulusZFixingDeckOutput_of_hliftGOutput {c₁ : ℂ} {n d : ℕ} {R' : ℝ}
    {hR'pos : 0 < R'}
    (h : concreteAnnulusHLiftGOutput c₁ n d R' hR'pos) :
    concreteAnnulusZFixingDeckOutput c₁ n d R' hR'pos := by
  obtain ⟨ψ₂, hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, ha₁, ha₂, hfix, hscale, hK⟩ := h
  have hmonoF : concreteAnnulusMonoFOutput c₁ n d R' hR'pos := by
    refine ⟨ψ₂, hpInf, p₀, hp0, a₂, a₁, ha₂, ha₁, ?_⟩
    haveI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
      isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
        (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
    letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
      (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
        (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
    exact monoF_witness isOpen_exterior (isPreconnected_exterior hR'pos)
      (nonempty_exterior hR'pos) a₂ a₁ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g
      hord hscale hfix hK
  refine ⟨ψ₂, hpInf, p₀, hp0, a₂, a₁, ζ₀, hζeq, hζ0, hord, hζpow, hζnorm,
    ha₂, ha₁, hg, hg', hmaps, hmaps', hgg', hg'g, ?_, ?_, hmonoF⟩
  · exact p0_rotation_invariant (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₂) (ζ₀ := ζ₀)
      (n := n) hζpow
  · exact a2_rotation_invariant (c₂ := c₁) (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₂)
      (ζ₀ := ζ₀) (n := n) hζpow

/-- **Constructed exterior-annulus hdisc datum on one same witness in both directions.**  For every
order bound, this packages the actual lifted monodromy loop, the literal annulus rotation that fixes
the projection, the `hliftF`/`hliftG` data, the corresponding algebraic `monoF`/`monoG` witness, and
nonvanishing of the moving identity coordinate.  The two directions use their own constructed annuli,
but within each direction the loop/deck/lift/mono data are tied to the same dyadic level and carrier. -/
theorem exteriorAnnulus_loop_and_full_zfixing_monoFG_steps (c₁ c₂ : ℂ) :
    ∀ d : ℕ,
      (∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₁‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₁ c₂ n R B R' ∧
        concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos ∧
        concreteAnnulusHLiftFOutput c₂ n d R' hR'pos ∧
        concreteAnnulusMonoFOutput c₂ n d R' hR'pos ∧
        ∀ a₁ : analyticSubring {ξ : ℂ | R' < ‖ξ‖},
          (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) →
          haveI := isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
            (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁ ≠ 0) ∧
      (∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ) (R B R' : ℝ) (hR'pos : 0 < R'),
        n = d + 1 ∧
        max 2 ‖c₂‖ < Rloop ∧
        (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
        coverAnnulusRadiusIneqs c₂ c₁ n R B R' ∧
        concreteAnnulusZFixingDeckOutput c₁ n d R' hR'pos ∧
        concreteAnnulusHLiftGOutput c₁ n d R' hR'pos ∧
        concreteAnnulusMonoGOutput c₁ n d R' hR'pos ∧
        ∀ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖},
          (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) →
          haveI := isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
            (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
            (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ≠ 0) := by
  intro d
  constructor
  · obtain ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hF⟩ :=
      exteriorAnnulus_loop_and_hliftF_data c₁ c₂ d
    refine ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq,
      concreteAnnulusZFixingDeckOutput_of_hliftFOutput hF, hF,
      concreteAnnulusMonoFOutput_of_hliftFOutput hF, ?_⟩
    intro a₁ ha₁
    exact exterior_id_algebraMap_ne_zero hR'pos a₁ ha₁
  · obtain ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq, hG⟩ :=
      exteriorAnnulus_loop_and_hliftG_data c₁ c₂ d
    refine ⟨n, Rloop, γ, γ', R, B, R', hR'pos, hn, hRloop, hperiod, hineq,
      concreteAnnulusZFixingDeckOutput_of_hliftGOutput hG, hG,
      concreteAnnulusMonoGOutput_of_hliftGOutput hG, ?_⟩
    intro a₂ ha₂
    exact exterior_id_algebraMap_ne_zero hR'pos a₂ ha₂

end Bottcher

namespace Bottcher

/-- **Raw z-fixing deck extracted from a concrete annulus `monoF` output.**  The algebraic `monoF`
output already carries the inverse-Böttcher projection and identity cover coordinate.  Choosing the
primitive dyadic multiplier gives the literal annulus rotation `ξ ↦ ζ₀ ξ`, with inverse, projection
fixing, and second-coordinate fixing on the same exterior carrier. -/
theorem concreteAnnulusZFixingDeckOutput_of_monoFOutput {c₂ : ℂ} {n d : ℕ} {R' : ℝ}
    {hR'pos : 0 < R'}
    (h : concreteAnnulusMonoFOutput c₂ n d R' hR'pos)
    (hn : n = d + 1) :
    concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos := by
  have hOut := h
  obtain ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, _hmono⟩ := h
  let ζ₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))
  have hζnorm : ‖ζ₀‖ = 1 := by
    dsimp [ζ₀]
    have hprim := Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact hprim.norm'_eq_one (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  have hζ0 : ζ₀ ≠ 0 := by
    dsimp [ζ₀]
    exact Complex.exp_ne_zero _
  have hζpow : ζ₀ ^ (2 ^ n) = 1 := by
    have horder : orderOf ζ₀ = 2 ^ n := by
      dsimp [ζ₀]
      exact orderOf_dyadicRoot n
    calc
      ζ₀ ^ (2 ^ n) = ζ₀ ^ orderOf ζ₀ := by rw [horder]
      _ = 1 := pow_orderOf_eq_one ζ₀
  have hord : d < orderOf ζ₀ := by
    dsimp [ζ₀]
    rw [orderOf_dyadicRoot, hn]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  have hζinvnorm : ‖ζ₀⁻¹‖ = 1 := by
    rw [norm_inv, hζnorm, inv_one]
  have hrot : Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} :=
    mapsTo_rotation_exterior hζnorm
  have hrot' : Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} :=
    mapsTo_rotation_exterior hζinvnorm
  have hcomp : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖} := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hcomp' : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖} := by
    intro ξ _hξ
    simp [rotation, hζ0]
  refine ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ζ₀, rfl, hζ0, hord, hζpow, hζnorm,
    ha₁, ha₂, analyticOnNhd_rotation ζ₀ _, analyticOnNhd_rotation ζ₀⁻¹ _,
    hrot, hrot', hcomp, hcomp', ?_, ?_, hOut⟩
  · exact p0_rotation_invariant (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₁) (ζ₀ := ζ₀)
      (n := n) hζpow
  · exact a2_rotation_invariant (c₂ := c₂) (U := {ξ : ℂ | R' < ‖ξ‖}) (ψ₁ := ψ₁)
      (ζ₀ := ζ₀) (n := n) hζpow

/-- **Uniform exterior-annulus z-fixing deck tower.**  One exterior carrier radius `R'` is chosen once;
for every dyadic bound the same carrier supports the constructed raw z-fixing rotation deck and the
corresponding `monoF` witness. -/
theorem exists_uniform_cover_annulus_zfixing_deck_tower (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ, concreteAnnulusZFixingDeckOutput c₂ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, hall, hmono⟩ := exists_uniform_cover_annulus_monoF_steps c₁ c₂
  refine ⟨R, B, R', hR'pos, hall, fun d => ?_⟩
  exact concreteAnnulusZFixingDeckOutput_of_monoFOutput (hmono d) rfl

/-- **Uniform-carrier loop plus z-fixing deck tower.**  The loop radius may vary with the dyadic level,
but the exterior annulus carrying the explicit z-fixing rotation deck is fixed once for all `d`. -/
theorem exteriorAnnulus_loop_and_uniform_zfixing_deck_tower (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₁‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, hall, hdeck⟩ := exists_uniform_cover_annulus_zfixing_deck_tower c₁ c₂
  refine ⟨R, B, R', hR'pos, hall, fun d => ?_⟩
  let n : ℕ := d + 1
  obtain ⟨Rloop, γ, γ', hRloop, hperiod⟩ := exists_circle_lift_period c₁ n
  exact ⟨n, Rloop, γ, γ', rfl, hRloop, hperiod, hdeck d⟩

/-- **Uniform-carrier loop plus z-fixing deck towers in both coordinate directions.**  Each direction
gets its own fixed exterior carrier, and for every dyadic bound that carrier supports the constructed
loop-matched z-fixing deck. -/
theorem exteriorAnnulus_loop_and_uniform_two_zfixing_deck_towers (c₁ c₂ : ℂ) :
    (∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₁‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusZFixingDeckOutput c₂ n d R' hR'pos) ∧
    (∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₂‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusZFixingDeckOutput c₁ n d R' hR'pos) := by
  exact ⟨exteriorAnnulus_loop_and_uniform_zfixing_deck_tower c₁ c₂,
    exteriorAnnulus_loop_and_uniform_zfixing_deck_tower c₂ c₁⟩

end Bottcher

namespace Bottcher

/-- **Concrete exterior-annulus z-fixing deck with a fixed inverse branch.**  This is the raw deck
object from `concreteAnnulusZFixingDeckOutput`, but with `ψ₁` supplied as a parameter so a tower can
state that the same far-field inverse branch is used at every dyadic depth. -/
def concreteAnnulusZFixingDeckOutputWithFixedInverse (c₂ : ℂ) (ψ₁ : ℂ → ℂ)
    (n d : ℕ) (R' : ℝ) (_hR'pos : 0 < R') : Prop :=
  ∃ (_hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (_hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (ζ₀ : ℂ),
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)) ∧
      ζ₀ ≠ 0 ∧ d < orderOf ζ₀ ∧ ζ₀ ^ (2 ^ n) = 1 ∧ ‖ζ₀‖ = 1 ∧
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
      AnalyticOnNhd ℂ (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} ∧
      AnalyticOnNhd ℂ (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖} ∧
      Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖} ∧
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
        (fun η => ψ₁ (η ^ (2 ^ n))) (rotation ζ₀ ξ) = (fun η => ψ₁ (η ^ (2 ^ n))) ξ) ∧
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
        (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) (rotation ζ₀ ξ) =
          (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) ξ)

/-- **Build the z-fixing annulus rotation deck from one fixed inverse branch.**  Analyticity and
far-field containment construct the projection and second coordinate; the dyadic multiplier supplies
the literal rotation deck fixing both. -/
theorem concreteAnnulusZFixingDeckOutputWithFixedInverse_of_projection_data
    {c₂ : ℂ} {ψ₁ : ℂ → ℂ} {n d : ℕ} {R' : ℝ} {hR'pos : 0 < R'}
    (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (hψan : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂)
    (hn : n = d + 1) :
    concreteAnnulusZFixingDeckOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos := by
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  obtain ⟨p₀, hp0⟩ := exists_projection_p0 (U := U) (ψ₁ := ψ₁) (n := n) (by
    simpa [U] using hψan)
  let a₁ : analyticSubring U :=
    ⟨(↑(id : ℂ → ℂ) : Germ (𝓟 U) ℂ), id, analyticOnNhd_id, rfl⟩
  have ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(id : ℂ → ℂ) := rfl
  obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := n)
    (by simpa [U] using hψan) (by simpa [U] using hcont)
  let ζ₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))
  have hζnorm : ‖ζ₀‖ = 1 := by
    dsimp [ζ₀]
    have hprim := Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact hprim.norm'_eq_one (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  have hζ0 : ζ₀ ≠ 0 := by
    dsimp [ζ₀]
    exact Complex.exp_ne_zero _
  have hζpow : ζ₀ ^ (2 ^ n) = 1 := by
    have horder : orderOf ζ₀ = 2 ^ n := by
      dsimp [ζ₀]
      exact orderOf_dyadicRoot n
    calc
      ζ₀ ^ (2 ^ n) = ζ₀ ^ orderOf ζ₀ := by rw [horder]
      _ = 1 := pow_orderOf_eq_one ζ₀
  have hord : d < orderOf ζ₀ := by
    dsimp [ζ₀]
    rw [orderOf_dyadicRoot, hn]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  have hζinvnorm : ‖ζ₀⁻¹‖ = 1 := by
    rw [norm_inv, hζnorm, inv_one]
  have hrot : Set.MapsTo (rotation ζ₀) U U := mapsTo_rotation_exterior hζnorm
  have hrot' : Set.MapsTo (rotation ζ₀⁻¹) U U := mapsTo_rotation_exterior hζinvnorm
  have hcomp : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id U := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hcomp' : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id U := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hpfix : ∀ ξ ∈ U,
      (fun η => ψ₁ (η ^ (2 ^ n))) (rotation ζ₀ ξ) = (fun η => ψ₁ (η ^ (2 ^ n))) ξ :=
    p0_rotation_invariant (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n) hζpow
  have ha₂fix : ∀ ξ ∈ U,
      (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) (rotation ζ₀ ξ) =
        (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) ξ :=
    a2_rotation_invariant (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n) hζpow
  refine ⟨by simpa [U] using hpInf, by simpa [U] using p₀, by simpa [U] using hp0,
    by simpa [U] using a₁, by simpa [U] using a₂, ζ₀, rfl, hζ0, hord, hζpow, hζnorm,
    by simpa [U] using ha₁, by simpa [U] using ha₂,
    analyticOnNhd_rotation ζ₀ _, analyticOnNhd_rotation ζ₀⁻¹ _,
    by simpa [U] using hrot, by simpa [U] using hrot', by simpa [U] using hcomp,
    by simpa [U] using hcomp', by simpa [U] using hpfix, by simpa [U] using ha₂fix⟩

/-- **Uniform z-fixing deck tower with one exterior carrier and one inverse branch.**  The same
far-field inverse `ψ₁` and the same annulus `{ξ | R' < ‖ξ‖}` are used for every dyadic bound; at level
`d` only the finite projection `ψ₁(ξ^(2^(d+1)))` and its induced coordinate change. -/
theorem exists_uniform_cover_annulus_zfixing_deck_tower_with_fixed_inverse (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ, concreteAnnulusZFixingDeckOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hall, hdata⟩ :=
    exists_uniform_cover_annulus_data_with_fixed_inverse_projection c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₁, hall, fun d => ?_⟩
  obtain ⟨hψan, hcont, _hproj, hpInf⟩ := hdata d
  exact concreteAnnulusZFixingDeckOutputWithFixedInverse_of_projection_data hpInf hψan hcont rfl

/-- **Uniform-carrier loop plus z-fixing deck tower with a fixed inverse branch.**  This is the concrete
monodromy-loop/deck package: the lifted loop is built at each dyadic level, while the deck side uses
one exterior carrier and one inverse Böttcher branch across the whole tower. -/
theorem exteriorAnnulus_loop_and_uniform_zfixing_deck_tower_with_fixed_inverse (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₁‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusZFixingDeckOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hall, hdeck⟩ :=
    exists_uniform_cover_annulus_zfixing_deck_tower_with_fixed_inverse c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₁, hall, fun d => ?_⟩
  let n : ℕ := d + 1
  obtain ⟨Rloop, γ, γ', hRloop, hperiod⟩ := exists_circle_lift_period c₁ n
  exact ⟨n, Rloop, γ, γ', rfl, hRloop, hperiod, hdeck d⟩

/-- **Both coordinate directions of the fixed-inverse uniform z-fixing tower.** -/
theorem exteriorAnnulus_loop_and_uniform_two_zfixing_deck_towers_with_fixed_inverse (c₁ c₂ : ℂ) :
    (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₁‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusZFixingDeckOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos) ∧
    (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₂‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusZFixingDeckOutputWithFixedInverse c₁ ψ₁ n d R' hR'pos) := by
  exact ⟨exteriorAnnulus_loop_and_uniform_zfixing_deck_tower_with_fixed_inverse c₁ c₂,
    exteriorAnnulus_loop_and_uniform_zfixing_deck_tower_with_fixed_inverse c₂ c₁⟩

end Bottcher

namespace Bottcher

/-- **Fixed-inverse exterior-annulus `hliftF` data.**  This is
`concreteAnnulusHLiftFOutput` with the inverse Böttcher branch `ψ₁` exposed as a fixed parameter, so a
uniform tower can state that the same inverse branch supplies every dyadic depth. -/
def concreteAnnulusHLiftFOutputWithFixedInverse (c₂ : ℂ) (ψ₁ : ℂ → ℂ)
    (n d : ℕ) (R' : ℝ) (hR'pos : 0 < R') : Prop :=
  ∃ (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (ζ₀ : ℂ)
    (hg : AnalyticOnNhd ℂ (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖})
    (hg' : AnalyticOnNhd ℂ (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖})
    (hmaps : Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hmaps' : Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hgg' : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖})
    (hg'g : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖}),
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)) ∧
      ζ₀ ≠ 0 ∧ d < orderOf ζ₀ ∧ ζ₀ ^ (2 ^ n) = 1 ∧ ‖ζ₀‖ = 1 ∧
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
      (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
        isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic {ξ : ℂ | R' < ‖ξ‖} ζ₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :
            Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) * (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       ∀ k : RatFunc ℂ,
        precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          (algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)
        = algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)

/-- **Fixed-inverse projection data gives the full `hliftF` germ datum.**  The same rotation deck that
pointwise fixes the finite projection also gives germ scaling of `a₁ = ξ`, germ fixing of the
pulled-back `c₂` coordinate, and `RatFunc ℂ`-linearity over the projection base. -/
theorem concreteAnnulusHLiftFOutputWithFixedInverse_of_projection_data
    {c₂ : ℂ} {ψ₁ : ℂ → ℂ} {n d : ℕ} {R' : ℝ} {hR'pos : 0 < R'}
    (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (hψan : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂)
    (hn : n = d + 1) :
    concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos := by
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  obtain ⟨p₀, hp0⟩ := exists_projection_p0 (U := U) (ψ₁ := ψ₁) (n := n) (by
    simpa [U] using hψan)
  let a₁ : analyticSubring U :=
    ⟨(↑(id : ℂ → ℂ) : Germ (𝓟 U) ℂ), id, analyticOnNhd_id, rfl⟩
  have ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(id : ℂ → ℂ) := rfl
  obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := n)
    (by simpa [U] using hψan) (by simpa [U] using hcont)
  let ζ₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))
  have hζnorm : ‖ζ₀‖ = 1 := by
    dsimp [ζ₀]
    have hprim := Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact hprim.norm'_eq_one (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  have hζ0 : ζ₀ ≠ 0 := by
    dsimp [ζ₀]
    exact Complex.exp_ne_zero _
  have hζpow : ζ₀ ^ (2 ^ n) = 1 := by
    have horder : orderOf ζ₀ = 2 ^ n := by
      dsimp [ζ₀]
      exact orderOf_dyadicRoot n
    calc
      ζ₀ ^ (2 ^ n) = ζ₀ ^ orderOf ζ₀ := by rw [horder]
      _ = 1 := pow_orderOf_eq_one ζ₀
  have hord : d < orderOf ζ₀ := by
    dsimp [ζ₀]
    rw [orderOf_dyadicRoot, hn]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  have hζinvnorm : ‖ζ₀⁻¹‖ = 1 := by
    rw [norm_inv, hζnorm, inv_one]
  have hrot : Set.MapsTo (rotation ζ₀) U U := mapsTo_rotation_exterior hζnorm
  have hrot' : Set.MapsTo (rotation ζ₀⁻¹) U U := mapsTo_rotation_exterior hζinvnorm
  have hcomp : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id U := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hcomp' : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id U := by
    intro ξ _hξ
    simp [rotation, hζ0]
  have hscale : (a₁ : Germ (𝓟 U) ℂ).compTendsto (rotation ζ₀)
        (tendsto_principal_principal.mpr hrot)
      = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) := by
    rw [ha₁]
    exact compTendsto_germ_scaling ζ₀ hrot (fun z _hz => by simp [rotation])
  have ha₂fix_pt : ∀ ξ ∈ U,
      (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) (rotation ζ₀ ξ) =
        (fun η => bottcherCoord c₂ (ψ₁ (η ^ (2 ^ n)))) ξ :=
    a2_rotation_invariant (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n) hζpow
  have hinv : (a₂ : Germ (𝓟 U) ℂ).compTendsto (rotation ζ₀)
        (tendsto_principal_principal.mpr hrot)
      = (a₂ : Germ (𝓟 U) ℂ) := by
    rw [ha₂]
    exact compTendsto_germ_fixed hrot ha₂fix_pt
  have hpfix : precompAnalytic (analyticOnNhd_rotation ζ₀ U) hrot p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun y hy => by
      simpa [U] using p0_rotation_invariant (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n)
        hζpow y hy)
  haveI : IsDomain (analyticSubring U) :=
    isDomain_analyticSubring U isOpen_exterior (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 (by simpa [U] using hpInf) isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
  have hK : ∀ k : RatFunc ℂ,
      precompMeroEquiv (analyticOnNhd_rotation ζ₀ U) (analyticOnNhd_rotation ζ₀⁻¹ U)
        hrot hrot' hcomp hcomp' isOpen_exterior
        (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
        (algebraMap (RatFunc ℂ) (meroField U) k)
      = algebraMap (RatFunc ℂ) (meroField U) k := by
    intro k
    simpa using! precompMeroEquiv_ratfuncToMeroVia_fix
      (analyticOnNhd_rotation ζ₀ U) (analyticOnNhd_rotation ζ₀⁻¹ U)
      hrot hrot' hcomp hcomp' isOpen_exterior
      (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
      hp0 (by simpa [U] using hpInf) hpfix k
  refine ⟨by simpa [U] using hpInf, by simpa [U] using p₀, by simpa [U] using hp0,
    by simpa [U] using a₁, by simpa [U] using a₂, ζ₀,
    analyticOnNhd_rotation ζ₀ _, analyticOnNhd_rotation ζ₀⁻¹ _,
    by simpa [U] using hrot, by simpa [U] using hrot', by simpa [U] using hcomp,
    by simpa [U] using hcomp', rfl, hζ0, hord, hζpow, hζnorm,
    by simpa [U] using ha₁, by simpa [U] using ha₂, ?_⟩
  exact ⟨by simpa [U] using hscale, by simpa [U] using hinv, by simpa [U] using hK⟩

/-- **Fixed-inverse exterior-annulus `hliftG` data.**  Coordinate-reversed form of
`concreteAnnulusHLiftFOutputWithFixedInverse`: the pulled-back first coordinate is fixed and
`a₂ = ξ` is scaled. -/
def concreteAnnulusHLiftGOutputWithFixedInverse (c₁ : ℂ) (ψ₂ : ℂ → ℂ)
    (n d : ℕ) (R' : ℝ) (hR'pos : 0 < R') : Prop :=
  ∃ (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₂ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (ζ₀ : ℂ)
    (hg : AnalyticOnNhd ℂ (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖})
    (hg' : AnalyticOnNhd ℂ (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖})
    (hmaps : Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hmaps' : Set.MapsTo (rotation ζ₀⁻¹) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖})
    (hgg' : Set.EqOn (rotation ζ₀ ∘ rotation ζ₀⁻¹) id {ξ : ℂ | R' < ‖ξ‖})
    (hg'g : Set.EqOn (rotation ζ₀⁻¹ ∘ rotation ζ₀) id {ξ : ℂ | R' < ‖ξ‖}),
      ζ₀ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ)) ∧
      ζ₀ ≠ 0 ∧ d < orderOf ζ₀ ∧ ζ₀ ^ (2 ^ n) = 1 ∧ ‖ζ₀‖ = 1 ∧
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ n)))) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
        isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ).compTendsto (rotation ζ₀)
          (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic {ξ : ℂ | R' < ‖ξ‖} ζ₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :
            Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) * (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) ∧
       ∀ k : RatFunc ℂ,
        precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
          (algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)
        = algebraMap (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) k)

/-- **Coordinate reversal turns fixed-inverse `hliftF` into fixed-inverse `hliftG`.** -/
theorem concreteAnnulusHLiftGOutputWithFixedInverse_of_hliftFOutputWithFixedInverse
    {c₁ : ℂ} {ψ₂ : ℂ → ℂ} {n d : ℕ} {R' : ℝ} {hR'pos : 0 < R'}
    (h : concreteAnnulusHLiftFOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos) :
    concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos := by
  obtain ⟨hpInf, p₀, hp0, b₂, b₁, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, hb₂, hb₁, hscale, hfix, hK⟩ := h
  refine ⟨hpInf, p₀, hp0, b₁, b₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, hb₁, hb₂, ?_⟩
  exact ⟨hfix, hscale, hK⟩

/-- **Fixed-inverse projection data gives the full `hliftG` germ datum.** -/
theorem concreteAnnulusHLiftGOutputWithFixedInverse_of_projection_data
    {c₁ : ℂ} {ψ₂ : ℂ → ℂ} {n d : ℕ} {R' : ℝ} {hR'pos : 0 < R'}
    (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (hψan : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₂ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₂ (ξ ^ (2 ^ n)) ∈ escapeOpen c₁)
    (hn : n = d + 1) :
    concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos := by
  exact concreteAnnulusHLiftGOutputWithFixedInverse_of_hliftFOutputWithFixedInverse
    (concreteAnnulusHLiftFOutputWithFixedInverse_of_projection_data
      (c₂ := c₁) (ψ₁ := ψ₂) hpInf hψan hcont hn)

/-- **Uniform fixed-inverse `hliftF` tower on one exterior carrier.** -/
theorem exists_uniform_cover_annulus_hliftF_tower_with_fixed_inverse (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ, concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hall, hdata⟩ :=
    exists_uniform_cover_annulus_data_with_fixed_inverse_projection c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₁, hall, fun d => ?_⟩
  obtain ⟨hψan, hcont, _hproj, hpInf⟩ := hdata d
  exact concreteAnnulusHLiftFOutputWithFixedInverse_of_projection_data hpInf hψan hcont rfl

/-- **Uniform fixed-inverse `hliftG` tower on one exterior carrier.** -/
theorem exists_uniform_cover_annulus_hliftG_tower_with_fixed_inverse (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      ∀ d : ℕ, concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, ψ₂, hall, hdata⟩ :=
    exists_uniform_cover_annulus_data_with_fixed_inverse_projection c₂ c₁
  refine ⟨R, B, R', hR'pos, ψ₂, hall, fun d => ?_⟩
  obtain ⟨hψan, hcont, _hproj, hpInf⟩ := hdata d
  exact concreteAnnulusHLiftGOutputWithFixedInverse_of_projection_data hpInf hψan hcont rfl

/-- **Uniform-carrier loop plus fixed-inverse `hliftF` tower.** -/
theorem exteriorAnnulus_loop_and_uniform_hliftF_tower_with_fixed_inverse (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₁‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hall, hdeck⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_fixed_inverse c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₁, hall, fun d => ?_⟩
  let n : ℕ := d + 1
  obtain ⟨Rloop, γ, γ', hRloop, hperiod⟩ := exists_circle_lift_period c₁ n
  exact ⟨n, Rloop, γ, γ', rfl, hRloop, hperiod, hdeck d⟩

/-- **Uniform-carrier loop plus fixed-inverse `hliftG` tower.** -/
theorem exteriorAnnulus_loop_and_uniform_hliftG_tower_with_fixed_inverse (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₂‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos := by
  obtain ⟨R, B, R', hR'pos, ψ₂, hall, hdeck⟩ :=
    exists_uniform_cover_annulus_hliftG_tower_with_fixed_inverse c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₂, hall, fun d => ?_⟩
  let n : ℕ := d + 1
  obtain ⟨Rloop, γ, γ', hRloop, hperiod⟩ := exists_circle_lift_period c₂ n
  exact ⟨n, Rloop, γ, γ', rfl, hRloop, hperiod, hdeck d⟩

/-- **Both coordinate directions of the fixed-inverse uniform `hlift` towers.** -/
theorem exteriorAnnulus_loop_and_uniform_hliftFG_towers_with_fixed_inverse (c₁ c₂ : ℂ) :
    (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₁‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₁) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos) ∧
    (∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      ∀ d : ℕ,
        ∃ (n : ℕ) (Rloop : ℝ) (γ γ' : ℝ → ℂ),
          n = d + 1 ∧
          max 2 ‖c₂‖ < Rloop ∧
          (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c₂) (γ θ) * γ' θ)
            = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n ∧
          concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos) := by
  exact ⟨exteriorAnnulus_loop_and_uniform_hliftF_tower_with_fixed_inverse c₁ c₂,
    exteriorAnnulus_loop_and_uniform_hliftG_tower_with_fixed_inverse c₁ c₂⟩

end Bottcher

namespace Bottcher

/-- Forget the explicit fixed inverse branch from the fixed-inverse `hliftF` package. -/
theorem concreteAnnulusHLiftFOutput_of_fixed_inverse {c₂ : ℂ} {ψ₁ : ℂ → ℂ}
    {n d : ℕ} {R' : ℝ} {hR'pos : 0 < R'}
    (h : concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ n d R' hR'pos) :
    concreteAnnulusHLiftFOutput c₂ n d R' hR'pos := by
  obtain ⟨hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, ha₁, ha₂, htail⟩ := h
  exact ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, ha₁, ha₂, htail⟩

/-- Forget the explicit fixed inverse branch from the fixed-inverse `hliftG` package. -/
theorem concreteAnnulusHLiftGOutput_of_fixed_inverse {c₁ : ℂ} {ψ₂ : ℂ → ℂ}
    {n d : ℕ} {R' : ℝ} {hR'pos : 0 < R'}
    (h : concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ n d R' hR'pos) :
    concreteAnnulusHLiftGOutput c₁ n d R' hR'pos := by
  obtain ⟨hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, ha₁, ha₂, htail⟩ := h
  exact ⟨ψ₂, hpInf, p₀, hp0, a₁, a₂, ζ₀, hg, hg', hmaps, hmaps', hgg', hg'g,
    hζeq, hζ0, hord, hζpow, hζnorm, ha₁, ha₂, htail⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Uniform fixed-inverse hLiftF plus the matching pulled-back transcendence witness.**  The annulus
root coordinate changes the projection base with the dyadic depth, so this deliberately packages the
handoff per depth rather than forcing a single fixed-field tower.  For each `d`, the same far-field
inverse branch gives the concrete `hliftF` datum at level `d+1`; if the far high-value downstairs set
has no nonzero relation `q(z,φ_{c₂}(z))`, it also gives the exact projection-base transcendence of the
pulled-back coordinate on that same annulus. -/
theorem exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_no_far_high_relation
    (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos ∧
        ((∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
          ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
            {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖}) →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂))) := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₁, hall, hψleft, fun d => ?_⟩
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  let N : ℕ := 2 ^ (d + 1)
  obtain ⟨hψan, hcont, _hproj, hpInf, _himage⟩ := hdata d
  constructor
  · exact concreteAnnulusHLiftFOutputWithFixedInverse_of_projection_data hpInf hψan hcont rfl
  · intro hno
    obtain ⟨p₀, hp0⟩ := exists_projection_p0 (U := U) (ψ₁ := ψ₁) (n := d + 1) (by
      simpa [U] using hψan)
    obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := d + 1)
      (by simpa [U] using hψan) (by simpa [U] using hcont)
    have hNpos : 0 < N := by
      dsimp [N]
      exact pow_pos (by norm_num : (0 : ℕ) < 2) (d + 1)
    have htr := transcendental_pullback_bottcher_of_no_far_high_relation
      (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (R := R) (R' := R') (N := N)
      hR'pos hNpos hψleft (p₀ := p₀) (a := a₂) hp0
      (by simpa [U, N] using hpInf) (by simpa [U, N] using ha₂)
      (by simpa [N] using hno)
    refine ⟨by simpa [U] using p₀, by simpa [U, N] using hp0,
      by simpa [U, N] using hpInf, by simpa [U] using a₂,
      by simpa [U, N] using ha₂, ?_⟩
    simpa [U, N] using htr

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Symmetric uniform fixed-inverse hLiftG plus pulled-back transcendence witness.**  This is the
coordinate-reversed form of
`exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_no_far_high_relation`: the fixed
inverse branch is now for `c₂`, the concrete datum is `hliftG`, and the far high-value obstruction
proves transcendence of the pulled-back `c₁` coordinate over the projection base. -/
theorem exists_uniform_cover_annulus_hliftG_tower_with_transcendence_of_no_far_high_relation
    (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₂ (bottcherCoord c₂ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ (d + 1) d R' hR'pos ∧
        ((∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
          ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₁ z)) 0
            {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₂ z‖}) →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₁ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁))) := by
  obtain ⟨R, B, R', hR'pos, ψ₂, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_no_far_high_relation c₂ c₁
  refine ⟨R, B, R', hR'pos, ψ₂, hall, hψleft, fun d => ?_⟩
  obtain ⟨hF, htr⟩ := hdata d
  constructor
  · exact concreteAnnulusHLiftGOutputWithFixedInverse_of_hliftFOutputWithFixedInverse hF
  · intro hno
    obtain ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩ := htr hno
    exact ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Uniform fixed-inverse hLiftF plus transcendence from far-domain topology.**
This closes the algebraic obstruction input of
`exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_no_far_high_relation` whenever the
far high-value downstairs set itself satisfies the hypotheses of `bottcher_transcendental_far` for
`c₂`.  The analytic representative on that set is supplied by `bottcherFarBound_spec`. -/
theorem exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_domain
    (c₁ c₂ : ℂ) (hc₂ : (0 : ℂ) ∉ filledJulia c₂) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos ∧
        (∀ S : Set ℂ,
          S = {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖} →
          IsOpen S → IsPreconnected S → S.Nonempty → S.Infinite →
          (∀ z ∈ S, bottcherFarBound c₂ hc₂ < ‖z‖) →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂))) := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_no_far_high_relation c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₁, hall, hψleft, fun d => ?_⟩
  obtain ⟨hF, htr⟩ := hdata d
  constructor
  · exact hF
  · intro S hSdef hSo hSc hSne hSinf hSfar
    have hno : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
        ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0 S := by
      obtain ⟨aS, haS, _htower⟩ := bottcherFarBound_spec c₂ hc₂ S hSo hSc hSne hSinf hSfar
      exact no_eval₂_bottcher_relation_of_bottcher_transcendental_far
        c₂ hc₂ hSo hSc hSne hSinf hSfar haS
    exact htr (by simpa [hSdef] using hno)

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Symmetric fixed-inverse hLiftG plus transcendence from far-domain topology.**
This is the coordinate-reversed form of
`exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_domain`: the fixed inverse
branch is for `c₂`, the concrete datum is `hliftG`, and the far high-value downstairs set is tested
against the far bound for `c₁`. -/
theorem exists_uniform_cover_annulus_hliftG_tower_with_transcendence_of_far_high_domain
    (c₁ c₂ : ℂ) (hc₁ : (0 : ℂ) ∉ filledJulia c₁) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₂ (bottcherCoord c₂ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ (d + 1) d R' hR'pos ∧
        (∀ S : Set ℂ,
          S = {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₂ z‖} →
          IsOpen S → IsPreconnected S → S.Nonempty → S.Infinite →
          (∀ z ∈ S, bottcherFarBound c₁ hc₁ < ‖z‖) →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₁ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁))) := by
  obtain ⟨R, B, R', hR'pos, ψ₂, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_domain c₂ c₁ hc₁
  refine ⟨R, B, R', hR'pos, ψ₂, hall, hψleft, fun d => ?_⟩
  obtain ⟨hF, htr⟩ := hdata d
  constructor
  · exact concreteAnnulusHLiftGOutputWithFixedInverse_of_hliftFOutputWithFixedInverse hF
  · intro S hSdef hSo hSc hSne hSinf hSfar
    obtain ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩ := htr S hSdef hSo hSc hSne hSinf hSfar
    exact ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩

end Bottcher

namespace Bottcher

/-- **The far high-value Böttcher subset is open.**
The exterior condition places the domain inside `escapeOpen c`; on that open exterior,
`bottcherCoord c` is continuous, so the Böttcher-value superlevel condition is open there. -/
theorem isOpen_far_high_bottcher_value {c : ℂ} {R Λ : ℝ}
    (hR : max 2 ‖c‖ < R) :
    IsOpen {z : ℂ | R < ‖z‖ ∧ Λ < ‖bottcherCoord c z‖} := by
  let E : Set ℂ := {z : ℂ | R < ‖z‖}
  have hEopen : IsOpen E := isOpen_lt continuous_const continuous_norm
  have hEsub : E ⊆ escapeOpen c := by
    intro z hz
    exact lt_trans hR hz
  have hcont : ContinuousOn (fun z : ℂ => ‖bottcherCoord c z‖) E :=
    ((analyticOnNhd_bottcherCoord_full c).continuousOn.mono hEsub).norm
  change IsOpen (E ∩ (fun z : ℂ => ‖bottcherCoord c z‖) ⁻¹' Set.Ioi Λ)
  exact hcont.isOpen_inter_preimage hEopen isOpen_Ioi

/-- **Radius-package form of `isOpen_far_high_bottcher_value`.** -/
theorem isOpen_far_high_bottcher_value_of_coverAnnulusRadiusIneqs
    {c₁ c₂ : ℂ} {n : ℕ} {R B R' : ℝ}
    (h : coverAnnulusRadiusIneqs c₁ c₂ n R B R') :
    IsOpen {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ n) < ‖bottcherCoord c₁ z‖} := by
  have hMpos : 0 < max 2 ‖c₁‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hR : max 2 ‖c₁‖ < R := by nlinarith [h.1]
  exact isOpen_far_high_bottcher_value (c := c₁) (R := R) (Λ := R' ^ (2 ^ n)) hR

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **F-side annulus handoff with automatic far-bound and openness.**
The radii are chosen with `R > bottcherFarBound c₂ hc₂`, so the far-bound hypothesis needed by
`bottcher_transcendental_far` follows from membership in the far high-value set.  The open-set
hypothesis is discharged by `isOpen_far_high_bottcher_value_of_coverAnnulusRadiusIneqs`; callers only
supply preconnectedness, nonemptiness, and infinitude of the far high-value set. -/
theorem exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_preconnected
    (c₁ c₂ : ℂ) (hc₂ : (0 : ℂ) ∉ filledJulia c₂) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      bottcherFarBound c₂ hc₂ < R ∧
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos ∧
        (∀ S : Set ℂ,
          S = {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖} →
          IsPreconnected S → S.Nonempty → S.Infinite →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂))) := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hRgt, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image_with_R_gt
      c₁ c₂ (bottcherFarBound c₂ hc₂)
  refine ⟨R, B, R', hR'pos, ψ₁, hRgt, hall, hψleft, fun d => ?_⟩
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  let N : ℕ := 2 ^ (d + 1)
  obtain ⟨hψan, hcont, _hproj, hpInf, _himage⟩ := hdata d
  constructor
  · exact concreteAnnulusHLiftFOutputWithFixedInverse_of_projection_data hpInf hψan hcont rfl
  · intro S hSdef hSc hSne hSinf
    have hSo : IsOpen S := by
      rw [hSdef]
      exact isOpen_far_high_bottcher_value_of_coverAnnulusRadiusIneqs (hall d)
    have hSfar : ∀ z ∈ S, bottcherFarBound c₂ hc₂ < ‖z‖ := by
      intro z hz
      rw [hSdef] at hz
      exact lt_trans hRgt hz.1
    have hnoS : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
        ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0 S := by
      obtain ⟨aS, haS, _htower⟩ := bottcherFarBound_spec c₂ hc₂ S hSo hSc hSne hSinf hSfar
      exact no_eval₂_bottcher_relation_of_bottcher_transcendental_far
        c₂ hc₂ hSo hSc hSne hSinf hSfar haS
    have hno : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
        ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
          {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖} := by
      simpa [hSdef] using hnoS
    obtain ⟨p₀, hp0⟩ := exists_projection_p0 (U := U) (ψ₁ := ψ₁) (n := d + 1) (by
      simpa [U] using hψan)
    obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := d + 1)
      (by simpa [U] using hψan) (by simpa [U] using hcont)
    have hNpos : 0 < N := by
      dsimp [N]
      exact pow_pos (by norm_num : (0 : ℕ) < 2) (d + 1)
    have htr := transcendental_pullback_bottcher_of_no_far_high_relation
      (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (R := R) (R' := R') (N := N)
      hR'pos hNpos hψleft (p₀ := p₀) (a := a₂) hp0
      (by simpa [U, N] using hpInf) (by simpa [U, N] using ha₂)
      (by simpa [N] using hno)
    refine ⟨by simpa [U] using p₀, by simpa [U, N] using hp0,
      by simpa [U, N] using hpInf, by simpa [U] using a₂,
      by simpa [U, N] using ha₂, ?_⟩
    simpa [U, N] using htr

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **G-side annulus handoff with automatic far-bound and openness.**
The symmetric form of
`exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_preconnected`. -/
theorem exists_uniform_cover_annulus_hliftG_tower_with_transcendence_of_far_high_preconnected
    (c₁ c₂ : ℂ) (hc₁ : (0 : ℂ) ∉ filledJulia c₁) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      bottcherFarBound c₁ hc₁ < R ∧
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₂ (bottcherCoord c₂ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ (d + 1) d R' hR'pos ∧
        (∀ S : Set ℂ,
          S = {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₂ z‖} →
          IsPreconnected S → S.Nonempty → S.Infinite →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₁ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁))) := by
  obtain ⟨R, B, R', hR'pos, ψ₂, hRgt, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_preconnected c₂ c₁ hc₁
  refine ⟨R, B, R', hR'pos, ψ₂, hRgt, hall, hψleft, fun d => ?_⟩
  obtain ⟨hF, htr⟩ := hdata d
  constructor
  · exact concreteAnnulusHLiftGOutputWithFixedInverse_of_hliftFOutputWithFixedInverse hF
  · intro S hSdef hSc hSne hSinf
    obtain ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩ := htr S hSdef hSc hSne hSinf
    exact ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **F-side annulus handoff with only preconnectedness left as topology.**
The far high-value set is automatically open, nonempty, infinite, and beyond the `c₂` far bound by the
preceding radius and real-ray lemmas.  The only remaining topological input is preconnectedness. -/
theorem exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_preconnected_only
    (c₁ c₂ : ℂ) (hc₂ : (0 : ℂ) ∉ filledJulia c₂) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      bottcherFarBound c₂ hc₂ < R ∧
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos ∧
        (∀ S : Set ℂ,
          S = {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖} →
          IsPreconnected S →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂))) := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hRgt, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_preconnected c₁ c₂ hc₂
  refine ⟨R, B, R', hR'pos, ψ₁, hRgt, hall, hψleft, fun d => ?_⟩
  obtain ⟨hF, htr⟩ := hdata d
  constructor
  · exact hF
  · intro S hSdef hSc
    have hSne : S.Nonempty := by
      simpa [hSdef] using far_high_bottcher_value_nonempty c₁ R (R' ^ (2 ^ (d + 1)))
    have hSinf : S.Infinite := by
      simpa [hSdef] using far_high_bottcher_value_infinite c₁ R (R' ^ (2 ^ (d + 1)))
    exact htr S hSdef hSc hSne hSinf

/-- **G-side annulus handoff with only preconnectedness left as topology.** -/
theorem exists_uniform_cover_annulus_hliftG_tower_with_transcendence_of_far_high_preconnected_only
    (c₁ c₂ : ℂ) (hc₁ : (0 : ℂ) ∉ filledJulia c₁) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      bottcherFarBound c₁ hc₁ < R ∧
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₂ (bottcherCoord c₂ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ (d + 1) d R' hR'pos ∧
        (∀ S : Set ℂ,
          S = {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₂ z‖} →
          IsPreconnected S →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₁ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁))) := by
  obtain ⟨R, B, R', hR'pos, ψ₂, hRgt, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high_preconnected_only c₂ c₁ hc₁
  refine ⟨R, B, R', hR'pos, ψ₂, hRgt, hall, hψleft, fun d => ?_⟩
  obtain ⟨hF, htr⟩ := hdata d
  constructor
  · exact concreteAnnulusHLiftGOutputWithFixedInverse_of_hliftFOutputWithFixedInverse hF
  · intro S hSdef hSc
    obtain ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩ := htr S hSdef hSc
    exact ⟨p₀, hp0, hpInf, a₁, ha₁, htrans⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **F-side annulus handoff with all far high-value topology discharged.**
The fixed inverse makes the far high-value Böttcher set preconnected as the image of an exterior;
nonemptiness and infinitude come from the real ray, and openness/far-bound membership come from the
radius package. -/
theorem exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high
    (c₁ c₂ : ℂ) (hc₂ : (0 : ℂ) ∉ filledJulia c₂) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      bottcherFarBound c₂ hc₂ < R ∧
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos ∧
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)) := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hRgt, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image_with_R_gt
      c₁ c₂ (bottcherFarBound c₂ hc₂)
  refine ⟨R, B, R', hR'pos, ψ₁, hRgt, hall, hψleft, fun d => ?_⟩
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  let S : Set ℂ := {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖}
  let N : ℕ := 2 ^ (d + 1)
  obtain ⟨hψan, hcont, _hproj, hpInf, _himage⟩ := hdata d
  have hF : concreteAnnulusHLiftFOutputWithFixedInverse c₂ ψ₁ (d + 1) d R' hR'pos :=
    concreteAnnulusHLiftFOutputWithFixedInverse_of_projection_data hpInf hψan hcont rfl
  have hSc : IsPreconnected S := by
    dsimp [S]
    exact isPreconnected_far_high_bottcher_value_of_coverAnnulusRadiusIneqs
      (h := hall d) hψleft hψan
  have hSne : S.Nonempty := by
    dsimp [S]
    exact far_high_bottcher_value_nonempty c₁ R (R' ^ (2 ^ (d + 1)))
  have hSinf : S.Infinite := by
    dsimp [S]
    exact far_high_bottcher_value_infinite c₁ R (R' ^ (2 ^ (d + 1)))
  have hSo : IsOpen S := by
    dsimp [S]
    exact isOpen_far_high_bottcher_value_of_coverAnnulusRadiusIneqs (hall d)
  have hSfar : ∀ z ∈ S, bottcherFarBound c₂ hc₂ < ‖z‖ := by
    intro z hz
    exact lt_trans hRgt hz.1
  have hnoS : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0 S := by
    obtain ⟨aS, haS, _htower⟩ := bottcherFarBound_spec c₂ hc₂ S hSo hSc hSne hSinf hSfar
    exact no_eval₂_bottcher_relation_of_bottcher_transcendental_far
      c₂ hc₂ hSo hSc hSne hSinf hSfar haS
  have hno : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
        {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖} := by
    simpa [S] using hnoS
  obtain ⟨p₀, hp0⟩ := exists_projection_p0 (U := U) (ψ₁ := ψ₁) (n := d + 1) (by
    simpa [U] using hψan)
  obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := d + 1)
    (by simpa [U] using hψan) (by simpa [U] using hcont)
  have hNpos : 0 < N := by
    dsimp [N]
    exact pow_pos (by norm_num : (0 : ℕ) < 2) (d + 1)
  have htr := transcendental_pullback_bottcher_of_no_far_high_relation
    (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (R := R) (R' := R') (N := N)
    hR'pos hNpos hψleft (p₀ := p₀) (a := a₂) hp0
    (by simpa [U, N] using hpInf) (by simpa [U, N] using ha₂)
    (by simpa [N] using hno)
  refine ⟨hF, by simpa [U] using p₀, by simpa [U, N] using hp0,
    by simpa [U, N] using hpInf, by simpa [U] using a₂,
    by simpa [U, N] using ha₂, ?_⟩
  simpa [U, N] using htr

/-- **G-side annulus handoff with all far high-value topology discharged.** -/
theorem exists_uniform_cover_annulus_hliftG_tower_with_transcendence_of_far_high
    (c₁ c₂ : ℂ) (hc₁ : (0 : ℂ) ∉ filledJulia c₁) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₂ : ℂ → ℂ),
      bottcherFarBound c₁ hc₁ < R ∧
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₂ c₁ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₂ (bottcherCoord c₂ z) = z) ∧
      ∀ d : ℕ,
        concreteAnnulusHLiftGOutputWithFixedInverse c₁ ψ₂ (d + 1) d R' hR'pos ∧
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₂ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₁ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₁ (ψ₂ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁)) := by
  obtain ⟨R, B, R', hR'pos, ψ₂, hRgt, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_hliftF_tower_with_transcendence_of_far_high c₂ c₁ hc₁
  refine ⟨R, B, R', hR'pos, ψ₂, hRgt, hall, hψleft, fun d => ?_⟩
  obtain ⟨hF, p₀, hp0, hpInf, a₁, ha₁, htrans⟩ := hdata d
  exact ⟨concreteAnnulusHLiftGOutputWithFixedInverse_of_hliftFOutputWithFixedInverse hF,
    p₀, hp0, hpInf, a₁, ha₁, htrans⟩

end Bottcher
