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
  simpa using precompMeroEquiv_ratfuncToMeroVia_fix hg hg' hmaps hmaps' hgg' hg'g
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
  simpa using precompMeroEquiv_ratfuncToMeroVia_fix hg hg' hmaps hmaps' hgg' hg'g
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
