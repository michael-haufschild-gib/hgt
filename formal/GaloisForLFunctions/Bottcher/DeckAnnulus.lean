/-
# The hDisc deck on a value annulus — collapsing the uniformization to the identity

`DeckBiholo.monoF_step_of_uniformization` reduces the disconnected lift step `hliftF` (at one depth) to
a `LiftUniformization U V φ ψ` (a biholomorphism of the cover onto a value region) together with a
**rotation-invariant** second coordinate `a₂ = b₂∘φ`.  This file removes the need to construct any
nontrivial cover Riemann surface: realize the cover `U` DIRECTLY in value space as a rotation-invariant
annulus, with `φ = ψ = id`, so the deck is literal multiplication `×ζ₀`.

Then the `hliftF` step at depth `n` (root order `2ⁿ`) needs only:
* `a₁ = ξ` (the identity germ on `U`) — the scaling coordinate, `a₁∘(×ζ₀) = ζ₀·a₁`;
* `a₂ = b₂` with `b₂` a **function of `ξ^{2ⁿ}`** — automatically rotation-invariant under any `ζ₀` with
  `ζ₀^{2ⁿ} = 1` (`pow_comp_rotation_invariant`), since `(ζ₀·ξ)^{2ⁿ} = ξ^{2ⁿ}`.

The genuine analytic content that remains is exactly: realize the second Böttcher coordinate as such a
function of `ξ^{2ⁿ}` — i.e. `a₂(ξ) = φ_{c₂}(z(ξ^{2ⁿ}))` where `z(w) = φ_{c₁}^{-1}(w)` is the inverse
Böttcher of `c₁` (so `ξ` is the `2ⁿ`-th root of `φ_{c₁}` on the cover, and the base point `z = ξ^{2ⁿ}`
read through `φ_{c₁}^{-1}` is deck-invariant).  That is built on top of the far-field inverse Böttcher.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.DeckBiholo
import GaloisForLFunctions.Bottcher.BottcherCoord

open Filter Topology Set

namespace Bottcher

/-- **The identity uniformization.**  `U ≅ U` via `φ = ψ = id`: the cover is realized directly in value
space, so the deck becomes the literal value-rotation `×ζ₀`.  The trivial biholomorphism that turns the
abstract uniformization datum of `monoF_step_of_uniformization` into "the cover IS a value annulus". -/
theorem liftUniformization_id (U : Set ℂ) : LiftUniformization U U id id where
  hφ := analyticOnNhd_id
  hψ := analyticOnNhd_id
  hφmaps := Set.mapsTo_id U
  hψmaps := Set.mapsTo_id U
  hψφ := by intro w _; rfl
  hφψ := by intro w _; rfl

/-- **A function of `ξ^N` is invariant under rotation by an `N`-th root of unity.**  If `ζ₀^N = 1`
then `b₂(ξ) = h(ξ^N)` satisfies `b₂(ζ₀·ξ) = b₂(ξ)`: `(ζ₀·ξ)^N = ζ₀^N·ξ^N = ξ^N`.  This is the engine
making the deck FIX `φ_{c₂}` automatically — `φ_{c₂}` enters the cover only through the deck-invariant
`ξ^{2ⁿ}`, so the dyadic deck (which permutes the `2ⁿ`-th roots `ξ`) cannot move it. -/
theorem pow_comp_rotation_invariant {h : ℂ → ℂ} {ζ₀ : ℂ} {N : ℕ} (hζ : ζ₀ ^ N = 1) (U : Set ℂ) :
    ∀ y ∈ U, (fun ξ => h (ξ ^ N)) (rotation ζ₀ y) = (fun ξ => h (ξ ^ N)) y := by
  intro y _
  simp only [rotation, mul_pow, hζ, one_mul]

/-- **The rotation `×ζ₀` self-maps a modulus annulus when `‖ζ₀‖ = 1`.**  For `U = {ξ | a < ‖ξ‖ ∧ ‖ξ‖ < b}`
(or any set defined by modulus bounds), multiplication by a unit-modulus `ζ₀` preserves `‖ξ‖`, hence
maps `U → U`.  The deck stays on the cover annulus. -/
theorem mapsTo_rotation_normAnnulus {ζ₀ : ℂ} (hζ : ‖ζ₀‖ = 1) {a b : ℝ} :
    Set.MapsTo (rotation ζ₀) {ξ : ℂ | a < ‖ξ‖ ∧ ‖ξ‖ < b} {ξ : ℂ | a < ‖ξ‖ ∧ ‖ξ‖ < b} := by
  intro ξ hξ
  simp only [rotation, Set.mem_setOf_eq, norm_mul, hζ, one_mul]
  exact hξ

/-- **monoF step from a rotation-invariant second coordinate (identity uniformization).**  The fully
specialized form: the cover `U` is a value annulus, the deck is `×ζ₀`, `a₁` is the identity germ `ξ`,
and `a₂ = b₂` need only be rotation-invariant.  Produces the `monoF`/`hliftF` existential at depth `d`:
a `K`-algebra automorphism `σ` of `meroField U` with `σ a₂ = a₂`, `σ ζ = ζ`, `σ a₁ = ζ·a₁`,
`orderOf ζ > d`.  The deck-fixing of `a₂` and the base field `K` are the rotation-invariance `hbfix`
and `hK`; the scaling of `a₁` is automatic (`a₁ = ξ`). -/
theorem monoF_step_trivial {U : Set ℂ} {b₂ : ℂ → ℂ} {ζ₀ : ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (hrot : Set.MapsTo (rotation ζ₀) U U) (hrot' : Set.MapsTo (rotation ζ₀⁻¹) U U)
    (hζ0 : ζ₀ ≠ 0) (d : ℕ) (hord : d < orderOf ζ₀)
    (hbfix : ∀ y ∈ U, b₂ (rotation ζ₀ y) = b₂ y)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(id : ℂ → ℂ)) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑b₂)
    (hK : ∀ k : K, precompMeroEquiv
        (analyticOnNhd_deckRot (liftUniformization_id U) hrot)
        (analyticOnNhd_deckRot (liftUniformization_id U) hrot')
        (mapsTo_deckRot (liftUniformization_id U) hrot)
        (mapsTo_deckRot (liftUniformization_id U) hrot')
        (eqOn_deckRot_comp hζ0 (liftUniformization_id U) hrot')
        (eqOn_deckRot_comp' hζ0 (liftUniformization_id U) hrot)
        hUo hUc hUne (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₂)
        = algebraMap (analyticSubring U) (meroField U) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₁)
        = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  have ha₂' : (a₂ : Germ (𝓟 U) ℂ) = ↑(b₂ ∘ (id : ℂ → ℂ)) := by rw [ha₂]; rfl
  exact monoF_step_of_uniformization hUo hUc hUne (liftUniformization_id U)
    hrot hrot' hζ0 d hord hbfix a₁ a₂ ha₁ ha₂' hK

/-- **The genuine second coordinate `a₂(ξ) = φ_{c₂}(ψ₁(ξ^{2ⁿ}))` as an analytic germ on the cover.**
With `ψ₁ = φ_{c₁}^{-1}` (the inverse Böttcher of `c₁` on its far value field, `FarFieldUnivalence`),
`ξ` plays the rôle of the `2ⁿ`-th root of `φ_{c₁}` on the cover (so `ξ^{2ⁿ} = φ_{c₁}` and the base point
is `z = ψ₁(ξ^{2ⁿ})`), and `a₂` is the genuine `φ_{c₂}` read at that base point.  It is analytic on `U`
wherever `ψ₁` is analytic at `ξ^{2ⁿ}` and the base point lands in `φ_{c₂}`'s domain
(`ψ₁(ξ^{2ⁿ}) ∈ escapeOpen c₂` — the far-field overlap of the two parameters, an explicit analytic
side-condition).  These two hypotheses are exactly the inverse-Böttcher analyticity and the
two-parameter far-field containment that the concrete cover supplies. -/
theorem exists_rotInvariant_a2 {c₂ : ℂ} {U : Set ℂ} {ψ₁ : ℂ → ℂ} {n : ℕ}
    (hψan : ∀ ξ ∈ U, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ U, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂) :
    ∃ a₂ : analyticSubring U,
      (a₂ : Germ (𝓟 U) ℂ) = ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) := by
  set pw : ℂ → ℂ := fun ξ => ξ ^ (2 ^ n) with hpw
  set F : ℂ → ℂ := fun ξ => bottcherCoord c₂ (ψ₁ (pw ξ)) with hF
  have han : AnalyticOnNhd ℂ F U := by
    intro ξ hξ
    have h1 : AnalyticAt ℂ pw ξ := analyticAt_id.pow (2 ^ n)
    have h2 : AnalyticAt ℂ ψ₁ (pw ξ) := hψan ξ hξ
    have h3 : AnalyticAt ℂ (bottcherCoord c₂) (ψ₁ (pw ξ)) :=
      ((differentiableOn_bottcherCoord c₂).analyticOnNhd (isOpen_escapeOpen c₂)) _ (hcont ξ hξ)
    have h32 : AnalyticAt ℂ (fun w => bottcherCoord c₂ (ψ₁ w)) (pw ξ) := h3.comp h2
    exact h32.comp h1
  exact ⟨⟨(↑F : Germ (𝓟 U) ℂ), F, han, rfl⟩, rfl⟩

/-- **`a₂` is fixed by the deck.**  `a₂(ξ) = φ_{c₂}(ψ₁(ξ^{2ⁿ}))` depends on `ξ` only through the
deck-invariant `ξ^{2ⁿ}`, so rotation by any `2ⁿ`-th root of unity `ζ₀` fixes it
(`pow_comp_rotation_invariant`).  This is the clause `hbfix` of `monoF_step_trivial` — the
"deck fixes `φ_{c₂}`" step, now AUTOMATIC: `φ_{c₂}` enters the cover only through `φ_{c₁}`'s
`2ⁿ`-th power, which the dyadic deck (permuting the `2ⁿ`-th roots) cannot move. -/
theorem a2_rotation_invariant {c₂ : ℂ} {U : Set ℂ} {ψ₁ : ℂ → ℂ} {ζ₀ : ℂ} {n : ℕ}
    (hζ : ζ₀ ^ (2 ^ n) = 1) :
    ∀ y ∈ U, (fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) (rotation ζ₀ y)
      = (fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) y :=
  pow_comp_rotation_invariant (h := fun w => bottcherCoord c₂ (ψ₁ w)) hζ U

/-- **Per-depth `hliftF` step from the inverse-Böttcher data (live deck route, fully assembled).**
Combining `exists_rotInvariant_a2` (the genuine `φ_{c₂}` germ `a₂`), `a2_rotation_invariant` (the deck
fixes it), and `monoF_step_trivial` (the `×ζ₀` deck on the value annulus): from a rotation-invariant
cover annulus `U`, a dyadic root `ζ₀` (`orderOf ζ₀ > d`, `ζ₀^{2ⁿ} = 1`), the inverse Böttcher `ψ₁` with
its analyticity + the two-parameter far-field containment, the identity germ `a₁ = ξ`, and the base
`ℂ(z)`-fixing `hK`, this produces the genuine second coordinate `a₂(ξ) = φ_{c₂}(ψ₁(ξ^{2ⁿ}))` together
with the per-depth `monoF`/`hliftF` `σ`-data: a `K`-algebra automorphism `σ` of `meroField U` scaling
`a₁` by `ζ` (order `> d`), fixing `a₂` and `ζ`.  This is EXACTLY the per-depth tuple that `q62`'s
`hDisc` consumes (with `a₁ = φ_{c₁}^{1/2ⁿ}`, so `noRelation_pow` lifts `NoRelation(a₁,a₂)` to
`NoRelation(φ_{c₁}, φ_{c₂})` since `a₁^{2ⁿ} = φ_{c₁}`).  The sole remaining inputs are now isolated:
the annulus `U` + `ψ₁` analyticity + containment (the far-field estimates) and the base-fixing `hK`. -/
theorem monoF_step_from_inverse {c₂ : ℂ} {U : Set ℂ} {ψ₁ : ℂ → ℂ} {ζ₀ : ℂ} {n : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (hrot : Set.MapsTo (rotation ζ₀) U U) (hrot' : Set.MapsTo (rotation ζ₀⁻¹) U U)
    (hζ0 : ζ₀ ≠ 0) (hζpow : ζ₀ ^ (2 ^ n) = 1) (d : ℕ) (hord : d < orderOf ζ₀)
    (hψan : ∀ ξ ∈ U, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ U, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂)
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
      (a₂ : Germ (𝓟 U) ℂ) = ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₂)
        = algebraMap (analyticSubring U) (meroField U) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₁)
        = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := n) hψan hcont
  have hbfix : ∀ y ∈ U, (fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) (rotation ζ₀ y)
      = (fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) y := a2_rotation_invariant hζpow
  obtain ⟨σ, ζ, m, hm, hord', hfix, hζfix, hscale⟩ :=
    monoF_step_trivial (b₂ := fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n))))
      hUo hUc hUne hrot hrot' hζ0 d hord hbfix a₁ a₂ ha₁ ha₂ hK
  exact ⟨a₂, σ, ζ, m, ha₂, hm, hord', hfix, hζfix, hscale⟩

end Bottcher
