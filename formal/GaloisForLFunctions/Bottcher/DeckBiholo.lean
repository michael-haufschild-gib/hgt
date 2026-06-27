/-
# Deck self-biholomorphism from the cover uniformization (the hDisc deck brick)

The disconnected-case lift data `hliftF` (Q62Assembly) needs, at every depth, a self-
biholomorphism `g` of the planar cover carrier `U` under which the Böttcher lift germ `φ̃c`
scales by a root of unity while the base coordinate `z` and the other coordinate `φ_{c₂}` are
fixed.  `CoverConstruction.deck_scaling_of_invertible_lift` extracts only the *scaling*
`φ ∘ g = ζ · φ` from a section of the lift; it does NOT produce the full self-biholomorphism
datum (`g, g'` analytic, `MapsTo g U U`, mutually-inverse `EqOn`) that `monoF_witness` / `hliftF`
actually consume.

This file supplies that missing link.  From a **global biholomorphism** `φ : U ≃ V` of the cover
onto a value region `V` (with inverse `ψ`), and the value-rotation `ρ = ×ζ` (a self-map of the
annular `V`), the conjugated map `g = ψ ∘ ρ ∘ φ` is an honest self-biholomorphism of `U`:

* `g`, `g' = ψ ∘ ρ⁻¹ ∘ φ` are analytic on `U`;
* `g, g'` map `U → U`;
* `g ∘ g' = g' ∘ g = id` on `U`;
* `g` scales the lift germ `↑φ` by `ζ`  (`hscale`);
* `g` fixes every germ `↑(b ∘ φ)` pulled back from a `ρ`-invariant `b` on `V`  (`hinv`, the base
  `z` and the second coordinate `φ_{c₂}`).

Composed with the verified field machinery (`monoF_witness`), this collapses the entire `hliftF`
step at one depth to the single analytic input: the uniformization `φ : U ≃ V`.  No abstract
Riemann-surface gluing is taken on faith here — the deck is built, axiom-clean, from the section.
-/
import GaloisForLFunctions.Bottcher.Q62Assembly

open Filter Topology Set

namespace Bottcher

/-- **Cover uniformization datum.** A global biholomorphism `φ : U ≃ V` with inverse `ψ`:
`φ, ψ` analytic, mapping `U → V` and `V → U` respectively, and mutually inverse on each side.
This is the genuine analytic input of the disconnected case — the connected dyadic cover `U` is
biholomorphic, via the Böttcher lift `φ̃c = φ`, onto the value region `V` (a norm-annulus). -/
structure LiftUniformization (U V : Set ℂ) (φ ψ : ℂ → ℂ) : Prop where
  hφ : AnalyticOnNhd ℂ φ U
  hψ : AnalyticOnNhd ℂ ψ V
  hφmaps : Set.MapsTo φ U V
  hψmaps : Set.MapsTo ψ V U
  hψφ : Set.EqOn (ψ ∘ φ) id U
  hφψ : Set.EqOn (φ ∘ ψ) id V

/-- The deck self-map conjugated through the uniformization: `g = ψ ∘ (×ζ) ∘ φ`.  On the cover
`U` it realizes the value-rotation `w ↦ ζ·w` of `V` — the sheet permutation of the dyadic deck. -/
def deckRot (ψ φ : ℂ → ℂ) (ζ : ℂ) : ℂ → ℂ := ψ ∘ rotation ζ ∘ φ

/-- **The deck map is analytic on `U`.**  Composition of the analytic `φ : U → V`, the entire
rotation `ρ = ×ζ : V → V`, and the analytic inverse `ψ : V → U`. -/
theorem analyticOnNhd_deckRot {U V : Set ℂ} {φ ψ : ℂ → ℂ} {ζ : ℂ}
    (H : LiftUniformization U V φ ψ) (hrot : Set.MapsTo (rotation ζ) V V) :
    AnalyticOnNhd ℂ (deckRot ψ φ ζ) U :=
  H.hψ.comp ((analyticOnNhd_rotation ζ V).comp H.hφ H.hφmaps) (hrot.comp H.hφmaps)

/-- **The deck map sends `U` into `U`.**  `φ : U → V`, `ρ : V → V`, `ψ : V → U`. -/
theorem mapsTo_deckRot {U V : Set ℂ} {φ ψ : ℂ → ℂ} {ζ : ℂ}
    (H : LiftUniformization U V φ ψ) (hrot : Set.MapsTo (rotation ζ) V V) :
    Set.MapsTo (deckRot ψ φ ζ) U U :=
  H.hψmaps.comp (hrot.comp H.hφmaps)

/-- **`deckRot ζ ∘ deckRot ζ⁻¹ = id` on `U`.**  The two deck maps for inverse rotations are
mutually inverse: pushing through `φ`, the rotations cancel (`ζ · ζ⁻¹ = 1`), and `ψ` undoes `φ`. -/
theorem eqOn_deckRot_comp {U V : Set ℂ} {φ ψ : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (H : LiftUniformization U V φ ψ) (hrot' : Set.MapsTo (rotation ζ⁻¹) V V) :
    Set.EqOn (deckRot ψ φ ζ ∘ deckRot ψ φ ζ⁻¹) id U := by
  intro w hw
  have hv : rotation ζ⁻¹ (φ w) ∈ V := hrot' (H.hφmaps hw)
  have e1 : φ (ψ (rotation ζ⁻¹ (φ w))) = rotation ζ⁻¹ (φ w) := H.hφψ hv
  have e2 : ψ (φ w) = w := H.hψφ hw
  simp only [deckRot, rotation, Function.comp_apply, id_eq] at e1 e2 ⊢
  rw [e1, mul_inv_cancel_left₀ hζ, e2]

/-- **`deckRot ζ⁻¹ ∘ deckRot ζ = id` on `U`** — the reverse composition. -/
theorem eqOn_deckRot_comp' {U V : Set ℂ} {φ ψ : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (H : LiftUniformization U V φ ψ) (hrot : Set.MapsTo (rotation ζ) V V) :
    Set.EqOn (deckRot ψ φ ζ⁻¹ ∘ deckRot ψ φ ζ) id U := by
  intro w hw
  have hv : rotation ζ (φ w) ∈ V := hrot (H.hφmaps hw)
  have e1 : φ (ψ (rotation ζ (φ w))) = rotation ζ (φ w) := H.hφψ hv
  have e2 : ψ (φ w) = w := H.hψφ hw
  simp only [deckRot, rotation, Function.comp_apply, id_eq] at e1 e2 ⊢
  rw [e1, inv_mul_cancel_left₀ hζ, e2]

/-- **The deck scales the lift coordinate by `ζ`:** `φ (deckRot ζ w) = ζ · φ w` on `U`.  This is
the genuine `φ̃c ∘ g = ζ · φ̃c` monodromy multiplier, realized by the conjugated value-rotation. -/
theorem deckRot_lift_scale {U V : Set ℂ} {φ ψ : ℂ → ℂ} {ζ : ℂ}
    (H : LiftUniformization U V φ ψ) (hrot : Set.MapsTo (rotation ζ) V V) :
    ∀ w ∈ U, φ (deckRot ψ φ ζ w) = ζ * φ w := by
  intro w hw
  have hv : rotation ζ (φ w) ∈ V := hrot (H.hφmaps hw)
  have e1 : φ (ψ (rotation ζ (φ w))) = rotation ζ (φ w) := H.hφψ hv
  simp only [deckRot, rotation, Function.comp_apply] at e1 ⊢
  exact e1

/-- **The deck fixes every base-pulled-back coordinate:** if `b` is invariant under the value-
rotation on `V` (`b (ρ y) = b y`), then `(b ∘ φ) (deckRot ζ w) = (b ∘ φ) w` on `U`.  The base
coordinate `z` and the second Böttcher coordinate `φ_{c₂}` are both of this form (functions of the
deck-invariant base `φ̃c^{2ⁿ}`), hence fixed by the deck. -/
theorem deckRot_base_fix {U V : Set ℂ} {φ ψ b : ℂ → ℂ} {ζ : ℂ}
    (H : LiftUniformization U V φ ψ) (hrot : Set.MapsTo (rotation ζ) V V)
    (hb : ∀ y ∈ V, b (rotation ζ y) = b y) :
    ∀ w ∈ U, (b ∘ φ) (deckRot ψ φ ζ w) = (b ∘ φ) w := by
  intro w hw
  have hscale : φ (deckRot ψ φ ζ w) = ζ * φ w := deckRot_lift_scale H hrot w hw
  have hbφ : b (rotation ζ (φ w)) = b (φ w) := hb (φ w) (H.hφmaps hw)
  simp only [Function.comp_apply, hscale]
  simpa only [rotation] using hbφ

/-- **Germ-level deck scaling.**  Lifts `deckRot_lift_scale` to the carrier germ identity that
`monoF_witness`/`hliftF` consume: `(↑φ) ∘ g = ζ · (↑φ)` in `Germ (𝓟 U) ℂ`. -/
theorem deckRot_germ_scale {U V : Set ℂ} {φ ψ : ℂ → ℂ} {ζ : ℂ}
    (H : LiftUniformization U V φ ψ) (hrot : Set.MapsTo (rotation ζ) V V)
    (hgmaps : Set.MapsTo (deckRot ψ φ ζ) U U) :
    (↑φ : Germ (𝓟 U) ℂ).compTendsto (deckRot ψ φ ζ) (tendsto_principal_principal.mpr hgmaps)
      = (↑(fun _ : ℂ => ζ) : Germ (𝓟 U) ℂ) * (↑φ : Germ (𝓟 U) ℂ) :=
  germ_scaling_of_function_scaling hgmaps (deckRot_lift_scale H hrot)

/-- **Germ-level deck fixing.**  Lifts `deckRot_base_fix` to the carrier germ identity:
`(↑(b ∘ φ)) ∘ g = ↑(b ∘ φ)` in `Germ (𝓟 U) ℂ`. -/
theorem deckRot_germ_fix {U V : Set ℂ} {φ ψ b : ℂ → ℂ} {ζ : ℂ}
    (H : LiftUniformization U V φ ψ) (hrot : Set.MapsTo (rotation ζ) V V)
    (hb : ∀ y ∈ V, b (rotation ζ y) = b y)
    (hgmaps : Set.MapsTo (deckRot ψ φ ζ) U U) :
    (↑(b ∘ φ) : Germ (𝓟 U) ℂ).compTendsto (deckRot ψ φ ζ) (tendsto_principal_principal.mpr hgmaps)
      = (↑(b ∘ φ) : Germ (𝓟 U) ℂ) := by
  rw [Germ.coe_compTendsto]
  exact Germ.coe_eq.mpr
    (Filter.eventually_principal.mpr (fun w hw => deckRot_base_fix H hrot hb w hw))

/-- **The full `monoF` step, reduced to the uniformization.**  Capstone of this file: for the
genuine carrier `M = meroField U`, the lift coordinate `a₁` (with germ `↑φ`) and a base-pulled-back
coordinate `a₂` (with germ `↑(b₂ ∘ φ)`, `b₂` rotation-invariant), the uniformization `φ : U ≃ V`
plus a root `ζ₀` of order `> d` whose rotation self-maps `V` produces exactly the existential
`q62_disconnected_both`'s `monoF` requires at depth `d`: a `K`-algebra automorphism `σ` of
`meroField U` with `σ a₂ = a₂`, `σ ζ = ζ`, `σ a₁ = ζ · a₁` and `orderOf ζ = m > d`.

The deck `σ` is `precompMeroAlgEquiv` along the self-biholomorphism `g = ψ ∘ (×ζ₀) ∘ φ` built here;
its scaling/fixing data are `deckRot_germ_scale`/`deckRot_germ_fix`.  Everything is machine-checked
and axiom-clean — the sole analytic input is the bundled uniformization `H`. -/
theorem monoF_step_of_uniformization {U V : Set ℂ} {φ ψ b₂ : ℂ → ℂ} {ζ₀ : ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (H : LiftUniformization U V φ ψ)
    (hrot : Set.MapsTo (rotation ζ₀) V V) (hrot' : Set.MapsTo (rotation ζ₀⁻¹) V V)
    (hζ0 : ζ₀ ≠ 0) (d : ℕ) (hord : d < orderOf ζ₀)
    (hbfix : ∀ y ∈ V, b₂ (rotation ζ₀ y) = b₂ y)
    (a₁ a₂ : analyticSubring U)
    (ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑φ) (ha₂ : (a₂ : Germ (𝓟 U) ℂ) = ↑(b₂ ∘ φ))
    (hK : ∀ k : K, precompMeroEquiv (analyticOnNhd_deckRot H hrot) (analyticOnNhd_deckRot H hrot')
        (mapsTo_deckRot H hrot) (mapsTo_deckRot H hrot')
        (eqOn_deckRot_comp hζ0 H hrot') (eqOn_deckRot_comp' hζ0 H hrot)
        hUo hUc hUne (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₂)
        = algebraMap (analyticSubring U) (meroField U) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₁)
        = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine monoF_witness hUo hUc hUne a₁ a₂ d ζ₀
    (analyticOnNhd_deckRot H hrot) (analyticOnNhd_deckRot H hrot')
    (mapsTo_deckRot H hrot) (mapsTo_deckRot H hrot')
    (eqOn_deckRot_comp hζ0 H hrot') (eqOn_deckRot_comp' hζ0 H hrot)
    hord ?_ ?_ hK
  · rw [ha₁]
    exact deckRot_germ_scale H hrot (mapsTo_deckRot H hrot)
  · rw [ha₂]
    exact deckRot_germ_fix H hrot hbfix (mapsTo_deckRot H hrot)

end Bottcher
