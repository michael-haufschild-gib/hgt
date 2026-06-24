/-
# Böttcher tower — the monodromy torsor from the `npow` covering (GAP B foundation)

The dyadic monodromy of `φ_c` is realized through the covering `w ↦ w^(2ⁿ)` of `ℂˣ`, to
which `bottcherCoord_iterate` conjugates `f_c^[n]`. Mathlib already provides this covering as
a **quotient covering** (`Complex.isQuotientCoveringMap_npow`): its structure group is the
`n`-th roots of unity `(powMonoidHom n).ker ≤ ℂˣ`, acting by multiplication, and its defining
property is

  `w₁^n = w₂^n  ↔  w₁ ∈ orbit (μ_n) w₂`    (`apply_eq_iff_mem_orbit`).

That is the **monodromy torsor**: the fibre over a base value is a single `μ_n`-orbit, so the
deck group `μ_n` acts simply transitively on branches. Multiplication by a kernel element is a
deck transformation (preserves the `n`-th power). These are the pieces the germ-field
automorphism `σ_n` of `DyadicMonodromyTower` is assembled from: pulling the deck multiplier
`w ↦ ζ·w` (ζ ∈ μ_{2ⁿ}) back through `φ_c` fixes `z` (hence `K = ℂ(z)`) and scales `φ_{c₁}`.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.Analysis.Complex.CoveringMap

open Complex

namespace Bottcher

/-- The `n`-th roots of unity inside `ℂˣ` — the deck (structure) group of the covering
`w ↦ wⁿ`, abbreviated for use as the dyadic monodromy multiplier group at `n = 2ᵏ`. -/
abbrev dyadicDeck (n : ℕ) : Subgroup ℂˣ := (@powMonoidHom ℂˣ _ n).ker

/-- A deck-group element is an `n`-th root of unity. -/
theorem dyadicDeck_pow {n : ℕ} (ζ : dyadicDeck n) : (ζ : ℂˣ) ^ n = 1 := by
  have h := ζ.2
  rwa [MonoidHom.mem_ker, powMonoidHom_apply] at h

/-- **Deck transformation.** Left multiplication by a deck-group element preserves the `n`-th
power map `w ↦ wⁿ` — it permutes each fibre, i.e. it is a deck transformation of the covering. -/
theorem deck_mul_npow {n : ℕ} (ζ : dyadicDeck n) (w : ℂˣ) : ((ζ : ℂˣ) * w) ^ n = w ^ n := by
  rw [mul_pow, dyadicDeck_pow ζ, one_mul]

/-- **The monodromy torsor.** Two units have the same `n`-th power iff they differ by an `n`-th
root of unity. The fibre of `w ↦ wⁿ` over a base value is exactly one `μ_n`-orbit; the deck
group `μ_n` acts simply transitively on the branches. This is the covering-theoretic core of
the dyadic monodromy: it is `Complex.isQuotientCoveringMap_npow`'s `apply_eq_iff_mem_orbit`. -/
theorem npow_eq_iff_mem_dyadicOrbit (n : ℕ) [NeZero n] (w₁ w₂ : ℂˣ) :
    w₁ ^ n = w₂ ^ n ↔ w₁ ∈ MulAction.orbit (dyadicDeck n) w₂ :=
  (Complex.isQuotientCoveringMap_npow n).apply_eq_iff_mem_orbit

/-- **Branch ambiguity is dyadic-root scaling.** If `v` and `w` are two Böttcher values whose
`2ⁿ`-th powers agree (e.g. two continuations of `φ_c` over a base point, both `2ⁿ`-th roots of
`φ_c(f_c^[n]·)` via `bottcherCoord_iterate`), then `v = ζ·w` for some `2ⁿ`-th root of unity `ζ`.
This pins the monodromy multiplier set to `μ_{2ⁿ}`. -/
theorem eq_dyadicRoot_mul_of_npow_eq {n : ℕ} {v w : ℂˣ} (h : v ^ (2 ^ n) = w ^ (2 ^ n)) :
    ∃ ζ : dyadicDeck (2 ^ n), v = (ζ : ℂˣ) * w := by
  have : v ∈ MulAction.orbit (dyadicDeck (2 ^ n)) w :=
    (npow_eq_iff_mem_dyadicOrbit (2 ^ n) v w).mp h
  obtain ⟨ζ, hζ⟩ := this
  exact ⟨ζ, hζ.symm⟩

/-- **The dynamics supplies the radical tower.** A preimage `w` of `z` under `f_c^[n]` carries a
`2ⁿ`-th root of the Böttcher value `φ_c(z)`: `φ_c(w)^(2ⁿ) = φ_c(z)`. This is the *faithful*
source of the Prüfer–Kummer structure — the `2ⁿ`-th roots of `φ_{c₁}` are not adjoined formally
but are actual Böttcher values at inverse-orbit points (`bottcherCoord_iterate` read backwards).
The disconnected case is exactly when these inverse branches are globally obstructed, forcing the
nontrivial monodromy. -/
theorem bottcherCoord_pow_preimage {c z w : ℂ} (hcw : ‖c‖ ≤ ‖w‖) (hw : 2 < ‖w‖) {n : ℕ}
    (h : (quadratic c)^[n] w = z) : (bottcherCoord c w) ^ (2 ^ n) = bottcherCoord c z := by
  rw [← h]; exact (bottcherCoord_iterate hcw hw n).symm

/-- **Inverse branches differ by a dyadic root of unity.** Two `f_c^[n]`-preimages `w₁, w₂` of
the same `z` have Böttcher values related by `φ_c(w₁) = ζ · φ_c(w₂)` for some `2ⁿ`-th root of
unity `ζ`. This is the monodromy multiplier at the value level: the `2ⁿ` branches of `φ_c` over
`z` form a `μ_{2ⁿ}`-orbit (cf. `npow_eq_iff_mem_dyadicOrbit`), so going between branches scales
`φ_{c₁}` by an element of `μ_{2ⁿ}` — the scaling the germ-field automorphism `σ_n` realizes. -/
theorem bottcherCoord_preimage_dyadic {c z w₁ w₂ : ℂ}
    (hc1 : ‖c‖ ≤ ‖w₁‖) (hw1 : 2 < ‖w₁‖) (hc2 : ‖c‖ ≤ ‖w₂‖) (hw2 : 2 < ‖w₂‖) {n : ℕ}
    (h1 : (quadratic c)^[n] w₁ = z) (h2 : (quadratic c)^[n] w₂ = z) :
    ∃ ζ : ℂ, ζ ^ (2 ^ n) = 1 ∧ bottcherCoord c w₁ = ζ * bottcherCoord c w₂ := by
  have hpow : (bottcherCoord c w₁) ^ (2 ^ n) = (bottcherCoord c w₂) ^ (2 ^ n) := by
    rw [bottcherCoord_pow_preimage hc1 hw1 h1, bottcherCoord_pow_preimage hc2 hw2 h2]
  have hne2 : bottcherCoord c w₂ ≠ 0 := bottcherCoord_ne_zero c w₂
  refine ⟨bottcherCoord c w₁ / bottcherCoord c w₂, ?_, ?_⟩
  · rw [div_pow, hpow, div_self (pow_ne_zero _ hne2)]
  · rw [div_mul_cancel₀ _ hne2]

end Bottcher
