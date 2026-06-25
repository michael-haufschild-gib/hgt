/-
# φ_b transcendence over ℂ(z) — the Mahler-method lane

The card's `u₀ ⟂ φ_b` proof cites Becker–Bergweiler for the `deg_U = 0` case: `φ_b` is **not**
algebraic over `ℂ(z)` for nonexceptional `b`. The natural-boundary route to this (φ_b's Julia set is a
natural boundary) is blocked: the Böttcher coordinate `bottcherCoord` is only built on the escape region
`escapeOpen c = {|z| > max(2,‖c‖)}`, not yet extended through the basin to `J_c`. The **Mahler-method**
route uses only the escape-region functional equation `φ_c(z²+c) = φ_c(z)²` (`bottcherCoord_quadratic`),
which IS available.

This file lays the Mahler groundwork. The transformation is `σ : z ↦ z²+c = quadratic c z`, a degree-`2`
self-map of the escape region; `φ_c` intertwines it with `w ↦ w²`. A polynomial relation
`P(z, φ_c(z)) = 0` therefore propagates: `P(σz, φ_c(z)²) = 0`. Iterating `σ` blows up the `z`-degree
geometrically while algebraicity bounds it — the Mahler/Nishioka contradiction (the remaining core).

* `quadratic_mem_escapeOpen` — `σ` preserves the escape region (strict expansion).
* `relation_propagate` — the functional-equation propagation of a relation under one application of `σ`.
* `relation_propagate_iterate` — its `n`-fold iterate: `P` evaluated at `(σⁿ z, φ_c(z)^{2ⁿ})` vanishes.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord
import GaloisForLFunctions.Bottcher.Dynamics

open Polynomial Bottcher

namespace PhiMahler

/-- **The squaring map preserves the escape region.** If `z ∈ escapeOpen c` then `quadratic c z =
z²+c ∈ escapeOpen c`, by strict expansion `‖z‖ < ‖z²+c‖` beyond radius `2`. So `σ : z ↦ z²+c` is a
self-map of the domain on which `φ_c` is defined — the Mahler transformation. -/
theorem quadratic_mem_escapeOpen {c z : ℂ} (hz : z ∈ escapeOpen c) :
    quadratic c z ∈ escapeOpen c := by
  obtain ⟨hc, h2⟩ := mem_escapeOpen_regime hz
  exact lt_trans hz (quadratic_norm_lt hc h2)

/-- **`σⁿ` preserves the escape region.** Iterating `quadratic_mem_escapeOpen`. -/
theorem quadratic_iterate_mem_escapeOpen {c z : ℂ} (hz : z ∈ escapeOpen c) (n : ℕ) :
    (quadratic c)^[n] z ∈ escapeOpen c := by
  induction n with
  | zero => simpa using hz
  | succ k ih => rw [Function.iterate_succ_apply']; exact quadratic_mem_escapeOpen ih

/-- **Functional-equation propagation of a polynomial relation (one Mahler step).** If `P ∈ ℂ[z][Y]`
satisfies `P(z, φ_c(z)) = 0` throughout the escape region, then `P(σz, φ_c(z)²) = 0` there too, where
`σz = z²+c`. Proof: `σz ∈ escapeOpen c` (stability), so the relation holds at `σz`:
`P(σz, φ_c(σz)) = 0`; and `φ_c(σz) = φ_c(z)²` (`bottcherCoord_quadratic`). This is the algebraic shadow of
the dynamical conjugacy `φ_c ∘ f_c = (·)² ∘ φ_c`. -/
theorem relation_propagate {c : ℂ} (P : Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ escapeOpen c, P.eval₂ (evalRingHom z) (bottcherCoord c z) = 0)
    {z : ℂ} (hz : z ∈ escapeOpen c) :
    P.eval₂ (evalRingHom (quadratic c z)) ((bottcherCoord c z) ^ 2) = 0 := by
  obtain ⟨hc, h2⟩ := mem_escapeOpen_regime hz
  have hq := hrel (quadratic c z) (quadratic_mem_escapeOpen hz)
  rwa [bottcherCoord_quadratic hc h2] at hq

/-- **`n`-fold Mahler propagation.** `P(σⁿ z, φ_c(z)^{2ⁿ}) = 0` on the escape region: the relation at
`σⁿ z` together with the iterated functional equation `φ_c(σⁿ z) = φ_c(z)^{2ⁿ}`. The `z`-degree of the
left coordinate grows like `2ⁿ` under `σⁿ`, while `Y` is replaced by `φ_c(z)^{2ⁿ}` — the geometric
blow-up that, against the fixed algebraic degree of a relation, drives the Mahler/Nishioka contradiction. -/
theorem relation_propagate_iterate {c : ℂ} (P : Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ escapeOpen c, P.eval₂ (evalRingHom z) (bottcherCoord c z) = 0)
    {z : ℂ} (hz : z ∈ escapeOpen c) (n : ℕ) :
    P.eval₂ (evalRingHom ((quadratic c)^[n] z)) ((bottcherCoord c z) ^ (2 ^ n)) = 0 := by
  have hbott : bottcherCoord c ((quadratic c)^[n] z) = (bottcherCoord c z) ^ (2 ^ n) := by
    induction n with
    | zero => simp
    | succ k ih =>
      obtain ⟨hc, h2⟩ := mem_escapeOpen_regime (quadratic_iterate_mem_escapeOpen hz k)
      rw [Function.iterate_succ_apply', bottcherCoord_quadratic hc h2, ih, ← pow_mul, pow_succ]
  have hq := hrel ((quadratic c)^[n] z) (quadratic_iterate_mem_escapeOpen hz n)
  rwa [hbott] at hq

/-- **The Mahler tower of roots.** Fix `z₀` in the escape region and set `w = φ_c(z₀)`. For every `n`,
`w^{2ⁿ}` is a root of the specialized one-variable polynomial `P(σⁿz₀, ·) = P.map (evalRingHom (σⁿz₀))`.
So a single point `z₀` produces an infinite sequence of roots `w, w², w⁴, …` of the family `P(σⁿz₀, ·)`
of *bounded* `Y`-degree `≤ deg_Y P`, with `|w^{2ⁿ}| = |w|^{2ⁿ}` blowing up when `|w|>1` (which holds on
the escape region, `|φ_c|=exp G>1`). This bounded-degree-vs-blow-up tension is the lever of the
Mahler/Nishioka contradiction; the remaining core is the precise height estimate that closes it. -/
theorem isRoot_specialize_iterate {c : ℂ} (P : Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ escapeOpen c, P.eval₂ (evalRingHom z) (bottcherCoord c z) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ escapeOpen c) (n : ℕ) :
    (P.map (evalRingHom ((quadratic c)^[n] z₀))).IsRoot ((bottcherCoord c z₀) ^ (2 ^ n)) := by
  rw [IsRoot.def, eval_map]
  exact relation_propagate_iterate P hrel hz₀ n

end PhiMahler
