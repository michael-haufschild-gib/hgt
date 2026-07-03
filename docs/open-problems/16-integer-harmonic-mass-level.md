# Problem 16 — A Green level curve of one Cantor Julia set enclosing integer harmonic mass of another

## Setup

For `c ∈ ℂ` let `f_c(z) = z² + c`, let `K_c` be the filled Julia set (the set of `z` with
bounded forward orbit), and let

- `G_c : ℂ → [0, ∞)` be the Green's function of `K_c` with pole at infinity: `G_c` is
  continuous on `ℂ`, harmonic and positive exactly on `ℂ ∖ K_c`, vanishes on `K_c`, satisfies
  `G_c(f_c(z)) = 2·G_c(z)` and `G_c(z) = log|z| + o(1)` as `z → ∞`;
- `μ_c` be the equilibrium (harmonic) measure of `K_c` — the probability measure on `K_c`
  which is the distributional Laplacian `μ_c = (1/2π)·Δ G_c`;
- `h_c = G_c(0)` the critical level. When `0 ∉ K_c` (equivalently the critical orbit escapes),
  `h_c > 0` and `K_c` is a Cantor set (compact, perfect, totally disconnected).

Throughout, fix two parameters `c₁ ≠ c₂` with `0 ∉ K_{c₁}` and `0 ∉ K_{c₂}`, so both `K₁ = K_{c₁}`
and `K₂ = K_{c₂}` are Cantor sets. Write `G₁ = G_{c₁}`, `μ₂ = μ_{c₂}`, `h₁ = h_{c₁}`.

Basic facts free to use: for `ℓ > h₁` the level set `{G₁ = ℓ}` is a single real-analytic
Jordan curve encircling `K₁` (above the critical level there are no critical points of `G₁`);
the open region `Ω_ℓ = {G₁ < ℓ}` it bounds is a Jordan domain containing `K₁`; `Ω_ℓ`
increases with `ℓ`; `μ₂` has no atoms.

## The problem

**Question A (main).** Let `h₁ < a < b` be given. Must there exist `ℓ ∈ (a, b)` such that

1. `{G₁ = ℓ} ∩ K₂ = ∅`, and
2. `μ₂(Ω_ℓ) ∈ {0, 1}`

— that is, a level curve of `G₁` in the prescribed window which avoids `K₂` and encloses
either none or all of the harmonic mass of `K₂`?

If the answer is no in general, characterize the exceptional pairs `(c₁, c₂)` — or at least
give verifiable sufficient conditions covering: (i) all pairs with `|c₁|, |c₂| ≥ R₀` for some
absolute `R₀` and window `(a, b) = (h₁ + 1/8, 3h₁/2)`; or (ii) all pairs outside a set of
zero measure/capacity in the parameter region `{both Cantor}`.

**Question B (warm-up, believed provable).** Show that for every `δ > 0` there is a point
`x ∈ K₁` with `dist(x, K₂) > 0` and a dyadic puzzle piece of `K₁` at `x` (a component of
`{G₁ < h₁/2^k}` containing `x`, for large `k`) whose closure has an open neighbourhood
disjoint from `K₂`. (Since `K₁ ≠ K₂` — a quadratic filled Julia set determines its parameter —
`K₁ ∖ K₂ ≠ ∅`; pieces shrink to points.)

**Question C (context; not required).** Deduce from a positive answer to A (plus B) the
following: for every pair as above there exists, for each `k`, a closed curve `γ_k` in
`ℂ ∖ (K₁ ∪ K₂)` winding once around a depth-`k` dyadic piece of `K₁`, such that the analytic
continuation of the Böttcher coordinate `φ_{c₂}` (normalized `φ_{c₂}(z) = z + O(1)` at ∞,
extended along paths in `ℂ ∖ K₂`) is single-valued on a connected open set containing all
`γ_k` and a neighbourhood of infinity.

## Remarks for the solver

- The monodromy mechanism behind C: `log φ_{c₂} = G_{c₂} + i·H₂` locally, where `H₂` is a
  harmonic conjugate; the period of `dH₂` along a cycle `γ ⊂ ℂ ∖ K₂` equals
  `2π · ∫ n(γ, w) dμ₂(w)` with `n(γ, ·)` the winding number. So single-valuedness along `γ`
  is exactly integrality of the `μ₂`-winding mass. Condition 2 in Question A is this
  integrality for the level cycle (`n ≡ 1` on `Ω_ℓ`); mass `1` means `K₂ ⊂ Ω_ℓ`, mass `0`
  means `K₂ ∩ Ω_ℓ = ∅`.
- The function `ℓ ↦ μ₂(Ω_ℓ)` is nondecreasing. Question A asks whether it must pass through
  an integer value AT a level whose curve misses `K₂`. The danger is a pair for which the
  mass strictly increases across the whole window while every level curve in the window meets
  `K₂`. For foliations by straight segments such total badness is possible: there are Cantor
  quadratic Julia sets `K` and real-analytic foliations by disjoint compact arcs such that
  every leaf meets `K` (a slanted-projection construction near `c = −2` — the projection of a
  Cantor set can contain an interval). The question is whether the *Green level foliation of
  another quadratic Julia set* can be bad in this way; its leaves are canonically attached to
  the dynamics of `c₁`, which may exclude the projection pathology.
- Useful structure: `μ₂` is the balanced self-similar measure — `μ₂` gives each of the `2^k`
  depth-`k` dyadic pieces of `K₂` mass exactly `2^{-k}`. So `μ₂(Ω_ℓ) ∈ {0,1}` fails only if
  `∂Ω_ℓ`-curves separate pieces of `K₂` for all `ℓ` in the window; conversely, if some level
  curve `{G₁ = ℓ}` in the window encloses some pieces of `K₂` entirely and excludes the rest,
  the enclosed mass is `m/2^k` — integrality then still fails unless `m ∈ {0, 2^k}`. A
  correct positive strategy must therefore either separate `K₂` wholly from the window's
  levels (norm/level gap), or find a level curve avoiding an entire "side" of `K₂`.
- Monotonicity gives one cheap positive case: if `K₂ ∩ {a < G₁ < b}` is empty, every level in
  the window has constant enclosed mass equal to `μ₂(Ω_a)`; but that constant need not be an
  integer, so even this case is only useful combined with connectivity of `K₂`-pieces across
  `{G₁ < a}`.

## What counts as a solution

Any of: a proof of Question A as stated; a counterexample pair with a proof of total badness
in some window; a sufficient criterion with explicit constants covering case (i); or a proof
of Question C by a route that bypasses Question A (e.g. constructing the curves `γ_k`
directly with zero `μ₂`-winding without using level curves).
