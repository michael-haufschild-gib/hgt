# Pole-vanishing Weil positivity at √2 and past the first prime: the trace certificate (Lean)

- **ID:** `WEIL-TRACE-CERT-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean, unconditional, computer-free)
- **Parents:** `1-in-progress/weil-positivity-soft-prime-entry.md` (Theorems C–D; its `√2` input),
  `1-in-progress/weil-pole-vanishing-bathtub-certificate-sqrt2.md` (superseded parallel card)
- **RH used:** no · **Computation used:** no (all numerics are `norm_num` rational enclosures in Lean)

## Statement

Let `μ₀(a)` be the pole-vanishing ground energy of the exact restricted Weil form (archimedean
Riemann–Siegel symbol, polar rank-two term, all prime powers `n ≤ e^{2a}`) on the logarithmic
aperture `[−a, a]`.

1. `μ₀(½ log 2) ≥ 1/10`: `RHTower.one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo`.
2. There is `b > ½ log 2` with `μ₀(c) > 0` for every aperture `c ≤ b`, so the prime `2` is
   included past `√2`: `RHTower.exists_polarGroundEnergy_pos_past_halfLogTwo`.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Proof

**(a) Trace certificate.** For a pole-vanishing `f`, `𝓕f(ξ) = ⟨e_ξ − p cosh(x/2) − iq sinh(x/2), f⟩`,
so `|𝓕f(ξ)|² ≤ ‖f‖² ρ²(ξ; p, q)`. The residual has the closed form
`ρ² = 2a − 2pC + p²(a + sinh a) − 2qS + q²(sinh a − a)`.

**(b) Reduction.** At `a = ½ log 2`, on `V₀` the form is `∫ W|𝓕f|²` with
`W(ξ) = Re ψ(1/4 + iπξ) − log π`: the polar term vanishes, and the `n = 2` translation has null
overlap. Since `W` is even and monotone in `|ξ|`, `Q ≥ (α − Σ_k 2h G_k R_k)‖f‖²`.

**(c) Numerics (all in Lean).**
- Parameters: `α = 3/10`, `h = 1/10`, 14 shells, total `< 1/5`.
- `W` lower bounds come from the digamma recurrence, the half-plane asymptotic and `log π < 1.146`.
- Shell constants come from the closed residual at rational phases `θ`: midpoint–radius enclosures
  of `log 2`, `2^{1/4}` and degree-20 Taylor `sin`/`cos`, plus the Lipschitz offset `0.00276`.

**(d) Extension.** Part 2 follows from the continuity of `μ₀` (Suzuki; constrained version in the
corpus).

## Lean

| result | module |
|---|---|
| enclosure arithmetic, Taylor enclosures | `HTGeometry/MidpointRadiusTrigEnclosures` |
| plane-wave residual bound, closed form, Lipschitz bound, source reduction, grid certificate | `RHTower/PoleVanishingWeilTraceCertificate` |
| constants, 14 shell residuals, 15 grid values, assembly | `RHTower/PoleVanishingWeilPositivityHalfLogTwo` |

- Wired into `RHTower.lean` and `HTGeometry.lean`.
- `lake build --old` passes.
- Lint: no issues in these modules, no heartbeat overrides.

## Novelty audit

- **Connes–Consani 2021:** positivity at `√2`, with one computer-checked estimate (margin 0.3 %).
- **Zhu, arXiv 2608.24827 (Aug 2026):** certified interval computation on `[−0.8, 0.8]`, primes
  included, margin `8.9·10⁻¹⁸`.
- **Corpus pod certificate (Sept 2026):** reaches `λ ≈ 1.568` numerically.
- **New here:**
  - a computer-free, kernel-checked proof with an order-one margin at `√2`;
  - the one-line trace criterion `μ₀ ≥ α − ∫(α − W)₊ dist²(e_ξ, span e^{±x/2})`;
  - its Krein-extension refinement (free kernel terms at lags `≥ 2a`).

  Positivity past `√2` is not new as a statement.

## Scope

- `μ₀` decays super-exponentially after the prime-2 entry: `0.52 → 0.017` by `λ = 1.568`,
  `≤ 0.003` at `λ = 1.649`.
- So level-by-level certificates cannot approach RH (gate "No slack"; HF-F12).
- Route reading: this is the finite-level arithmetic Hodge index (HF-F11 = route RW).
