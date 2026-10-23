# The prime mean is quantized height by height

- **ID:** prime-mean-quantized-height-by-height
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Trans-Horizon Incidence Mechanics (§3.17 quantization of the prime mean; §5 parity pair)
- **Statement:** For `0 < ε < 1/2`, `t₀ ≠ 0`, `a ∈ [−1, 1]`, the weight `f_{a,t₀}(d) d^{-ε}`
  (`f(p) = a cos(t₀ log p)`, completely multiplicative) is paid iff `a = 0`.

## Why it matters

The corpus quantization law reads the prime mean on the real axis: a paid weight below half damping
has `ν ∈ {0, −1}`. The oscillating patterns have `ν = 0` on the real axis for every `a`, so that law
allows all of them. The local prime mean at the height `±t₀` is `a/2`; the order of
`Σ f(n)n^{-w}` at `1 ± it₀` must be an integer for a paid weight, which forces `a = 0`. The quantization
is a law at every height of the abscissa line, not only on the real axis.

## Paper proof

Let `s₁ = 1 − ε + it₀`, `C(s) = Σ c(d)d^{-s} = F(s + ε)`, `m = Σ c(d)/d`, `Φ` the complex Mellin pairing.

1. **Complex pairing identity.** For `Σ|c(d)|d^{-θ} < ∞` and `θ < Re s < 1`:
   `Φ(s) = ζ(s)(C(s) − m)` (Fubini over `(n, d)` with `|c(d)| |{n/d}-defect| |Δ_n(s)| ≤
   |s| n^{θ−σ−1} · |c(d)| d^{-θ}`; each modulus pairs to `ζ(s)(d^{-s} − 1/d)`).
2. **Analyticity at `s₁`.** Paid ⇒ `Φ` holomorphic on `Re s > 1/2 ∋ s₁` (corpus). `Q = Φ + mζ` and `ζ`
   are analytic at `s₁`, `ζ` not locally zero (identity theorem on `ℂ ∖ {1}`), and
   `C(s₁ + u) ζ(s₁ + u) = Q(s₁ + u)` for `u > 0`.
3. **Two-sided power law.** `C(s₁ + u) = F(1 + u + it₀)` and the Euler comparison give
   `|C(s₁ + u)| ≍ (|ζ(1 + u)| |ζ(1 + u + 2it₀)|)^{a/2} ≍ u^{-a/2}` (`|ζ(1+u)| ≍ 1/u`, `ζ(1 + 2it₀) ≠ 0`).
4. **Integer order.** `ζ(z) = (z − s₁)^q g(z)`, `g(s₁) ≠ 0`; `Q ≢ 0` near `s₁` (else `C ζ = 0`
   against step 3), so `Q(z) = (z − s₁)^p h(z)`, `h(s₁) ≠ 0`. On the ray `|C| = |Q|/|ζ| ≍ u^{p−q}`.
   Comparing with step 3, `−a/2 = p − q ∈ ℤ`; with `|a| ≤ 1` this forces `a = 0`.
5. **`a = 0`.** `f = δ_1` on `ℕ_{≥1}`; its weight is paid at every damping.

## Gates
- [x] 0 → 1  in-progress (corpus: the integer-order law exists only at the real abscissa,
  `exists_nat_eq_of_rpow_bounds_at_abscissa`)
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized (`ThePrimeMeanIsQuantizedHeightByHeight.lean`:
  `complexMellinPairing_eq_zeta_mul_of_summable`, `exists_ray_bounds_of_order`,
  `exists_norm_oscSeries_rpow_bounds`, `receiverBounded_oscPattern_damped_iff`; axioms `propext`,
  `Classical.choice`, `Quot.sound`)

## Log
- 2026-10-23 — formalized and wired into the THIM umbrella; moved to 3-formalized.
- 2026-10-23 — created.
