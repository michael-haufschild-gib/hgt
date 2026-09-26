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

## Explicit level past the prime-2 entry (Lean)

**Statements.**
- `RHTower.one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo`: at the aperture
  `b = ½(log 2 + 1/50)` (`λ₁ = √2 · e^{1/100} ≈ 1.4284`), `μ₀(b) ≥ 1/20` with the prime `2` in the
  form.
- `RHTower.one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo`: every aperture
  `c ≤ b` has `μ₀(c) ≥ 1/20`.

Axioms: `[propext, Classical.choice, Quot.sound]`.

**Mechanism: Krein extension freedom.** On `V₀(b)` the form is the Fourier multiplier
`W − √2 log 2 · (cos 2πLξ − cos 2π·2b·ξ)`. The prime term is `cos 2πLξ`, and the added
`cos 2π·2bξ` is a lag-`2b` term with null overlap, so it is free.
- The difference equals `2 sin(π(2b+L)ξ) sin(πξ/50)`.
- It is nonpositive on `[0.7111, 1.4221]`, at most `0.12319|ξ|`, and at most `1.9606` everywhere.

**Certificate data.**
- Parameters: `α = 3/10`, `h = 1/10`, 18 shells.
- Shell residuals use the optimal residual `2b − C²/(b+sinh b) − S²/(sinh b − b)`, so no fitted
  parameters are needed.
- Tail thresholds `1.8, 2.05, 3.2, 6.6, 12.5` use a sharpened logarithm bound (compare at
  `2^j·264.0625`).
- Modules: `RHTower/PoleVanishingWeilPrimeTwoEntry` (translation = modulation, source reduction,
  general-symbol certificate) and `RHTower/PoleVanishingWeilPositivityPrimeTwo`.
- Wired into the umbrella; `lake build --old` passes; lint clean.

**Scope.** Computer-free, but below the numerical record: the corpus pod certificate reaches
`λ ≈ 1.568` and Zhu reaches `e^{0.8}`. This result does not address the super-exponential decay
of `μ₀` (HF-F12).
