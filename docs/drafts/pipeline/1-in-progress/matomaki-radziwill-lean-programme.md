# Matomäki–Radziwiłł in Lean — the shared Route-E analytic gate

- **ID:** `MR-LEAN-PROGRAMME-001`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME (infrastructure for several stage-2 cards)
- **RH used:** no
- **Computation used:** no

## Why this card exists

Five stage-2 cards are blocked on exactly two published analytic theorems, neither in mathlib nor in
the vendored `PNTPlus`:

| Card | Blocking input |
|---|---|
| `2-fully-proven/new_scientific_knowledge/route-e-coprime-square-root-mobius-product-sign-law.md` | Matomäki–Radziwiłł 2016, Theorem 1 (for `μ`) |
| `2-fully-proven/new_scientific_knowledge/route-e-growing-reciprocal-marker-low-breadth-transport.md` | same |
| `2-fully-proven/new_scientific_knowledge/route-e-reciprocal-marker-mobius-hall-law.md` | same |
| `2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md` | Matomäki–Teräväinen 2022, Theorem 1.2 (all-interval `E₃`) |
| `2-fully-proven/route-e-forbidden-support-e3-stability.md` | same |

Every other step of all five cards is already an unconditional Lean theorem of this corpus.  This
card tracks the construction of the missing analytic layer.  It is infrastructure, not new
scientific knowledge: the mathematics is published, and the work is the formalisation.

## The exact target

For `route-e-coprime-square-root-mobius-product-sign-law` the corpus has already reduced the card's
whole statement to one hypothesis, `RHTower.Sieve.AveragedMeanSquare` at `μ` — equivalently
(`averagedMeanSquare_of_maximal`, `maximalWindowMeanSquare_of_firstMoment`) the maximal-window form.
In classical notation, with `X = √x` and window length `h`:

```text
(1/X) ∑_{X/2 ≤ y ≤ X} | ∑_{y < n ≤ y+h} μ(n) |²  =  o(h²)      for every h = h(X) → ∞.
```

That is Matomäki–Radziwiłł Theorem 1 for the Möbius function.  Nothing weaker suffices: the card
quantifies over *every* window law with `h/log log(3x) → ∞`, and the corpus's own unconditional
range (`route_e_sign_density_of_mertens_rate`) is governed by the error term in the prime number
theorem, hence never reaches below `h ≈ X·exp(-c(log X)^{3/5})`.

## The route being formalised

Soundararajan's Bourbaki exposé 1119 (arXiv:1606.08021) gives a staged proof, each stage widening
the admissible range of `h`.  The stages are the milestones of this card.

| Milestone | Range of `h` | New ingredients |
|---|---|---|
| A (exposé §3) | `h ≥ exp((log X)^{3/4})` | Lemmas 2.1, 2.2, 2.3, 2.4 + Turán–Kubilius |
| B (exposé §4) | `h ≥ exp(10(log log X)^{10/9})` | + Lemmas 2.5, 2.6 (large values, Halász–Montgomery) |
| C (exposé §5) | `h > exp((log log log X)²)` | + the high-moment trick on the exceptional set |
| D (MR 2016 §§4–7) | every `h → ∞` | the full ladder of prime ranges `P^{(0)},…,P^{(L)},Q` |

Only milestone D closes the three `route-e-*` cards; A–C are strict intermediate advances over the
corpus's current unconditional range and are worth banking separately.

### The lemmas, and what the corpus already owns

- **Lemma 2.1 (Plancherel).** `∫_0^∞ |∑_{xe^{-1/T}<n≤xe^{1/T}} a(n)|² dx/x = (2/π)∫ |A(y)|² (sin(y/T)/y)² dy.`
  **DONE** — see "Lean progress" below.
- **Lemma 2.2 (multiplicative → additive windows).**  For `a` supported on `[c₁X, c₂X]` and
  `1 ≤ h ≤ c₁X/10`,
  `∫_0^∞|∑_{x<n≤x+h}a(n)|²dx ≪ (c₂²/c₁)X∫|A(y)|² min(h²/(c₁²X²), 1/y²) dy`.
  Open.  Proof: average the additive window over a shift `ν ∈ [2h,3h]`, substitute `ν = δx`, and
  feed the result into Lemma 2.1 at `T = 2/log(1+δ)`.
- **Lemma 2.3 (Vinogradov–Korobov twisted sums).** `∑_{n≤x}λ(n)n^{it} ≪ x exp(-log x/(log(x+|t|))^{2/3+δ})`
  and the prime analogue.  The corpus owns a zero-free strip and a twisted Möbius contour layer
  (`MoebiusTwist*.lean`); the exact uniformity in `t` needs an audit.
- **Lemma 2.4 (mean value theorem).** `∫_{-T}^{T}|∑_{n≤N}a(n)n^{it}|²dt ≪ (T+N)∑|a(n)|²`.
  **CORPUS** — `Sieve/DirichletIntegralBound.integral_normSq_dirPoly_le` and the symmetric form
  `Sieve/LogPolyDirPoly.integral_Icc_normSq_dirPoly_symm_le`.
- **Lemma 2.5 (large values for prime polynomials).** `|E| ≪ (V² log T)^{1+log T/log P}`.
  Open; the corpus's sixth-moment layer (`Sieve/DirichletSixthMoment*.lean`) is the same device at a
  fixed exponent and should generalise to the `k`-th power used here.
- **Lemma 2.6 (Halász–Montgomery).** `∫_E|∑_{n≤N}a(n)n^{it}|²dt ≪ (N+|E|T^{1/2}log T)∑|a(n)|²`.
  Open.
- **Lemma 7.1 (Halász–Montgomery for prime polynomials).** Open; needed only for general `f`, not
  for `μ`.
- **Turán–Kubilius** `∑_{X≤n≤2X}(ω_P(n)-W(P))² ≪ X W(P)`. **CORPUS** — `Sieve/TuranKubilius.lean`
  (uniformity over the moving prime set needs an audit).
- **The rough-integer sieve** `#{n ≤ X : n has no prime factor in [P,Q]} ≪ X/W(P)`. **CORPUS** —
  `Sieve/RoughCountTuran.card_roughSet_le`, `Sieve/RoughCount.card_rough_Ioc_le`,
  `Sieve/SelbergTail.card_rough_Ioc_le_selberg`.

## Lean progress

### Lemma 2.1 landed — `Sieve/LogWindowPlancherel.lean`

The corpus's Gallagher layer (`Sieve/GallagherSplitIntegral.lean`) bounds the mean square of a
logarithmic window sum by `2δ²·∫_{|w|≤W}|F|² + M₂·2/(π²W)`, where `M₂` is a *sup* bound on the
Dirichlet polynomial.  That second term is fatal for short windows: with the natural normalisation
it forces `h ≫ √X`, which is exactly where the corpus's unconditional range currently sits.  The
new module replaces the inequality by the exact identity, and the sup term disappears.

| Item | Declaration |
|---|---|
| the window sum as a sum of constant indicators; it lies in every `L^p` | `logWindowSum_eq_sum_indicator`, `memLp_logWindowSum`, `integrable_logWindowSum` |
| the common spectral factor `K_δ(w) = (e^{2πiwδ}-1)/(2πiw)` | `logWindowKernel` |
| `‖e^{iθ}-1‖ = 2|sin(θ/2)|`, hence `‖K_δ(w)‖ = |sin(πδw)|/(π|w|)` | `norm_exp_ofReal_mul_I_sub_one`, `norm_logWindowKernel`, `normSq_logWindowKernel` |
| the spectral weight is even, and bounded by `δ²` and by `(πw)^{-2}` | `normSq_logWindowKernel_neg`, `normSq_logWindowKernel_le_sq`, `normSq_logWindowKernel_le_inv_sq`, `normSq_logWindowKernel_le_min` |
| the Fourier integral factors: `𝓕 S (w) = K_δ(w)·A(-w)` | `fourier_logWindowSum` (with `integral_exp_mul_indicator_logWindow`, `integrable_exp_mul_indicator_logWindow`) |
| **Lemma 2.1**: `∫_ℝ|S(u)|²du = ∫_ℝ ‖K_δ(w)‖²·|A(w)|²dw` | `integral_normSq_logWindowSum_eq` |
| the spectral density is integrable, and any majorant of it bounds the mean square | `integrable_normSq_logWindowKernel_mul_logPoly`, `integral_normSq_logWindowSum_le_of_majorant` |

Unconditional, umbrella-wired, olean built; `#print axioms` on all capstones gives
`propext`, `Classical.choice`, `Quot.sound` only.

## Log

- 2026-08-17 — card opened; Lemma 2.1 formalised as an exact identity, replacing the corpus's lossy
  Gallagher inequality.  Next brick: Lemma 2.2, the multiplicative-to-additive window transfer.
