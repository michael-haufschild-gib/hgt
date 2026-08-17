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
  **NOT NEEDED for these cards** — see "Lemma 2.2 is bypassed" below.
- **Lemma 2.3 (Vinogradov–Korobov twisted sums).** `∑_{n≤x}λ(n)n^{it} ≪ x exp(-log x/(log(x+|t|))^{2/3+δ})`
  and the prime analogue.  **This is a hard prerequisite, and the corpus does not have it** — see
  "The Vinogradov–Korobov prerequisite" below.
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

### The discrete interface landed — `Sieve/LogWindowDiscreteTransfer.lean`

Plancherel controls `∫_ℝ|S(u)|²du`; the cards consume a *finite sum* over starting points.  This
module is the bridge, and it is what makes "Lemma 2.2 is bypassed" (below) effective.

| Item | Declaration |
|---|---|
| the integers of a finite set in a real interval number at most its length plus one | `card_filter_mem_Ioc_le` |
| two windows of equal length differ only in their two end intervals, so `‖S(u) - S(u')‖ ≤ M·((e^{u'}-e^{u}+1) + (e^{u'+δ}-e^{u+δ}+1))` | `norm_logWindowSum_sub_le` |
| **the transfer**: for starting points whose intervals `[u_i, u_i+λ)` are pairwise disjoint and on which `S` oscillates by at most `C`, `λ∑_i‖S(u_i)‖² ≤ 2∫_ℝ‖S‖² + 2λC²·#{i}` | `sum_normSq_logWindowSum_le_integral` |

Unconditional, umbrella-wired, olean built, axiom-clean.  Note that `norm_logWindowSum_sub_le`
needs no hypothesis on `δ` or on the sign of `u`: the count bound is uniform.

## Log

- 2026-08-17 — card opened; Lemma 2.1 formalised as an exact identity, replacing the corpus's lossy
  Gallagher inequality.  Two structural findings recorded below: Lemma 2.2 is unnecessary for these
  cards, and the Vinogradov--Korobov zero-free region is a hard prerequisite for every milestone.

## Two structural findings (2026-08-17)

### Lemma 2.2 is bypassed

The exposé needs the Saffari--Vaughan device because Theorem 1.1 is stated for *additive* windows
`[x, x+h]`, while Plancherel is natural for *multiplicative* windows `[xe^{-1/T}, xe^{1/T}]`.  The
three `route-e-*` cards do not need it: the corpus has already reduced them to
`RHTower.Sieve.AveragedMeanSquare`, whose inner sum is

```text
innerFibre x h a  =  { b : x/a ≤ b ≤ (x + h√x)/a }  =  ( y, y(1 + h/√x) ] ,   y = x/a,
```

a multiplicative window whose *ratio* `1 + h/√x` does not depend on the outer variable `a`.  So
Lemma 2.1 applies to the card's own object with `δ = log(1 + h/√x)`, and the only interface still
needed is the passage from the discrete sum over `a ∈ (√x, 2√x]` to the integral over starting
points.  That passage is elementary: the points `u_a = log(x/a)` are separated by `≍ 1/√x`, and on
an interval of length `1/(4√x)` around `u_a` at most one integer enters or leaves each end of the
window, so

```text
∑_a S(u_a)²  ≤  8√x ∫_ℝ S(u)² du  +  8·#{a} ,
```

and `#{a} ≍ √x = o(h²√x)` whenever `h → ∞`.  This removes one full lemma from the programme.

### The Vinogradov--Korobov prerequisite

Lemma 2.3 is used in *every* stage of the exposé (§3 (28)--(29), §4 (38), §5, §7 (56)), always in
the same way: the sum over a dyadic block of primes `P_j` must exhibit cancellation uniformly for
frequencies `|y| ≤ X`.  The bound needed is

```text
∑_{p ≤ P} p^{it}  ≪  π(P)/(1+|t|)  +  P·exp( - log P / (log(P + |t|))^{2/3+δ} ) ,
```

and it is useful exactly when `log P ≫ (log X)^{2/3+δ}`.  The choice `P_j ≥ exp((log h)^{9/10})`
with `h ≥ exp((log X)^{3/4})` gives `log P_j ≥ (log X)^{27/40}`, and `27/40 > 2/3` is the whole
reason for those exponents.

The corpus's zero-free region is `RHTower.Sieve.riemannZeta_ne_zero_routeT_region` /
`exists_routeT_zero_free_region`, of classical shape `1 - c/(log γ)^κ` with a generous `κ`; the
twisted Möbius layer (`MoebiusTwistSaving`, `MoebiusTwistSharpRate`) carries the matching saving
`exp(-c log N / (log K)^9)` uniformly for `5 + 4|τ| ≤ K`.  With exponent `9` — or even with the
classical de la Vallée Poussin exponent `1` — the requirement becomes `log P ≫ (log X)^9`
(respectively `≫ log X`), which is impossible since `P ≤ h ≤ X`.  **So no reorganisation of the
argument avoids the Vinogradov--Korobov region: an exponent strictly below `3/4` is a hard
prerequisite for every milestone.**

The corpus does own the combinatorial heart of the Vinogradov method:
`Sieve/VinogradovMeanValueBound.vinogradov_mean_value_bound` bounds the diagonal solution count of
the Vinogradov system with explicit constants, and `Sieve/VinogradovRouteTSaving.lean` extracts a
power-saving exponent from it.  The missing chain is: mean value ⟹ exponential-sum bound for
`∑_{n ≍ N} n^{it}` ⟹ growth of `ζ` in the strip ⟹ zero-free region with exponent `2/3+δ` ⟹
Lemma 2.3 by contour shift.  This becomes **Milestone 0** of the programme, and it must be built
before A.

Revised milestone order: **0 (Vinogradov--Korobov) → A → B → C → D**.
