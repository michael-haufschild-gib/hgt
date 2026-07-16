# Watson flatness for half-argument digamma jets — unconditional discharge

- **ID:** watson-flatness-discharge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/HTGeometry/QuantitativeHolderInterface.lean`
- **Statement:** For every `n`, every `P : MvPolynomial (Fin (n+2)) ℂ`, and every `c > 0`,
  if `σ ↦ halfDigammaJetEval n P σ = O(exp (−cσ))` at `+∞`, then this evaluation is
  eventually zero on the real ray.

## Goal

`WatsonFlatness` was the single named analytic input separating `QuantitativeHolder` from the
already formalized Hölder contradiction. Its discharge makes quantitative Hölder unconditional.
In the completed-`ξ` chain, only the independent `XiFrequencyCollapse` proposition remains.

## Scientific register and dual gate

- **Register:** `[SEARCH] [BRIDGE] [FORMALIZATION]`.
- **Novelty:** **not new scientific knowledge.** The proof is a Watson-uniqueness argument built
  from standard Phragmén–Lindelöf principles. The contribution is a complete specialization to
  half-argument digamma jets and its unconditional formalization, not a new uniqueness principle.
- **Significance:** high as project infrastructure: it removes the analytic `WatsonFlatness`
  hypothesis from quantitative Hölder and from the corresponding side of the `ξ` chain.
- **Classification:** significant bridge, but it fails the `NOVEL × SIGNIFICANT` gate for a claim
  of new mathematical knowledge and therefore belongs under `not_new_scientific_knowledge`.

## Gates

- [x] 0 → 1 in-progress: well-posed; all pole, growth, strip, and power-map obligations isolated
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`, with no open mathematical input
- [x] 2 → 3 formalized: unconditional Lean theorems, exact source checks and module builds,
      regenerated-index lint on the isolated Watson change set, and axiom inspection all pass
- [ ] 3 → 4 publication-ready

## Proof `[PROVED HERE]`

Fix `n`, `P`, and `c > 0`, and write

`E(s) = halfDigammaJetEval n P s`,  `G(z) = E(1+z)`.

Assume `E(σ) = O(exp(−cσ))` on the real ray at `+∞`. We prove that `G` vanishes on
the nonnegative real ray.

### 1. Polynomial growth on a `2π/3` sector

Let

`S = {z ∈ ℂ : −‖z‖/2 ≤ Re z}`.

For `z ∈ S` and `t ≥ 0`, expansion of the squared norm gives

`((‖z‖+t)/2)^2 ≤ ‖z+t‖^2`.

Hence

`(‖z‖+t)/2 ≤ ‖z+t‖`.

Taking `t=2k+1` yields the uniform denominator separation

`(‖z‖+2k+1)/4 ≤ ‖(1+z)/2+k‖`.

In particular `(1+z)/2` meets no digamma pole. For the Gauss-series term one obtains

`|a_k((1+z)/2)| ≤ 2(1+‖z‖)/(k+1)^2`.

Summation of this majorant and the off-pole Gauss identity give

`‖ψ((1+z)/2)‖ ≤ C₀(1+‖z‖)`.

For every `m ≥ 0`, the in-tree polygamma shift formula at the integer translates of
`s=(1+z)/2`, followed by the in-tree limit at infinity, identifies
`ψ^(m+1)(s)` with its absolutely convergent inverse-power series. The same denominator
separation gives a summable majorant proportional to `(k+1)^{−(m+2)}`. Thus

`‖ψ^(m+1)((1+z)/2)‖ ≤ C_m`

uniformly on `S`. The finite multivariate-polynomial estimate then supplies constants `C_P ≥ 0`
and `d_P ∈ ℕ` such that

`‖G(z)‖ ≤ C_P(1+‖z‖)^{d_P}`  for every `z ∈ S`.

The same pole separation and the existing analyticity theorem show that `G` is analytic on `S`.

### 2. Propagation of ray decay into a sector wider than a half-plane

Fix

`α=2π/3`,  `θ=π/12`,  `β=13π/24`.

For the upper strip `0 < Im η < α`, put

`H₊(η)=G(exp η) exp((c/2)e^{−iθ} exp η)`.

On `Im η=0`, the assumed ray estimate bounds `H₊` for large `Re η`; continuity bounds the
remaining compact interval. On `Im η=α`,

`Re(e^{−iθ} exp(x+iα)) = exp(x) cos(α−θ) < 0`,

so the exponential weight dominates the polynomial sector bound. Globally in the strip,
`H₊` has a double-exponential envelope with exponent parameter `1`, while
`1 < π/α = 3/2`. The horizontal-strip Phragmén–Lindelöf theorem therefore bounds `H₊`
throughout the closed upper strip.

The reflected construction

`H₋(η)=G(exp η) exp((c/2)e^{iθ} exp η)`

does the same on `−α < Im η < 0`. Since `β < α` and

`δ = cos(β−θ) = cos(11π/24) > 0`,

the two strip estimates combine to constants `C ≥ 0`, `d>0` with

`‖G(z)‖ ≤ C exp(−d‖z‖)`

whenever `|arg z| ≤ β`.

### 3. Power widening and right-half-plane uniqueness

Let `κ=13/12`; then `1<κ<2` and `κπ/2=β`. On the closed right half-plane define,
using the principal complex power,

`W(w)=G(w^κ)`.

For nonzero `w` with `Re w ≥ 0`, `|arg w| ≤ π/2`, hence
`arg(w^κ)=κ arg w` and `|arg(w^κ)|≤β`. Also
`‖w^κ‖=‖w‖^κ`. Consequently

`‖W(w)‖ ≤ C exp(−d‖w‖^κ)`.

This estimate bounds `W` on the closed half-plane and makes its positive-real restriction
superpolynomial relative to `exp`: for every `m`, eventually

`d x^κ − mx ≥ x`,

because `d x^{κ−1}→+∞`. Thus `exp(x)^m‖W(x)‖→0`. Analyticity in the open
half-plane and continuity on its closure follow from the principal-power lemmas, including at
zero. The right-half-plane Phragmén–Lindelöf uniqueness theorem gives

`W(w)=0` for every `Re w ≥ 0`.

For `t≥0`, take `x=t^{1/κ}≥0`. The real and complex power identities give `x^κ=t`, so
`G(t)=W(x)=0`. Therefore `E(σ)=0` for every real `σ≥1`, and in particular eventually at
`+∞`. This is `WatsonFlatness`. ∎

## Lean certificate

- `HTGeometry/DigammaSectorBounds.lean` formalizes denominator separation, absence of poles,
  Gauss-series growth, the all-order polygamma series bound, polynomial jet growth, and
  analyticity on the shifted sector.
- `HTGeometry/WatsonFlatnessDischarge.lean` formalizes both strip arguments, the uniform sector
  decay, principal-power widening, superpolynomial decay, the right-half-plane zero theorem, and
  exports `watsonFlatness : WatsonFlatness` and
  `quantitativeHolder : QuantitativeHolder` with no hypotheses.
- `RHTower/XiHypertranscendenceChain.lean` exports
  `xi_hypertranscendental_of_frequencyCollapse`; only `XiFrequencyCollapse` remains as a
  hypothesis.
- Exact source checks and exact module builds for all three touched theorem modules pass with no
  warnings in the touched files. A regenerated-index `formal_tools.py lint --check-generated`
  audit of the isolated Watson change set also passes; the temporary baseline repair consisted
  only of importing five unrelated modules already unreachable before this card existed.
- The exported theorems depend only on `[propext, Classical.choice, Quot.sound]`; there is no
  project axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration in the proof surface.

## Log

- 2026-07-16 — paper proof and unconditional Lean implementation completed; exact theorem-module
  checks/builds and axiom inspection passed.
- 2026-07-16 — regenerated-index lint passed on the isolated Watson change set after neutralizing
  five pre-existing baseline umbrella gaps; promoted to `3-formalized`. The live shared tree still
  has unrelated active reachability/index failures, none involving the Watson modules.
