# The discrete Báez-Duarte Gram matrix, evaluated exactly

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## Correction to the previous card

`gram-diagonal-reduces-to-two-scalars.md` reduced the Gram diagonal to two scalars and named the cross tail
`∫₁^∞ {θv}{v}v^{-2}dv` as the obstruction, on the ground that the cells of `{θv}` and `{v}` interleave
incommensurably. That is correct about the **pieces** and wrong as a statement about the **Gram entry** at
`θ = 1/m`. The Báez-Duarte normalisation removes the difficulty entirely, and the previous card's framing
should be read as superseded here.

## The mechanism

On the cell `(a, a+1)` between consecutive integers, `⌊v/m⌋` cannot jump — a multiple of `m` is an integer —
so with `q = ⌊a/m⌋` and `{v} = v − a`,

`{v/m} − (1/m){v} = (v/m − q) − (v − a)/m = (a − mq)/m = (a mod m)/m`,

**a constant on the cell.** So `bdGenReal (1/m) v = (a mod m)/(m·v)` there, a product of two generators is a
constant times `v^{-2}`, and `∫_a^{a+1} v^{-2} = 1/(a(a+1))`.

## What is proved

`RHTower/BaezDuarteGramDiscrete.lean`, reusing the cell decomposition of `FractSqConstSeries`:

* `floor_div_eq_of_mem_cell` — `⌊v/m⌋` is the integer quotient of the left endpoint (the proof uses
  integrality: `a < (k+1)m` forces `a + 1 ≤ (k+1)m`);
* `bdGenReal_inv_nat_eq_of_mem_cell` — the generator is `(a mod m)/(m·v)` on the cell;
* `bdGenReal_mul_eq_of_mem_cell`, `abs_bdGenReal_mul_le`, `integrableOn_bdGenReal_mul` — the product and its
  integrability;
* `integral_tailCell_bdGenReal_mul` — one cell contributes
  `(a mod m₁)(a mod m₂)/(m₁m₂·a(a+1))`;
* **`hasSum_bdGram_discrete` — `bdGram (1/m₁) (1/m₂) = ∑_{n≥1} (n mod m₁)(n mod m₂)/(m₁m₂·n(n+1))`;**
* **`hasSum_bdGram_bdDiscrete`** — the same for `bdDiscrete i = 1/(i+1)`, i.e. for every entry of the Gram
  matrix that `bdDistDiscrete` actually uses.

All axiom-clean. Every term is rational and the series converges like `∑1/n²`.

Two checks that the formula is right rather than merely well-typed: at `m = 1` every term vanishes, matching
`bdGen 1 = 0`; and at `m₁ = m₂ = 2` it gives `(1/4)∑_{n odd}1/(n(n+1)) = (log 2)/4 ≈ 0.173`, which sits above
the Cauchy–Schwarz floor `(θ log θ)² ≈ 0.120` of `sq_le_bdGram_self`. Logarithms appear when these series are
summed in closed form — that is where the classical cotangent structure lives — but the series themselves need
nothing beyond cell cutting.

## Where this leaves the reduction

The chain in `nyman-beurling-carrier-no-hardy-space.md` is: `d_N → 0 ⟹ RH`, with
`d² = 1 + ∑ᵢcᵢθᵢ log θᵢ` where `bdGram·c = −θ log θ`. For the discrete system, **every ingredient is now
explicit**: the Gram entries are the rational series above and the right-hand side is `−θᵢ log θᵢ` with
`θᵢ = 1/(i+1)`. There is no unevaluated object left in the reduction for the system the criterion uses.

What remains is not a formalisation gap but the mathematics: showing that the solutions of these explicit
linear systems satisfy `∑ᵢ cᵢθᵢ log θᵢ → −1`. That statement is equivalent to RH, so it is exactly as hard as
RH — but it is now a fully explicit statement about rational series, with nothing hidden behind an
unevaluated integral.

## Addendum (same day): the right-hand side, and an arithmetic identity

`RHTower/BaezDuartePairingSeries.lean` does for the pairing what the main text did for the Gram matrix.
Pairing the piecewise-constant generator with the target `1/v` and summing the cells:

* `abs_bdGenReal_le` — the pointwise bound `|bdGenReal θ v| ≤ 2/v` (`|θ| ≤ 1`), extracted so every
  integrability argument in this layer cites one lemma;
* `integral_tailCell_bdGenReal_mul_inv` — one cell contributes `(a mod m)/(m·a(a+1))`;
* **`hasSum_pairing_discrete`** — `∑_{n≥1} (n mod m)/(m·n(n+1)) = (log m)/m`, the right-hand side of the
  normal system as a rational series.

Comparing the two evaluations of the same pairing — cell counting here, the dilation identity of
`BaezDuarteTargetPairing` there — gives an identity neither produces alone:

**`hasSum_mod_div_mul_succ` — `∑_{n≥1} (n mod m)/(n(n+1)) = log m`.**

Elementary and unconditional. `m = 1` gives `0 = log 1`; `m = 2` is the classical
`∑_{n odd} 1/(n(n+1)) = log 2`. The logarithm enters from the dilation side; the left side is pure counting.

So both data of the discrete Báez-Duarte normal system are now explicit rational series — the matrix by
`hasSum_bdGram_discrete`, the right-hand side by `hasSum_pairing_discrete` — and the whole criterion reads:
RH holds if the solutions of these rational systems satisfy `∑ᵢ cᵢ (log(i+1))/(i+1) → 1`.
