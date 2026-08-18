# The two-dimensional prime-pair sieve is built (2026-08-18)

Corrects the earlier `cards/route-e-e3-elementary-layer` note "do not re-attempt `(FS7)`".

## What was wrong with the no-go
The note said `(FS7)` (`∫_{T₀}^T |P(1+it)|²dt ≪ T/(R log x) + 1/(log x)²` for
`P(s)=∑_{p≍R}p^{-s}`) is out of reach because `RHTower.Sieve.dirichlet_meanValue_theorem` has error
`O(N log N)` and even Montgomery--Vaughan's `O(N)` only gives `O(1/log R)`.  True — but the second
logarithm never comes from the mean value theorem.  It comes from the **two-dimensional upper-bound
sieve on the off-diagonal pairs**, which is exactly what Matomäki--Teräväinen's Section 5 does, and
which the corpus already owned: `Sieve/RoughPairSieve` (a `SelbergSieve` for the pair form
`m(m+d)`, density `pairNu`), `Sieve/RoughPairCount.card_roughPair_le`.

## New modules (all axiom-clean, all wired into `GaloisForLFunctions.RHTower`)
- `Sieve/PrimePairCount.card_primePair_le` — a prime above the sifting range has no prime factor in
  it, so the rough-pair sieve counts prime pairs.
- `Sieve/PrimePairShiftSum.sum_inv_shiftCorrection_le` — `∑_{d≤K} ∏_{p∣d,P₁<p≤h}p/(p−1) ≤ e·K`.
  Route: expand over subsets (`Finset.prod_add`), count multiples
  (`Nat.Ioc_filter_dvd_card_eq_div`), reassemble to `∏_p(1+1/(p(p−1))) ≤ exp 1`, with the
  telescoping `∑_{2≤n≤h}1/(n(n−1)) = 1 − 1/h` proved.
- `Sieve/PrimePairAverage.sum_card_primePair_le` — the shift-uniform level budget plus the average.
- `Sieve/PrimePairNeighbour.sum_card_neighbour_le` — reusable: a symmetric near-diagonal relation
  whose pairs differ by ≤ K has total count `≤ #s + 2∑_{d≤K}#{n ∈ s : n+d ∈ s}` (diag/up/down
  `biUnion` cover).  Plus `le_add_of_log_close`: a multiplicative window of ratio `e^δ` at height
  `≤ 2R` has additive length `≤ 6Rδ`.
- `Sieve/DyadicPrimeMeanSquare.integral_normSq_dyadicPrimePoly_le` — the mean square itself, on top
  of `Sieve/GallagherAlmostDiagonal.integral_Icc_normSq_logPoly_le_count`.

## Cost of the sieve level
`card_roughPair_le`'s level constraint is `h^{2k} ≤ z` with `k ≳ e·∑_{p≤h}2/(p−2) ≍ 2e log log h`,
so the remainder is `z^{1+o(1)} = exp(C log h log log h)`; usable only for
`log h ≍ log Y/log log Y`.  The saving is therefore `(log log Y)²/(log Y)²`, not `1/(log Y)²`.  That
`(log log)²` is harmless for the E3 cards: `(FS8)`'s second term becomes `(log x)^{-2.2}/log log x`,
still `o((log x)^{-2-2ε})`.

## Still open on the two E3 cards
`(FS4)` — the Perron/minorant assembly of Matomäki--Teräväinen Theorem 1.2 — and the cofactor
card's elementary `(7)`/`(9)` unsigned squarefree harmonic estimates.

## Concurrency
Another Claude session owns the `omegaBudget`/spectral limit lane of
`matomaki-radziwill-lean-programme.md` (files `Budget*`, `Ladder*`, `OmegaBudget*`,
`SpectralParameters`, `PolylogLimits`, `AnnulusBoundUniform`, `DiscBoundUniform`,
`ContourParamMono`, `WidthEnvelopeBounds`).  Do not edit those.

## Second batch (same day): the cofactor card's `(7)`/`(9)` are CLOSED
- `Sieve/ElementaryHarmonicBounds` — `two_mul_sqrt_succ_sub_two_le_sum`, `sum_filter_dvd_eq`,
  `sum_inv_sqrt_dvd_le`, `sum_inv_dvd_le`, `sum_telescope_inv`, `sum_inv_sq_odd_le`.
  NOTE: the upper bound `∑_{n≤M}n^{-1/2} ≤ 2√M` already existed as `RHTower.sum_one_div_sqrt_le`
  (in `RHTower/PrimeMassLowerBound.lean`, namespace `RHTower`, not `RHTower.Sieve`) — reused.
- `Sieve/CoprimeSquarefreeHarmonic` — `sum_coprime_ge`, `sum_notSquarefree_le`,
  `sum_inv_coprime_squarefree_ge` (`≥ (log M)/8 − 7/8`),
  `sum_inv_sqrt_coprime_squarefree_ge` (`≥ √M/4 − 2`), under `2 ∣ Q` and `∑_{p∣Q}1/p ≤ 5/8`.
- `RHTower/RouteECofactorUnsignedMass` — parity balance for an arbitrary weight antitone above 1
  (`CofactorParity.sum_oddBase_two_mul_le_sum_parityClass`), `oddBase_eq_coprime_squarefree`,
  and the capstones `sum_inv_parityClass_ge`, `sum_inv_sqrt_parityClass_ge`.

Mechanism: `1/2 (prime 2) + 1/8 (band Mertens mass) + 1/4 (odd reciprocal squares) < 1`.
Useful reusable facts found on the way: `Aux.log_le_sum_inv`, `Aux.sum_inv_le_log` (PNT+
`Sieve/AuxResults`, namespace `Aux`); `Nat.Ioc_filter_dvd_card_eq_div`; `Finset.sum_union_inter`
(there is NO `Finset.sum_biUnion_le_sum_of_nonneg` — proved locally as `sum_biUnion_le_of_nonneg`).

## The source is located and the unique remaining core is named (2026-08-18)
`arXiv:2207.05038` = Matomäki–Teräväinen, **"Almost primes in almost all short intervals II"**.
Theorem 1.1 is the `E₂`/almost-all statement at `(log x)^{2.1}`; **Theorem 1.2** is the all-interval
bonus: `(x, x+√x(log x)^{1.55}]` contains an `E₃` number, proved "by following the proof of
Theorem 1.1 very closely".  Section 7 was not retrievable via ar5iv (document truncated).

### Numerology (my own derivation — re-derive before relying on it)
With `A = P₁P²`, main term `≍ h/((log P₁)(log x)²) ≍ √x(log x)^{-0.45}/log log x`.  Using only the
trivial `max|P₁| ≍ 1/log log x` and the now-proved `(FS7)`, the sharp-cutoff error is
`≍ √x(log x)^{-0.45}` — **exactly `log log x` times the main term**, the `log log` coming from the
`≍ log log x` dyadic blocks in `[T₀, T]` (`T/T₀ = R/T₀ ≍ log x`).  `(5.2)`'s `(log x)^{-ε/10}`
covers it.  So the **unique remaining analytic input for both E3 cards** is

    (5.2)   ∫_{T₀}^{T}|P₁(1+it)P(1+it)|²dt ≪ (T h/x)(log x)^{-2-ε/10}.

Why it cannot be cheapened: no pointwise cancellation in `P₁` (`log P₁ = 1.1 log log x`, far outside
any zero-free region for `|t| ≤ √x`); the MVT on the product `P₁P` is diagonal-dominated (length
`P₁R ≫ T`) and gives `1/(log P₁ log R)`, worse than `max|P₁|²∫|P|²`; shrinking the dyadic block does
not shrink the MVT's `N∑|a|²` term.  It is a genuine Type II estimate — Watt / Deshouillers–Iwaniec
/ Heath-Brown sparse MVT.

### Corpus assets for that next milestone (read before building)
- `Sieve/PerronShortInterval.norm_sum_Icc_sub_sum_Icc_sub_perronInterval_le` — sharp two-cutoff
  truncated Perron for a short interval, unconditional, error `B·N^σ(5(1+log M)+4(1+log N))/(πT)`.
- `Sieve/Maynard*` — a large-values layer: `huxley_heathBrown_grouped_large_values`,
  `montgomery_heathBrown_grouped_large_values_finset`, weighted/windowed variants.
- `Sieve/DirichletMeasureLargeValues` — `volume_largeValues_le` (Chebyshev level-set measure),
  `integral_norm_dirPoly_halasz`; `Sieve/DirichletLargeValuesL1` — `card_largeValues_div_le`.
- NEW `Sieve/MeanSquareLevelSplit` — `sq_le_levelSplit`, `integral_sq_le_levelSplit`: the dyadic
  level-set split `∫_E f² ≤ V₀²|E| + ∑_{j<J}(2^{j+1}V₀)²|{f ≥ 2^jV₀} ∩ E|`, the shape `(5.2)`
  consumes.  Axiom-clean, wired.

## CORRECTION (same day, later): the deficit is NOT log log x
The "exactly one log log x" claim recorded above is an artefact of the sharp-cutoff Perron kernel
`≍ x/|t|` and the `≍ log log x` dyadic blocks.  With a smooth window in the multiplicative variable
the block sum disappears entirely and the whole all-interval E₃ theorem reduces to ONE inequality:

    (★)  ∫_{1 ≤ |t| ≤ T₀}|P₁(1+it)||P(1+it)|²dt  <  (1/2)·P₁(1)·P(1)² ,

with the main term supplied by the long-window count (PNT on intervals of length ≍ x).  No Type II
input is used in the reduction.

Bounding |P₁| by its sup reduces (★) to a statement about the LARGE polynomial alone,
`∫_{1≤|t|≤T₀}|P|² < (1/2)P(1)²`, which is FALSE by a factor ≍ 25: the near-diagonal prime-pair term
`2T₀R^{-2}#{0<|p−p'| ≤ R/T₀} ≍ 4/(log R)²` is INDEPENDENT of h (shortening the window raises T₀ and
lowers the pair range in exact proportion) and already exceeds `P(1)² ≍ 0.48/(log R)²`.  A Selberg
majorant with transform in [-δ,δ] contributes `(1/δ)(2δ/(log R)²)` — the same irreducible term.  So
no window, no h, no constant-chasing closes it.

(★) itself is true with margin `≍ (P₁/log P₁)^{1/2} = (log x)^{0.55+o(1)}`: on |t| ≥ 1 the short
polynomial has typical size `(P₁ log P₁)^{-1/2}`, not its sup.  All the loss is in the sup /
Cauchy–Schwarz step.

### The exact open core, after the L¹ level split
    ∫_{S_V}|P|² ≤ (small const)·∫_{1≤|t|≤T₀}|P|²,   S_V = {t ∈ [1,T₀] : |P₁(1+it)| ≥ V ≍ P₁(1)}.
`|S_V|/T₀ ≍ log P₁/P₁ = (log x)^{-1.1+o(1)}` IS provable (spaced-point large values:
`RHTower.LargeValuesDpoly`, `RHTower.WellSpacedSubset`), but small measure does not bound the
|P|²-mass: |P|² is spiky, its whole mass sits on a set of measure O(1) while |S_V| ≍ T₀(log x)^{-1.1}.
The separation is arithmetic — that is the Type II content.

### Dead routes for the open core (do not re-attempt)
- adapted moments for P₁ (`Sieve/PrimePowerSupport`): `P₁^ℓ ≤ T₀` caps the saving at `T₀^{-0.09}`,
  a power saving where BOUNDED measure is needed.
- moments of `P₁^kP^j`, j ≥ 1: `R > T₀`, so the MVT length term `P₁^kR^j` cancels the gain.
- Hölder with `∫|P|⁴`: that integral is T₀-independent while |S_V| ∝ T₀.
- shifted-pair expansion of `∫|P₁P|²`: its near-diagonal term is T₀-independent and the same order
  as the trivial `max|P₁|²∫|P|²`, so the 2-D sieve gives nothing here (it was decisive for (FS7)
  only because there the competitor was the MVT, not a sup).

### New Lean asset from this cycle
`Sieve/MeanSquareLevelSplit.integral_mul_le_levelSplit` — the L¹ level split
`∫_E f·g ≤ V₀∫_E g + M∫_{E∩{f≥V₀}} g` (0 ≤ f ≤ M, g ≥ 0, 0 ≤ V₀), the form (★) consumes; it does
not square the short factor, unlike Cauchy–Schwarz.  Axiom-clean, wired.
