# The GHS route to sharp Halász, and Gallagher's lemma in the useful direction (2026-08-07)

## The proof map is now known and written down

`docs/drafts/pipeline/1-in-progress/halasz-ghs-proof-map.md` records the full skeleton of
Granville–Harper–Soundararajan, arXiv:1706.03755 (sharp Halász, "more intuitive proof"), with the
companion arXiv:1706.03749. Four steps: (1) the log recursion — DONE in the corpus as
`RHTower.Sieve.norm_sum_Icc_mul_log_sub_sum_primes_le'`; (2) a second application giving a triple
convolution; (3) a dyadic partition of the prime range into `P_k = (x^{1−e^{1−k}}, x^{1−e^{−k}}]` —
this is where Halász's `1+M` prefactor comes from, it is the *count of scales*; (4) truncated Perron +
Cauchy–Schwarz with a prime-supported mean square.

Their **Lemma 1** is the input my earlier no-go 3 named as missing:
`∫_{−T}^T |∑_{T²≤n≤x} a_n Λ(n) n^{−1−it}|² dt ≪ ∑ |a_n|² Λ(n)/n`.
GHS state explicitly that the standard Dirichlet mean value theorem cannot give this — it yields
`Λ(n)²`, not `Λ(n)`. The proof is a smooth weight plus Brun–Titchmarsh in short intervals.

## Built: Gallagher's lemma in the mean-value direction

`RHTower/Sieve/GallagherReverse.lean` (green, axiom-clean, wired):
`∫_{Icc (-W) W} ‖logPoly a s w‖² ≤ (5/(4δ²)) ∫_ℝ ‖logWindowSum a s δ u‖²` whenever `2πδW ≤ 1`.

The corpus's `gallagher_identity` is an *equality*, so the only missing piece was a lower bound for the
Fejér weight on the central range: `le_fejerWeightAt_re` (`≥ (4/5)T` for `|TL| ≤ 1`) and
`le_fourier_triC_re` (`≥ (4/5)δ²` for `|2πδw| ≤ 1`), both from `2 − 2cos θ ≥ (4/5)θ²`
(mathlib `Real.cos_bound`). Do not rebuild the Fejér/triangular layer: `TriangularKernel`,
`TriangularInversion`, `TriangularIntegralForm`, `FejerSymmBound`, `FejerBounds`, `GallagherLemma`,
`LogWindowKernel` already own the transform, its closed form `2(1−cos TL)/(TL²)`, nonnegativity, the
cap and the decay.

Next brick: GHS Lemma 1 = this + Cauchy–Schwarz per window + the corpus's Brun–Titchmarsh count
(`Sieve/BrunTitchmarsh`, `Sieve/PrimeWindowUpper.card_primes_Ioc_le_explicit`).

## Update: the arithmetic side of GHS Lemma 1 is built

`RHTower/Sieve/GallagherAlmostDiagonal.lean` — `logNeighbourCount s δ n = #{m ∈ s : |log n − log m| < δ}`,
`integral_normSq_logWindowSum_le_count` (no hypothesis on δ at all), and
`integral_Icc_normSq_logPoly_le_count` (the mean value theorem with the count as its only arithmetic).

`RHTower/Sieve/PrimeLogWindowCount.lean` — `logNeighbourCount_le_sieve` discharges the count for a prime
support using the corpus's `RHTower.Sieve.card_prime_Ioc_le` (Sieve/PrimeInterval; the clean
Brun–Titchmarsh shape with `selbergFibreError z Y + z`), and
`integral_Icc_normSq_logPoly_le_prime_sieve` assembles the prime-supported mean value theorem.

The δ cancels: Gallagher contributes `5/(4δ)` and the window length contributes `e^δ − e^{−δ} ≍ 2δ`.
With `log Y ≍ (log p)/3` the per-prime weight is `≍ (log p)/p` — GHS Lemma 1's `Λ(n)/n`, not `Λ(n)²/n`.

## Update 2: the Lorentzian-weighted mean value theorem (no hypotheses)

`RHTower/Sieve/LorentzianMeanSquare.lean`:
`∫_ℝ ‖logPoly a s w‖²/(1+w²) dw ≤ (25π/2) ∑_{n ∈ s} (logNeighbourCount s (1/(2π)) n) ‖a n‖²`
for arbitrary `a : ℕ → ℂ` and `s : Finset ℕ` — **zero hypotheses**.

Built from the corpus's dyadic annulus scaffolding (`GallagherDyadicTail.dyadicAnnulus`,
`pairwise_disjoint_dyadicAnnulus`, `iUnion_dyadicAnnulus`) plus mathlib's `hasSum_integral_iUnion`,
`Summable.tsum_mono` (NOT `tsum_le_tsum` — renamed), `hasSum_geometric_of_lt_one`,
`setIntegral_mono_set`. The mechanism: on annulus `k` the weight is `≤ 4^{-k}` and the mean value
theorem at `T = 2^{k+1}` costs `2^k`, so the series is geometric; `logNeighbourCount_mono` charges every
block to the unit-scale count.

This is `I₂` of GHS step 4 over the whole line, so no truncated Perron formula is needed for the `B_k`
factor. What still needs a Perron passage is the *outer* extraction of `S_k(x)` from its Dirichlet
series; the corpus's exact smoothed identity (`SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral`,
kernel Lorentzian by `exists_bound_mellin_smoothWeight_line`) is the candidate, with a smoothing scale
`H = N/(log N)³` making the sharp-cutoff error `O(N/log N)`.

## Update 3: GHS Lemma 1 is built, over the whole line

- `RHTower/Sieve/LorentzianDirPoly.lean` — the Lorentzian MVT in the `dirPoly` frequency variable via the
  corpus's `logPoly_eq_dirPoly`; substitution `t = 2πw` costs `2π`, weight improves (`1+4π²w² ≥ 1+w²`).
  Change of variables: `MeasureTheory.Measure.integral_comp_mul_left` (inside `namespace Measure`).
- `RHTower/Sieve/LorentzianPrimeSupport.lean` — `logPoly_eq_logPoly_filter` (drop vanishing coefficients)
  turns the index-set count into the **support** count; for a prime-supported coefficient sequence the
  sieve then discharges it. `integral_lorentz_normSq_logPoly_le_prime_sieve` IS GHS Lemma 1 with no
  truncation of the frequency line.
- `RHTower/Sieve/MertensBlock.lean` — Mertens' first theorem on a block `(y, z]`, by subtracting two
  instances of `RHTower.Mertens.mertens_first_prime`. Needed by GHS steps 2 and 3.
  `Finset.Icc_union_Ioc_eq_Icc` does NOT exist; prove the split by `ext a; simp [...]; omega`.

Remaining in the GHS skeleton: steps 2-3 (second recursion application + dyadic prime partition, both
Mertens bookkeeping) and the outer Perron passage for `S_k(x)`.

## Update 4: steps 2 and its arithmetic are done

- `RHTower/Sieve/MultiplicativePrimeAverage.lean` — the averaged recursion (divide the prime-only
  recursion by `log N`) and its second application, giving the double prime average (triple convolution)
  with error `∑_{p ∈ P} log p (9+T)⌊N/p⌋/log⌊N/p⌋`.
- `RHTower/Sieve/PrimeLogQuotientSum.lean` — that error is `O(N log log N)`:
  `∑_{p, ⌊N/p⌋≥2} (log p)/(p log⌊N/p⌋) ≤ ((log 3 + 2C)/log 2)(1 + log⌊log₂N⌋)`.
  **Proof mechanism worth remembering:** group primes by `Nat.log 2 ⌊N/p⌋`. The fibre is an interval of
  integers with integer endpoints because `2^j ≤ ⌊N/p⌋ ↔ p ≤ ⌊N/2^j⌋` (`Nat.le_div_iff_mul_le` twice);
  the endpoints are within a factor 3 (`⌊N/2^j⌋ ≤ 2⌊N/2^{j+1}⌋+1`), so `MertensBlock` gives mass
  `≤ log 3 + 2C` per fibre; `log⌊N/p⌋ ≥ j log 2` on the fibre; `Finset.sum_fiberwise_of_maps_to` plus the
  corpus's `sum_Icc_one_div_le_one_add_log` (Sieve/HarmonicLogBound — do NOT restate it, I did and had to
  delete it) give the harmonic sum. No `rpow` anywhere.
- Trap: `∀ x ∈ s with p, ...` is not valid binder syntax; write `∀ x ∈ Finset.filter p s, ...`.

## Update 5: steps 1-3 of the GHS skeleton are complete

- `Sieve/TripleConvolutionWindow.lean` — `norm_inner_double_le` (inner double sum ≤ M(log M + C)) and
  `norm_window_triple_le`: one dyadic window of the triple convolution is `O(N(n−m+1))`. The inner
  `log M` cancels the outer `1/log⌊N/p⌋`, so the window contribution IS N times the window's Mertens mass.
- `Sieve/DoubleAverageSplit.lean` — `filter_large_quotient_eq` (`2^n ≤ ⌊N/p⌋ ↔ p ≤ ⌊N/2^n⌋`, so the
  large-quotient primes are an initial segment), `sum_split_at_quotient_threshold`, `doubleAverageTerm`,
  and `norm_double_average_sub_initial_le`: the double average equals its restriction to `p ≤ ⌊N/2^n⌋`
  plus `O(N n)`.

**Design win worth remembering:** GHS's summation over double-exponential blocks
`(x^{1−e^{1−k}}, x^{1−e^{−k}}]` is unnecessary. Because the quotient-window mass bound is additive in
`n − m`, the union of all discarded blocks is a *single* window `2 ≤ ⌊N/p⌋ < 2^n`, bounded in one step by
`O(N n)`; their discarded part `xL/100` is the case `n ≍ L`. No real powers appear anywhere in steps 1-3.

Only step 4's outer Perron passage remains (extract the initial-segment sum from its Dirichlet series);
candidate is `SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral` with `H = N/(log N)³`.

## Update 6: step 4 needs truncated Perron; the smoothing routes are dead

All of step 4's devices are built (`TripleConvolutionPerron`, `WeightedCauchySchwarz`,
`LorentzianPrimeSupport`, `SmoothWeightWindow` — the last now has the sharper
`norm_weighted_sub_partialSum_le_sqrt`, `≤ √H·√(window ℓ²)`, committed by another session with a missing
`Mathlib.Algebra.Order.Chebyshev` import that I fixed).

**No-go recorded on the card:** for the triple convolution `‖d(n)‖ ≲ (log x)²d₃(n)`, every *smoothed*
route needs a short-interval divisor estimate (Shiu, or Piltz with a power-saving error): fine smoothing
`H = x/(log x)^A` leaves `∑_{x<n≤x+H}d₃(n)`, and coarse smoothing (`H ≍ x`, i.e. PNTPlus's exact
`x^s/(s(s+1))` Cesàro formula) leaves `∑_{n≤x}d(n)n/x ≍ x(log x)⁴`, which is not small.  Higher-order
Riesz means return to the window sum.

Only **truncated Perron with the `1/s` kernel** avoids it: its error is the *global*
`(x^σ/T)∑_n‖d(n)‖/n^σ ≍ x(log x)^c/T`, needing no short-interval input.  So the one remaining analytic
development is Perron's lemma,
`|(1/2πi)∫_{σ−iT}^{σ+iT} y^s ds/s − 1_{y>1}| ≪ y^σ min(1, 1/(T|log y|))`,
by contour shift plus the residue at `s = 0`.  PNTPlus's `Rectangle`/`ResidueCalcOnRectangles` machinery
is reusable; its own `PerronFormula.lean` is the `x^s/(s(s+1))` kernel and is NOT usable here.
