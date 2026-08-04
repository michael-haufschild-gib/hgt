# MR splice: wide-range mean square for the factorized Möbius polynomial

- **ID:** `mr-splice-wide-range-mean-square`
- **Stage:** 1-in-progress
- **Type:** THEOREM PROGRAMME (analytic half of the Matomäki–Radziwiłł input)
- **Consumer:** `RHTower/Sieve/MRInterface.MRBilinear` and, through it, the Route E sign-class
  density theorems (`tendsto_signClass_of_MR`)
- **RH used:** no.  **External novelty claimed:** none — this is the formalization programme for
  known Matomäki–Radziwiłł-type technology; every statement is unconditional.

## Frozen target

Produce, unconditionally and with explicit constants, a frequency mean square

```text
∫_{|t| ≤ T} ‖F₁(t)·F₂(t)‖² dt ≤ (trivial size)/(saving → ∞)
```

for the Ramaré-factorized Möbius block polynomial (long factor `F₁`, dyadic prime factor `F₂`),
on ranges `T` wider than any zero-free region reaches, and feed it through
`GallagherSplitIntegral.gallagher_split` to a short-interval Möbius variance at window exponents
strictly below the contour floor `L ≥ N·exp(−c(log N)^{1/10})` recorded in
[[contour-route-is-long-windows-only]].  Terminal consumer: `MRBilinear μ hh` for an explicit
window law `hh`.

## Why the splice closes (mechanism)

`DirichletProductSplit` / `DirichletConvSplit` give, for any threshold `V`,

```text
∫ |F₁F₂|² ≤ V²·∫|F₁|² + B₁²B₂²·meas{|F₂| ≥ V},
```

with `∫|F₁|²` controlled by the mean value theorem (`DirichletIntegralMeanValue`) and the
exceptional measure by the sixth moment.  The sixth moment's fibre constant is the load-bearing
quantity: the general bound (`CubeFibreDivisorBound`) loses `C_ε N^ε`, which poisons the exponent
bookkeeping at polynomial windows.

## 2026-08-04 completed piece: prime support removes the fibre loss

`RHTower/Sieve/PrimeCubeSupport.lean` proves, unconditionally:

- `sum_normSq_convCube_le_of_support` — the cube's `ℓ²` bound through an arbitrary coefficient
  support: only fibre points with all three coordinates in the support enter Cauchy–Schwarz;
- `cubeFibreOn_primeSupport_card_le_nine` — a triple of primes with a fixed product is one of at
  most nine: the first two coordinates lie among the ≤ 3 prime factors of the anchored product
  (uniqueness of factorization), the third is determined;
- `sum_normSq_convCube_le_of_prime_support` — `∑‖(F₂³)-coefficients‖² ≤ 9·(∑‖b‖²)³`;
- `volume_largeValues_sixth_le_of_prime_support`, `volume_largeValues_sixth_symm_le_of_prime_support`
  — the level-set bounds

  ```text
  V⁶·|{t ∈ [-T,T] : |F₂(t)| ≥ V}| ≤ 2(T + 4·(2P)³(1+log(2P)³))·9·(∑_p |b_p|²)³,
  ```

  with the absolute constant `9` in place of `C_ε N^ε`.

For a dyadic prime range `(P,2P]` with unit coefficients, `∑|b_p|² ≍ P/log P`, so for `T ≤ P³`
the exceptional measure is `≪ (log P)⁻³·(P/V)⁶` — the clean prime-polynomial moment the MR
mechanism runs on.

## Staged plan (each stage numerically pre-certified before Lean)

1. **[DONE]** prime-support sixth moment, absolute fibre constant.
2. Parameter balance for the splice: choose `V`, `T`, dyadic `P`-ranges; certify with a numeric
   sweep (mpmath/python) that the good and exceptional terms both beat the trivial size for an
   explicit window exponent `θ < 1`; record the certified exponents here before any Lean.
3. The Ramaré cross-term bookkeeping: identify the corpus's factorization output
   (`RamareFactorization`, `DirichletBilinear.dirPoly_mul_eq_dirPoly`) with the `F₁F₂` shape on
   each dyadic block; sum over blocks.
4. Gallagher passage (`gallagher_split` integral form) to the short-interval variance.
5. Blocks/normalization to `MRBilinear μ hh` at the certified window law.

## Hostile falsifiers

- The frequency-range test of [[contour-route-is-long-windows-only]] must be recomputed at stage 2:
  the splice must cover `W ≳ N/L` for the claimed window `L`, with no pointwise-bound smuggling.
- The trivial sups `B₁, B₂` may only be used on the exceptional set; any use on the whole range
  reverts to the mean value theorem's `σ ≥ 3/4` wall.
- No parameter may be chosen after inspecting a divisor or zero: all choices are functions of
  `N, L` alone.

## Log

- 2026-08-04 — card created; stage 1 built and verified
  (`lake env lean` pass; axioms `propext, Classical.choice, Quot.sound`).

## 2026-08-04 stage-2 balance certified: single split caps at the mean-value wall

Numeric sweep over `θ ∈ [0.40, 0.60]`, `α = log_N P ∈ [0.05, 0.65]`, threshold
`V = P/(log P)^A`, `A ∈ {0.3, 0.45, 1, 2}`, at `N = 10³⁰`, using the exact constants of the
built lemmas (symmetric MVT for the long factor, prime sixth moment with fibre constant 9 for
the short factor, trivial sups on the exceptional set):

```text
θ = 0.40:  best max(good, exc)/N² ≈ 9·10¹²   (a positive power of N over budget)
θ = 0.49:  ≈ 4·10⁷                            (still a power of N)
θ = 0.51:  ≈ 3·10⁶  → θ = 0.60: ≈ 3·10²       (polylog-sized overshoot only)
```

Symbolically: the good term forces `P ≪ N^{2θ−1}·(log)^{2A}`, so a nontrivial dyadic prime scale
exists only for `θ > 1/2` — the single-threshold split with `sup²·measure` on the exceptional set
re-derives the mean-value wall (with polylog overhead) and cannot cross `θ = 1/2`.

**Consequence for stage 3 (next Lean unit): the double split.**  On the exceptional set
`E = {|F₂| ≥ V}` the long factor must be paid by its own level-set structure, not by its sup:

```text
∫_E |F₁|² ≤ V₁²·meas(E) + ∫_{{|F₁| ≥ V₁}} |F₁|²,
```

with the second term bounded by layer cake against the (sixth-moment or mean-value) level-set
measures of `F₁`.  This restricted-second-moment lemma is the exact mechanism by which
Matomäki–Radziwiłł pass below the wall; the constant-relative threshold regime
(`V = εP/log P`, exceptional measure `≲ ε⁻⁶(log P)³`) identified by the sweep is where it must
be applied.  All ingredients are corpus-owned; no new analytic input is required for the lemma
itself.

- 2026-08-04 — stage 2 closed (this section); stage 3 statement frozen.

## 2026-08-04 stage-2b correction: the false wall was the ℓ¹ Gallagher tail

The stage-2 freeze of the double split was premature; the extended sweep kills it in the same
`W = (N/L)²` budget (still a positive power of `N` over budget for every `θ < 1/2`, with either
`sup²·meas` or a fourth-moment tail on the long factor).  Interrogating the failure located the
actual obstruction, and it is not in the split at all:

**The corpus's Gallagher passage bounds the far frequencies by the ℓ¹ tail `M₂·2/(π²W)`, which
forces `W ≍ (N/L)²`; every split architecture then carries an `N`-power deficit below `θ = 1/2`.
But the Gallagher weight itself decays: `norm_fourier_triC_le` gives the full
`2δ²/(1+(δπw)²) ≤ 2/(π²w²)`.  Splitting the far range `|w| ≥ W` dyadically and paying each block
with the mean value theorem replaces the ℓ¹ tail by**

```text
∑_{T = 2^k W} (2/(π²T²))·(T + 4N(1+log N))·N  ≪  N/W + (N/W)²·log N,
```

**which at `W = N/L` is `O(L² log N)` — polylog-free.  The `(N/L)²` requirement disappears.**

### Certified power-clean corridor

Re-running the balance under `W = N/L`, prime scale `P³ ≍ W`, constant-relative threshold
`V = εP/log P` (`ε = 1/log N`), at `N = 10³⁰`:

```text
θ ∈ {0.30, 0.40, 0.50, 0.60, 0.75}:
  good/N²      ≈ (log N)^{-1.4…-0.9}      (below budget)
  far-tail/L²  ≈ (log N)^{1.0}            (no N-power)
  exceptional  ≈ (log N)^{9.4…8.9}·N⁰     (no N-power)
```

No power-of-`N` obstruction remains anywhere in `θ ∈ (1/4, 1)` — in particular across the whole
Route E marker corridor `(1/2, 3/4]`.  Below `θ = 1/4` the single prime scale fails
(`P³ ≍ W` collides with the long factor's diagonal) and iterated ranges — genuine MR — are
required.  The entire remaining fight in the corridor is a `log`-power fight:

- the diagonal `log N` (Gallagher tail and MVT diagonal), and
- the exceptional `ε⁻⁶·(log)³⁺` from the sixth moment at constant-relative threshold,

to be beaten by the built Halász layer (`MoebiusUniformFrequency`: distance saving
`log log z − 7 log log T − C`, i.e. `(log)`-power pointwise savings off one exceptional
frequency) — exactly the regime that layer was built for.

### Revised stage 3 (frozen)

- **3a `[NEXT LEAN UNIT]` — weighted Gallagher far tail.**  In `GallagherSplitIntegral`'s
  framework, replace the ℓ¹ tail by the dyadic weighted mean value:

  ```text
  ∫_ℝ 𝓕(triC δ)(w)·|F(w)|² dw
    ≤ 2δ²·∫_{|w|≤W}|F|² + (2/π²)·∑_{k≥0} (2^k W)^{-2}·∫_{|w|≤2^{k+1}W}|F|²,
  ```

  with each block integral paid by the symmetric mean value theorem; conclude the variance bound
  with frequency budget `W = N/L` and error `O((N/W + (N/W)² log N)·∑|aₙ|²/N)`-shape.  All
  ingredients corpus-owned (`norm_fourier_triC_le`, `integral_Icc_normSq_dirPoly_symm_le`);
  no arithmetic input.
- **3b — the log-power fight on the exceptional set**: splice `MoebiusUniformFrequency` into the
  product split's good set and the prime sixth moment (fibre 9) into its exceptional set, per
  dyadic prime scale `P ≍ (N/L)^{1/3}`; target an explicit `(log)^{-δ}` saving in the corridor.
  Pre-certify the log bookkeeping numerically before Lean.

## Log (continued)

- 2026-08-04 — stage 2b closed: ℓ¹-tail identified as the false wall; weighted dyadic tail
  certified power-clean; corridor `θ ∈ (1/4, 1)` certified free of `N`-power obstructions;
  stage 3a/3b frozen.  Stage-1 module built (`lake build` 8801 jobs) and axiom-audited clean.

## 2026-08-04 stage 3a closed: the dyadic far tail is formalized

`RHTower/Sieve/GallagherDyadicTail.lean` (wired into `RHTower.lean`; targeted build pass; axioms
only `propext, Classical.choice, Quot.sound`):

- `dyadicAnnulus`, `exists_dyadic_scale`, `iUnion_dyadicAnnulus`,
  `pairwise_disjoint_dyadicAnnulus` — the annuli `{2^k W ≤ |w| < 2^{k+1} W}` tile `{|w| ≥ W}`;
- `gallagher_split_integral_dyadic` — **the ℓ¹ tail is gone**: for ANY real `α, β` (no sign
  hypotheses; the linter proved them unnecessary) with
  `∫_{|w|≤T} ‖F‖² ≤ αT + β` for all `T ≥ W`,

  ```text
  ∫_ℝ ‖window sums‖² du ≤ 2δ²(αW + β) + 4α/(π²W) + 4β/(3π²W²),
  ```

  each annulus paid through the sharp weight decay `1/(π²w²)` (`GallagherTail.lean`, constant 1 —
  found in-tree during the build, halving the certified constants) and summed by the geometric
  series;
- `gallagher_meanValue_dyadic_le` — instantiated with the mean value theorem
  (`α = 2Σ₂`, `β = 4N(1+log N)Σ₂/π`): the far tail carries the mean-square mass `Σ₂ = ∑‖aₙ‖²`,
  never the ℓ¹ mass `(∑‖aₙ‖)²`.

With `W ≍ N/L` and `Σ₂ ≍ N` this is the `O(L² log N)`-tail bound certified by the stage-2b sweep,
now unconditional in Lean.  The frequency budget for the arithmetic input is henceforth `N/L`,
not `(N/L)²`.

**Next (stage 3b, unchanged):** the log-power fight — product split at `W = N/L` with the
prime-support sixth moment (fibre 9) on the exceptional set and the Halász uniform-frequency
saving on the good set; pre-certify the log bookkeeping numerically before Lean.

- 2026-08-04 — stage 3a built and verified.
