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

## 2026-08-04 stage 3b as frozen is FALSIFIED by pre-certification

The full numeric model — Ramaré designated range `(P₁, z]` with Brun rough remainder
`(9·log P₁/log z)²` and square part, weighted pointwise Cauchy–Schwarz over dyadic prime blocks
(harmonic weights `H/h_P`, `∑ h_P/H = 1`), per-block double split with the fibre-9 prime sixth
moment, stage-3a Gallagher far tail — gives, at its optimum over
`θ ∈ {0.55, 0.6, 0.7}`, `log P₁ ∈ (log N)^{0.5..0.8}`, `z = N^{0.05..0.2}`, all thresholds:

```text
variance/L² ≈ (log N)^{+2.8}   —   DIVERGES.
```

**The certified obstruction.**  The dominant term is the exceptional-set tail of the long factor:

```text
B₂²·∫_{|F₁| ≥ V₁}|F₁|²  ≈  B₂²·(N/P)²·log N·log K₁
```

by the mean-value layer cake — after the harmonic weights this costs `≈ log N · log log N`
per block-sum and nothing in the built toolkit pays for it.  Verified escape attempts, both dead:

- ℓ-adapted high moments of the prime factor (`(2P)^ℓ ≍ T`): at `log P ≍ (log N)^{0.6}` the
  `ℓ!·(log P)^{(1+2a)ℓ}` mass costs `exp((log N)^{0.4+o(1)})`; at `log P ≍ log N` the moment
  degenerates to a fixed moment and returns fixed log-powers — never enough to beat the
  `sup²`-free requirement.
- pointwise contour control of `F₁` reaches only `|w| ≤ exp((log N)^{1/10})`
  ([[contour-route-is-long-windows-only]]); the mid-range `exp((log N)^{1/10}) ≤ |w| ≤ N/L`
  is untouched.

**Surviving requirement (the real MR heart).**  The level sets of the long μ-cofactor factor
`F₁` must be controlled *arithmetically*, by re-factorizing `F₁` itself at a lower designated
range and iterating — the Matomäki–Radziwiłł range induction `[P₁,Q₁], [P₂,Q₂], …` over
`≈ log log N` scales, where each range's exceptional set is paid by the next range's prime
polynomial.  No single-split or double-split architecture over one range can close, at any
threshold choice: this is now certified, not suspected.

**Next unit (stage 3b′): the induction model.**  Build the numeric model of the full MR range
induction (their Sections 3–5 skeleton): the scale schedule `log P_j ≍ ρ^j`, per-scale
moment-adapted `ℓ_j`, the induction inequality tying scale `j`'s exceptional measure to scale
`j+1`'s polynomial, and the terminal scale paid by `MoebiusUniformFrequency`.  Only after the
model certifies an explicit `(log)^{-c}` does any Lean statement get frozen.  The generalized
prime-fibre mass bound `∑|coeffs(F₂^ℓ)|² ≤ ℓ!·(∑|b_p|²)^ℓ` (variable `ℓ`, extending the fibre-9
cube module) will be an ingredient of every certified variant, but is not licensed until the
induction model closes.

- 2026-08-04 — stage 3b falsified as frozen; obstruction and surviving induction shape recorded.

## 2026-08-04 stage 3b″: the MR-note architecture replaces the induction guess

Fetched and read the actual Matomäki–Radziwiłł expository note (arXiv:1502.02374), which proves
exactly the corridor target (`∑_{x≤n≤x+X^δ} λ(n) = o(X^δ)` a.e., variance `≪ X/(log X)^{1/3−ε}`)
in 12 self-contained pages.  The real mechanism for polynomial windows needs **neither** the range
induction guessed in 3b′ **nor** any product-split/sixth-moment machinery:

**Route (A) — note §4 (λ-specific).**  Parseval (their Lemma 4: ranges `[0, X^{1−δ}]` plus dyadic
`max_{T>X^{1−δ}}(X^{1−δ}/T)∫_T^{2T}`, = our stage-3a shape) → `t ≤ (log X)^{10}` by the twisted
PNT bound (corpus owns, stronger) → ONE Ramaré range `[P, Q]`, `P = exp((log X)^{2/3+ε})`,
`Q = X^{δ/3}`, rough remainder by sieve density `log P/log Q` **inside the MVT coefficient mass**
(my earlier model mis-charged this as a squared per-window Brun count — the correct cost is
linear, fundamental-lemma constant) → `H = (log X)^5` short-range splitting, Cauchy–Schwarz cost
`(H log(Q/P))²` → **the short prime polynomial is pointwise `≪ (log X)^{-A}` for ALL
`(log X)^{10} ≤ |t| ≤ X`** via Perron + `log ζ` on the Vinogradov–Korobov line (their Lemma 2).
*Blocker for the corpus:* Lemma 2 needs a zero-free region `σ ≥ 1 − c/(log t)^κ` with `κ < 1`;
the corpus's 3-4-1/DLVP layer is `κ = 1` and provably cannot feed it (the required
`log P ≥ (log X)^κ·log log X` collides with `log P ≤ log Q ≪ log X`).  A Littlewood-quality
region (`c·log log t/log t`) would still yield a `(log log X)^{-1}` saving; Vinogradov–Korobov
gives `(log X)^{-1/3+ε}`.  Either is a major classical formalization (Weyl/Vinogradov sums).

**Route (B) — note appendix (general `f`, no zero-free region at all).**  Their Theorem 3:
saving `(log X)^{-1/48}` with `H = (log X)^{1/48}`, `log P = (log X)^{1−1/48}`,
`log Q = log X/log log X`, via [4, Lemmas 3, 8, 11, 12, 14]:
split `t`-set at `|Q_{j,H}(1+it)| ≶ (log X)^{-100}`; small side by MVT; large side by a
well-spaced set `𝒯` with `|𝒯| ≪ exp((log X)^{1/48+o(1)})` ([4, L8]: adapted-moment count for the
SHORT prime polynomial), each point paid by the Halász sup for the long factor
(`≪ (log X)^{-1/24}`, [4, L3] — the corpus's `MoebiusUniformFrequency` layer is this bound's
mechanism) times the prime large-value refinement ([4, L11]) whose spacing factor
`exp(−(log X)^{1/5})` absorbs `|𝒯|` since `1/5 > 1/48`.  **Every ingredient is in the corpus's
existing technology class** (mean values, spaced large-value counts, Halász distance) — no new
zero-free region.

**Frozen stage 3b″ (route B), missing-piece list against the corpus:**
1. `[LICENSED — first Lean unit]` variable-`ℓ` adapted moment count for short prime polynomials
   (range ratio `e^{1/H}`): the ℓ-fold analogue of `PrimeCubeSupport` (fibre of an ordered
   ℓ-tuple of primes with fixed product ≤ ℓ^{ℓ−1}; mass `≤ ℓ!·(∑|b_p|²)^ℓ`), feeding the
   spaced-count bound `|𝒯| ≪ exp((log X)^{1+o(1)}/log P)`.  Consumer now certified.
2. Halász–Montgomery duality / prime large-value refinement with the spacing decay ([4, L11]) —
   audit `DirichletLargeValuesCount`, `AlmostOrthogonality`, `CharacterSeparation` first.
3. Halász sup for the sharp long factor `F_{j,H}` ([4, L3]) — bridge from `MoebiusUniformFrequency`
   (smooth Euler sums) to sharp cutoffs; this is the known "mean-value Halász" frontier.
4. Ramaré + short-range splitting assembly ([4, L12] = note (3)+(5)) — corpus has all pieces.
5. Multiplicative Parseval ([4, L14] / note Lemma 4) — stage 3a covers the additive shape;
   decide additive vs multiplicative normalization at assembly time.

- 2026-08-04 — 3b′ induction guess superseded by the note's actual architecture; route (B)
  frozen; unit 1 licensed.

## 2026-08-04 route-B unit 1 built: the variable-ℓ adapted moment

`RHTower/Sieve/PrimePowerSupport.lean` (wired into `RHTower.lean`; targeted build 8802 jobs;
axioms only `propext, Classical.choice, Quot.sound`; zero warnings):

- `powIdx`, `powIdx_val_add_one` — the `ℓ`-tuple product index in `Fin (N^ℓ)`;
- `dirPoly_convPow` — **the `ℓ`-th power of a Dirichlet polynomial is a Dirichlet polynomial**
  (`Finset.prod_univ_sum` over the pi-type, phases multiplied via `Real.log_prod` and
  `Complex.exp_sum`);
- `sum_normSq_convPow_le_of_support` — the power's `ℓ²` mass through an arbitrary support;
- `powFibreOn_primeSupport_card_le` — a tuple of primes with fixed product has every coordinate
  among the ≤ `ℓ` anchor primes (`Prime.dvd_finsetProd_iff`), so the prime-supported fibre has
  at most `ℓ^ℓ` points (fibre ⊆ `piFinset` of the anchor image);
- `sum_normSq_convPow_le_of_prime_support` — mass `≤ ℓ^ℓ·(∑‖b_p‖²)^ℓ`;
- `largeValues_pow_setOf`, `volume_largeValues_pow_symm_le_of_prime_support` — the adapted-moment
  level-set bound

  ```text
  V^{2ℓ}·|{t ∈ [-T,T] : |F(t)| ≥ V}| ≤ 2(T + 4N^ℓ(1+log N^ℓ))·ℓ^ℓ·(∑_p ‖b_p‖²)^ℓ,
  ```

  for every `ℓ ≠ 0` — the sixth moment (`ℓ = 3`, fibre 9) is now the special case.

This is the counting engine for the route-B well-spaced set `𝒯`: with `N` the short prime range
`e^{(j+1)/H}` and `ℓ ≈ log T/(j/H)` so that `N^ℓ ≍ T`, the `ℓ^ℓ = exp(ℓ log ℓ)` fibre cost is
exactly the tolerable `exp((log X)^{1/48+o(1)})` loss of [4, Lemma 8].

**Next units:** (2) the spaced-count corollary of this bound (from measure to well-spaced point
counts — the corpus's `DirichletLargeValuesCount` pattern at variable `ℓ`); then the [4, L11]
duality refinement audit; then the numeric re-certification of the full route-B bookkeeping with
these corpus constants before assembly.

- 2026-08-04 — unit 1 built and verified.

## 2026-08-04 route-B unit 2 built: the adapted-moment well-spaced count

`RHTower/Sieve/PrimePowerLargeValuesCount.lean` (wired; build 8803 jobs; axioms only
`propext, Classical.choice, Quot.sound`; zero warnings; first-pass compile):

- `card_largeValues_pow_le` — for a prime-supported vector, any `ℓ ≠ 0`, and `R + 1` values
  `≥ V` at `δ`-spaced points of `[δ/2, T − δ/2]`:

  ```text
  (R+1)·V^{2ℓ} ≤ (T + 4N^ℓ(1+log N^ℓ))·(δ⁻¹ + 2 log N^ℓ)·ℓ^ℓ·(∑_p ‖b_p‖²)^ℓ,
  ```

  by applying the corpus's discrete cap (`card_largeValues_le`) to the power polynomial
  `convPow` and feeding the unit-1 mass bound.  This is [4, Lemma 8]'s counting inequality in
  corpus form: with `N = e^{(j+1)/H}`, `ℓ ≈ log T·H/j` (so `N^ℓ ≍ T`) and threshold
  `V = (log X)^{-100}`-scale against prime mass `∑‖b_p‖² ≈ h_j`, the right side is
  `T·polylog·exp(ℓ(log ℓ + log h_j + 2·100·log log X))/…` — the `exp((log X)^{1/48+o(1)})`
  spaced-count of the note.

Remaining route-B units: (3) [4, L11] duality-refinement audit (`AlmostOrthogonality`,
`CharacterSeparation`, `FrequencySeparation`); (4) sharp-cutoff Halász sup ([4, L3]) from the
uniform-frequency layer; (5) numeric re-certification of the full route-B bookkeeping with these
exact corpus constants; (6) assembly.

- 2026-08-04 — unit 2 built and verified.

## 2026-08-04 unit 3 (audit) closed: the wall is the zero-free-region exponent

**The κ-criterion.**  Write the available region as `σ ≥ 1 − c/(log|t|)^κ`.  Route (B)'s
[4, L11] step must absorb the unit-2 spaced count `|𝒯| ≪ exp(C·(log T/log P)·log log X)` by the
off-diagonal prime-sum decay `exp(−c·log P/(log T)^κ)`, which requires
`log P ≳ (log T)^{(1+κ)/2}` — while the Ramaré rough saving requires `log P = o(log X)`.  Both
hold simultaneously **iff κ < 1** (Littlewood's `log log`-refined κ = 1 also passes, with a
`(log log X)^{-c}` saving).  Route (A)'s Lemma 2 needs `log P ≍ (log X)^κ·log log X`, i.e. the
same criterion.  Spot checks: κ = 9 forces `log P ≥ (log T)⁵` — impossible; κ = 2/3 gives
`log P ≈ (log X)^{5/6}` and a `(log X)^{-1/6+o(1)}` saving.

**What is formalized, anywhere in the tree:** the corpus strip (`zetaLowerA`-layer) and the
vendored `PNTPlus.ZetaZeroFree` are both **κ = 9** (`σ ∈ Ico (1 − A/(log|t|)⁹) 1`, with
`|ζ| ≳ (log|t|)⁻⁷` lower bounds; hence `MediumPNT`'s `exp(−c(log x)^{1/10})` error, reach
exponent `1/(κ+1) = 1/10`).  Even de la Vallée Poussin (κ = 1) is not formalized — and κ = 1
would still not suffice.

**Terminal analytic requirement for the corridor (both routes):** one formalized zero-free
region with κ < 1, in three quality tiers:
1. **Littlewood** (`σ ≥ 1 − c·log log t/log t`): needs Weyl-differencing bounds for
   `∑ n^{it}` (equivalently `ζ(1+it) ≪ log t/log log t`); yields an explicit
   `(log log X)^{-c}` corridor saving — sufficient for every `o(1)` consumer
   (`MRBilinear` is a `Tendsto → 0` statement with no rate).
2. **van der Corput/Korobov–Vinogradov family** (κ = 2/3+ε): yields `(log X)^{-c}`.
3. The note's constants as published.

Tier 1 is the licensed next target: mathlib owns the van der Corput lemma for oscillatory
integrals; the sum version (via Abel summation + the integral test) and the Weyl-differencing
step are classical and self-contained.  Everything else in route (B) is now built (units 1–2)
or corpus-owned; unit 4 (sharp-cutoff Halász sup) remains but is not region-gated.

- 2026-08-04 — unit 3 audit closed; tier-1 (Littlewood region) licensed as the next analytic
  build; numeric κ-criterion recorded above.

- 2026-08-05 — the κ < 1 requirement now has its own production card:
  `littlewood-zero-free-region.md` (stage L1 numerically certified:
  `ζ(1+it) ≤ (1.24…1.93)·log t/log log t` across five decades of `log t` with the
  k-th-derivative-test chain; formalization staged L2–L6 there).  This card's unit 5
  (numeric re-certification of route B) waits on that card's L2 honest constants.

## 2026-08-05 SCOPE BOUNDARY (binding): what MRBilinear can and cannot deliver

Recorded from user direction; consistent with the formal interface and with the corpus
no-gos (`equidistributed-phase-threshold`, `density-envelope-cannot-decide-rh`,
`five-lanes-one-wall`).

1. **Littlewood does not finish this card.**  After the zero-free region lands (κ < 1),
   the corridor still needs (a) the unit-5 numeric re-certification of the route-B
   bookkeeping at Littlewood tier, and (b) the analytic assembly (Halász mean-value side)
   before `MRBilinear` is a theorem.

2. **A completed MR theorem yields exactly local sign-class density — no more.**  The
   Lean interface makes the limit visible: `MRBilinear f hh` controls
   `pairSum/(h·√x·log 2) − (blockMean f x)²`, i.e. the *fluctuation about block means*.
   The coherent component lives in the subtracted `blockMean²` term.  Fourier
   countermodels (a lone coherent low-frequency mode — a "Gibbs current" — of size `X^θ`
   riding on windows of length `X^θ`) satisfy every mean-square/almost-all statement of
   this shape while carrying nonzero net current.  This is the same extremal object as
   the `equidistributed-phase-threshold` lone-phase no-go, one layer up.

3. **Consequence.**  `route_e_sign_density` / `route_e_signClass_nonempty`
   (`Sieve/RouteEMain.lean`) become unconditional once MRBilinear is proved — that is the
   honest scope of the Littlewood→MR milestone.  Route E's physical Hall / seam-flux
   theorem (the RH-bearing coherent statement, e.g. the `(G2)` parity-mixing law of
   `ROUTE-E-GIBBS-PARITY-001` with growth `x^{−b}`, `b > 1/2`) is NOT implied by any
   mean-square input and must be attacked by a mechanism that couples to the coherent
   low-frequency mode (multiplicative cutoff boundary per that card, or a
   positivity-creating mechanism per `five-lanes-one-wall`).  Do not present MRBilinear
   as closing Route E.

## 2026-08-10 the κ-criterion gate is discharged: Littlewood is formalized

Unit 3 recorded the terminal analytic requirement of both routes as *one formalized zero-free
region with `κ < 1`*, in three tiers, with tier 1 (Littlewood, `σ ≥ 1 − c·log log t/log t`) licensed
as the next build.  Tier 1 is now an unconditional Lean theorem:

```text
RHTower.Sieve.exists_littlewood_zero_free_region_abs :
  ∃ c T, 0 < c ∧ 3 ≤ T ∧ ∀ β γ,
    T ≤ |γ| → β ≤ 1 → 1 − c·log log|γ| / log|γ| < β → ζ(β + iγ) ≠ 0
```

axioms `[propext, Classical.choice, Quot.sound]`.  It did **not** need Weyl differencing or van der
Corput: the corpus's own derivative-test chain already gave the growth bound, and what was missing
was the observation that the region is limited by the *width of the strip on which the growth bound
holds*, not by the size of the bound.  Choosing the derivative-test order so that
`2^K ≍ log t/(log log t)²` — smaller than the order that optimises the line — widens the strip from
`1/log t` to `(log log t)²/log t` at a polylogarithmic cost in the bound, and Landau's remainder
`16 log Φ/R` drops from `log t·log log t` to `log t/log log t`.  See the parent card
`littlewood-zero-free-region.md`, section `W`.

**Next on this card (unchanged in shape, now unblocked):** unit 5 — re-certify the route-B
bookkeeping numerically with the Littlewood-tier saving `(log log X)^{-c}` and the exact corpus
constants — then unit 4 (sharp-cutoff Halász sup) and the assembly.

## 2026-08-10 the Halász distance layer no longer needs a zero-free strip

`RHTower/Sieve/MoebiusDistanceSharp.lean` (wired, axiom-clean, warning-free).

`MoebiusUniformFrequency`'s distance bound `D(μ, χ_t; z)² ≥ log log z − 7 log log T − C` is gated on
`log⁹T/A ≤ log z`, because the lower bound it uses for `|ζ(σ+it)|` comes from the exponent-nine
zero-free strip and the abscissa `σ = 1 + 1/log z` has to lie inside that strip.  That constraint —
smoothness `z ≥ exp((log T)⁹)` — is what made the layer unusable at the corridor's prime scales.

The three-four-one inequality gives a lower bound for `|ζ(σ+it)|` at **every** `σ > 1` with no
zero-free input:

```text
|ζ(σ+it)| ≥ exp( (−22 − 3 log(1 + 1/(σ−1)) − log‖ζ(σ+2it)‖)/4 )   (exp_le_norm_riemannZeta_shift),
```

and right of the abscissa the harmonic sum already bounds `‖ζ(w)‖ ≤ 3 + log(4 + |Im w|)`
(`norm_riemannZeta_ge_one_log_le`, from `norm_riemannZeta_ge_one_le` at the cutoff
`⌈3 + |Im w|⌉`).  Feeding that through the corpus's own truncation/abscissa-shift passage
(`sum_cos_div_prime_ge_of_le`) gives, for **every** `z ≥ 3` and every `|t| ≥ 1`:

- `sum_cos_div_prime_ge_absolute` —
  `∑_{p ≤ z} cos(t log p)/p ≥ −(3/4)·log(1 + log z) − (1/4)·log(3 + log(4 + 2|t|)) − C`;
- `le_mulDistSqPair_moebius_absolute` — hence
  `D(μ, χ_t; p ≤ z)² ≥ (1/4)(log log z − log log|t|) − C`.

The trade is explicit: a self-loss `(3/4) log log z` in exchange for dropping the `(log T)⁹`
smoothness gate.  The bound is positive and growing whenever `log z ≥ (log T)^{1+ε}`, so the
Halász layer is now available across the corridor's parameter range, where before it was vacuous.

Note this is *independent* of the Littlewood region: it uses no zero-free region at all.  The two
are complementary — the region controls the *left* of the abscissa (route (A)'s Lemma 2, route (B)'s
spacing decay), the three-four-one bound controls the abscissa itself.

### The gate removal propagates to the chain capstones

`RHTower/Sieve/MoebiusDistanceSharp.lean` (continued) and `RHTower/Sieve/LiouvilleChainFree.lean`:

- `exists_sum_cos_div_prime_ge_free` — the pole box covers `|t| ≤ 9`, the three-four-one bound the
  rest, so for **every** `z ≥ 3` and **every real** `t`
  `∑_{p≤z} cos(t log p)/p ≥ −(3/4)log(1 + log z) − (1/4)log(3 + log(4 + 2|t|)) − C`;
- `exists_mulDistSqPair_ge_free` — the same for the distance of any weight that is `−1` on the
  primes;
- `exists_norm_sum_moebius_smooth_le_free` — the damped smooth Möbius sum is
  `≤ C(1 + log z)^{3/4}(3 + log(4+2|t|))^{1/4}` against a trivial `≍ log z`: a genuine
  `(log z)^{1/4}` power saving at every scale;
- `liouvilleDeltaFree`, `exists_liouvilleC_delta_free` — the `hunif` input of
  `norm_sum_Icc_mul_log_le_damped(_near)` with no gate;
- `exists_norm_sum_Icc_liouvilleC_mul_log_free`,
  `exists_norm_sum_Icc_liouvilleC_mul_log_near_free`,
  `exists_norm_sum_Icc_liouvilleC_mul_log_block_near_free` — **all three** of `LiouvilleChain`'s
  capstones with the hypothesis `1/log z ≤ zetaLowerA/log⁹(t₀2^K)` deleted, otherwise verbatim.

All axiom-clean and warning-free.  The consequence for this card is that the Halász layer is no
longer confined to smoothness `z ≥ exp((log T)⁹)`: it is available at the corridor's prime scales,
which is where units 4–6 need it.

### Strip quality without the strip: `z ≤ T` replaces the gate

The self-loss `(3/4) log log z` of the gate-free distance is a loss in the *truncation*, not in the
frequency, so it disappears the moment the truncation stays below the frequency range.  For
`3 ≤ z ≤ T` and `|t| ≤ T`, monotonicity gives
`(3/4)log(1+log z) + (1/4)log(3+log(4+2|t|)) ≤ log log T + 11/10`
(`wide_losses_le_logLog`), hence

- **`exists_mulDistSqPair_ge_height`** —
  `D(f, χ_t; p ≤ z)² ≥ log log z − log log T − C` for every `3 ≤ z ≤ T`, `|t| ≤ T`;
- `liouvilleDeltaHeight`, `exists_liouvilleC_delta_height` — the same as a drop-in `hunif` for
  `norm_sum_Icc_mul_log_le_damped(_near)`.

Against `exists_mulDistSqPair_ge_uniform` (`log log z − 7 log log T − C`, gated on
`log⁹T/A ≤ log z`) this is a factor `7` better in the constant and replaces an unsatisfiable
smoothness demand by `z ≤ T`.  Removing the residual `(3/4) log log z` in the regime `z > T` needs a
`z`-independent lower bound for `|ζ|` at the abscissa, i.e. genuinely the zero-free region's control
of `ζ'/ζ` near the line — recorded as a separate obligation, not attempted here.

## 2026-08-10 unit 4, first obstruction removed: the sieve level was the loss, and Brun–Titchmarsh has no cap

Unit 4 (sharp-cutoff Halász sup) sits behind two named obstructions recorded in the corpus:

> (a) the Selberg sieve level is capped — `selbergFibreError = Y²e^{4c}(log z)^4` must stay under a
> main term of size `O(1)` per prime pair, so `log Y = O(1)` and `Q ≍ (mass)/log Y` gains nothing;
> (b) the outer weight's mass concentrates at `p` near `N` … restricting it to `p ≤ √N` fixes this.

**(a) is now removed.**  It was never a fact about sieves — it is a fact about *that* sieve
statement.  `Sieve/PrimeLogWindowCount.logNeighbourCount_le_sieve` carries two independent
parameters, the level `Y` and the sifting range `z`, and the fibre error couples them.
Brun–Titchmarsh — already in the tree, vendored, unused by this layer
(`PNTPlus.BrunTitchmarsh.primesBetween_le`) — has the same shape with the two identified and *no
fibre term*:

```text
#{primes in (A, B]} ≤ 2(B − A)/log z + 6z(1 + log z)³ + 1        for every z > 1 .
```

Three new modules, all unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired into
`RHTower`, umbrella builds warning-free:

| module | content |
|-|-|
| `Sieve/PrimeWindowBrunTitchmarsh` | `card_prime_Ioc_le_bt`, `logNeighbourCount_le_bt`, the mean square, and the affine pair `btMeanSquareConst/Rate` |
| `Sieve/PrimeWindowSharpLevel` | the level choice `z = q^{1/4}` and the resulting sharp count |
| `Sieve/PerronTripleBrunTitchmarsh` | the substitution into the vertical triple bound |

### The sharp count

```text
logNeighbourCount_le_sharp :
  s a finset of primes, q prime →
    #{p ∈ s : |log p − log q| < 1} ≤ 700·q/log q + 1
```

against the `q(e − e⁻¹) + 1` *integers* the unit multiplicative window contains.  The whole
logarithm is saved.  The admissibility of the level `z = q^{1/4}` is the inequality
`6(1 + u/4)³u ≤ 610·e^{3u/4}` for `u = log q ≥ 4` (`poly_le_exp_three_quarters`), proved from
`x ≤ e^x` at `x = 3u/16` — no Stirling, no asymptotics.

### What it buys, exactly

The near-diagonal weight of the almost-diagonal mean value theorem on a prime support drops from
`q` to `q/log q`.  For the von Mangoldt weight `a_q = f(q)(log q)q^{−σ}` at `σ = 1 + 1/log z`:

```text
∑_q q‖a_q q^{−σ}‖²        ≍ ∑_{q ≤ z} (log q)²/q  ≍ (log z)²/2        (Montgomery–Vaughan)
∑_q (q/log q)‖a_q q^{−σ}‖² ≍ ∑_{q ≤ z} (log q)/q   ≍ log z            (Brun–Titchmarsh)
```

a factor `log z`, hence `√Q` from `log z` to `√(log z)`.  This is *sharp*: for `f = 1` the inner
polynomial is `≈ 1/(σ−1+it)` and `∫_{|t|≤1}|B|²dt ≈ π/(σ−1) ≍ log z`, matching.  The
Montgomery–Vaughan `n`-weight was lossy by exactly one logarithm on prime supports, because primes
in a window of length `y` number `y/log y`, not `y`.

### What it does not buy

The recorded deficit against Halász's `(1+m)e^{−m}` is `log N`.  With obstruction (a) removed the
deficit is `√(log N)` — the requirement on the distance drops from `m ≥ log log N + ω(1)` to
`m ≥ ½log log N + ω(1)`.  **The remaining half is not a mean-square defect.**  The accounting:

```text
‖∑_{n≤N} f‖/N  ≲  log log N/log N  +  e^{−m}·√Q_A·√Q_B ,
```

with `√Q_A = O(1)` after obstruction (b)'s `p ≤ √N` restriction and `√Q_B ≍ √(log z)` now.  The
surviving `√(log N)` comes from the *un-normalised* inner GHS weight `b_q = f(q)log q`; the outer
weight `a_p = f(p)log p/log(N/p)` is normalised and costs nothing.  Every application of the
logarithmic recursion normalises the previous weight and creates one new un-normalised one, so no
number of recursions removes it.

Independently verified this session, and worth recording as a no-go: **no rearrangement of the
absolute-value Perron route can reach Halász.**  For `f = 1` the integrand `|ζ(σ+it)|/|s|` has
`∫_{|t|≤T}|ζ(σ+it)|dt/(1+|t|) ≍ log log N` while the true mean value is `1`; the cancellation
destroyed by `|·|` is worth exactly `log log N`, which is the size of `(1+m)` at the extremal
`m ≍ log log N`.  So the ceiling of the whole pointwise family is `e^{−m}·log log N`, and any route
to `(1+m)e^{−m}` must keep the phase.  The corpus is now at `e^{−m}√(log N)`; the gap to the
absolute-value ceiling is `√(log N)/log log N`, and the gap from that ceiling to Halász is the
phase.

## 2026-08-10 unit 4, the architecture is now known: GHS's `I₂` is a cell aggregate, and it is built

Fetched the actual analytic part of Granville–Harper–Soundararajan (arXiv:1706.03755, *A more
intuitive proof of a sharp version of Halász's theorem*).  The corpus had the right skeleton — triple
Dirichlet convolution, Perron — and **three wrong joints**.  All three are now identified, and the
one that carries the loss is built.

### What GHS actually do

```text
S_k(x) ≪ x ∫ |A_k(s)| · |B_k(s)| · |F_x(s)| |ds|/|s| + x ,      A_k = ∑_{p ∈ P_k} f(p)log p/(p^s log(x/p))
```

with `P_k = P ∩ (x^{1−e^{1−k}}, x^{1−e^{−k}}]`, and then Cauchy–Schwarz `≤ √(I₁I₂)` where

```text
I₁ = ∫ |A_k|² |ds| ,          I₂ = ∫ |B_k|² |F_x|² |ds|/|s|² .
```

1. **The Cauchy–Schwarz split is `A` against `B·F`, not `A` against `B` with `F` pointwise.**  The
   corpus's `integral_symm_norm_perron_triple_affine_le` does `sup‖F‖ · √(∫‖A‖²) · √(∫‖B‖²)`.  That
   is the wrong grouping: the long factor must travel with the inner prime polynomial.
2. **`I₂` is cut into unit cells.**  On each cell the envelope `‖F_x‖²/|s|²` is frozen at its
   maximum and the inner polynomial keeps its exact mean square.  The long factor therefore enters
   through
   ```text
   L(x)² := ∑_{|h| ≤ log²x + 1} (1/(h²+1))·sup_{|t−h| ≤ 1/2} |F_x(1+it)|² ,
   ```
   an **ℓ² aggregate of per-cell suprema**, not a global supremum times a length.  *This is the
   `(1+m)`.*  The corpus's ceiling `sup‖F‖ · log T` is exactly what the aggregate replaces.
3. **`I₁` has no height-linear term** because the outer weight is normalised by `1/log(x/p)` and
   restricted to a dyadic `k`-range: `I₁ ≪ ∑_{p ∈ P_k}(log p)/(p log²(x/p)) ≪ e^k/log x`, against
   `I₂ ≪ L(x)²e^{−k}log x`.  The `e^{±k}` cancel in `√(I₁I₂) ≪ L(x)` — which is why the `k`-partition
   is structural, not bookkeeping.

GHS's Lemma 1 is "the mean value theorem for Dirichlet polynomials **on primes**" — i.e. exactly the
`q/log q` near-diagonal weight built here earlier today.  That build was on the critical path.

### Built this session: the cell aggregate

| module | content |
|-|-|
| `HTGeometry/CellMaxProductIntegral` | `exists_cell_max_mul_integral_le`: `∫ G·H ≤ ∑_k (max_{cell k} G)·∫_{cell k} H` for `H ≥ 0` |
| `Sieve/LogPolyTranslation` | `logPoly_add_right`, `norm_twist`, and the sharp prime mean square **on an arbitrary cell** |
| `Sieve/HalaszCellAggregate` | `primeCellMass`, `integral_cell_normSq_logPoly_le`, `exists_cell_aggregate_normSq_logPoly_le` |

```text
exists_cell_aggregate_normSq_logPoly_le :
  s a finset of primes, E continuous and ≥ 0 →
    ∃ v, (∀ k < m, v k ∈ cell k) ∧
      ∫_a^{a+m/π} E(w)·‖logPoly c s w‖² dw  ≤  (∑_{k<m} E(v k)) · primeCellMass c s
```

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower` builds
warning-free (18219 jobs).  The cell length is `1/π`, the largest for which Gallagher's constraint
`2πδW ≤ 1` holds at the neighbour scale `δ = 1`; translation invariance
(`integral_Icc_normSq_logPoly_shift_le_prime_sharp`) is what makes the *same* mean square available
on every cell, and it costs nothing because a frequency shift only twists the coefficients by
unimodular factors.

### What is left of unit 4

Only the instantiation: take `E(w) = ‖F(σ − 2πiw)‖²/‖σ − 2πiw‖²` and identify `∑_k E(v_k)` with
`L(x)²`; then Cauchy–Schwarz `A` against `B·F` and the `k`-partition of the outer prime range.  No
new analytic input is needed — the aggregate is the object the previous four architectures were
missing, and it is now a theorem.

Note: `GaloisForLFunctions.HTGeometry` currently fails to build for an unrelated reason — a
concurrent agent's untracked `ConstitutiveQGammaProcess.lean` re-declares
`summable_succ_pow_mul_geometric`, already in `PolydiscAnalytic`.  Not touched.  `RHTower` and both
new modules build clean on their own targets.

## 2026-08-10 unit 4: both remaining joints built — the regrouping and the aggregate on the Perron line

The two GHS joints identified above are now theorems.  Five modules total this session, all
unconditional, axioms `[propext, Classical.choice, Quot.sound]`, `RHTower` builds warning-free
(18225 jobs).

### Joint 1 — the regrouped Cauchy–Schwarz (`Sieve/PerronTripleRegrouped`)

```text
integral_Icc_norm_perron_triple_regrouped_le :
  ∫_{|y|≤T} ‖L(A,s)·L(B,s)·L(f,s)·x^s/s‖ dy
    ≤ √(∫_{|y|≤T} ‖L(A,s)‖²) · √(∫_{|y|≤T} (‖L(B,s)‖·‖L(f,s)‖·x^σ/‖s‖)²)
```

The long factor travels with the **inner** polynomial.  The corpus's
`integral_symm_norm_perron_triple_affine_le` splits `(‖A‖‖B‖)·(‖f‖·kernel)` and charges `sup‖f‖`;
that grouping is what caps it.  `norm_perron_triple_integrand_regrouped` is the same modulus
identity with a different `ring` at the end — the regrouping costs nothing.

### Joint 2 — the aggregate on the Perron line (`Sieve/HalaszCellAggregateLine`)

```text
LSeries_line_shift : L(a, σ+i(v+y)) = L(a·n^{-iv}, σ+iy)
integral_Icc_normSq_LSeries_cell_le_prime :
  ∫_{v−1/2}^{v+1/2} ‖L(a, σ+iy)‖² dy ≤ 2π · primeCellMass (a·n^{−σ}) s
exists_cell_aggregate_normSq_LSeries_le :
  ∫_b^{b+m} E(y)·‖L(a, σ+iy)‖² dy ≤ (∑_{k<m} E(v_k)) · 2π · primeCellMass (a·n^{−σ}) s
```

for prime-supported `a`, any continuous `E ≥ 0`, with `v_k` a maximiser of `E` on the `k`-th unit
cell.  The shift is free: `‖n^{−iv}‖ = 1`, so the mean square is the same on every cell of the line.

With `E(y) = (‖L(f,σ+iy)‖·x^σ/‖σ+iy‖)²` the two joints compose: joint 1 produces exactly the
integral joint 2 bounds, and `∑_k E(v_k)` is GHS's `L(x)²` — the ℓ² aggregate of per-cell suprema of
the long factor that replaces `sup‖f‖ · log T`.

### The full session chain

| module | content |
|-|-|
| `Sieve/PrimeWindowBrunTitchmarsh` | prime window count with a free level; `btMeanSquareConst/Rate` |
| `Sieve/PrimeWindowSharpLevel` | `#{p : |log p − log q| < 1} ≤ 700 q/log q + 1` at level `q^{1/4}` |
| `Sieve/PerronTripleBrunTitchmarsh` | substitution into the old triple bound |
| `HTGeometry/CellMaxProductIntegral` | `∫ G·H ≤ ∑_k (max_{cell} G)·∫_{cell} H` |
| `Sieve/LogPolyTranslation` | the sharp prime mean square on an arbitrary Gallagher cell |
| `Sieve/HalaszCellAggregate` | `primeCellMass`, the aggregate in Gallagher's variable |
| `Sieve/PerronTripleRegrouped` | **joint 1** |
| `Sieve/HalaszCellAggregateLine` | **joint 2** |

### What is left of unit 4

Only joint 3 and the assembly, both arithmetic:

* the dyadic partition of the outer prime range `P_k = P ∩ (x^{1−e^{1−k}}, x^{1−e^{−k}}]`, whose
  purpose is to make `I₁ = ∫‖L(A_k)‖² ≪ e^k/log x` cancel `I₂ ≪ L²e^{−k}log x` — the outer weight
  `f(p)log p/log(x/p)` is already the corpus's `ghsOuter`;
* the identification of `∑_k E(v_k)` with `L(x)² = ∑_h (1/(h²+1))·sup_{|t−h|≤1/2}‖F_x(1+it)‖²`,
  which is the kernel bound `1/‖σ+iy‖² ≤ 4/(1+h²)` on the `h`-th cell.

No further analytic input.  Every device the four capped architectures were missing is now a
theorem in the tree.

## 2026-08-10 unit 4: the aggregate is length-independent — the `log T` is gone

Two more modules; the architecture's quantitative payoff is now a theorem.

### The composition (`Sieve/PerronTripleCellBound`)

```text
exists_cell_bound_integral_norm_perron_triple :
  ∃ v, (∀ k < m, v k ∈ cell k) ∧
    ∫_b^{b+m} ‖A·B·f·x^s/s‖ dy
      ≤ √(∫_b^{b+m} ‖A‖²)
        · √( (∑_{k<m} ‖f(σ+iv_k)‖²·x^{2σ}/‖σ+iv_k‖²) · 2π·primeCellMass (B·n^{−σ}) sB )
```

Joint 1 was generalised from the symmetric range to an arbitrary `Icc c d` (its proof never used
symmetry), and then joints 1 and 2 compose directly.

### The kernel sum (`Sieve/PerronKernelCellSum`)

```text
sum_cells_inv_normSq_le :
  v k ∈ [k − n, k − n + 1] for k < m  →  ∑_{k<m} 1/‖σ + i·v_k‖² ≤ 7/σ² + 1
```

**uniformly in `m`.**  Seven cells lie within distance three of the axis and pay `1/σ²` each; the
rest telescope through `Sieve/AveragedSquarefreeTail.sum_Icc_inv_sq_le` at level `R = 2`.  The cell
offset is taken at an integer, which is free — the Perron height may be chosen an integer.

Consequence: against a uniform bound `V` for the long factor, the aggregate is
`≤ V²x^{2σ}(7/σ² + 1)`.  The route it replaces gives `sup‖f‖ · ∫dt/‖σ+it‖ ≍ V·log T`.  **The factor
`log T` — the whole recorded deficit against Halász — is gone.**

### The accounting now closes

At GHS's parameters (`T = (log x)²`, outer range `P_k = P ∩ (x^{1−e^{1−k}}, x^{1−e^{−k}}]`):

| factor | corpus object | size |
|-|-|-|
| `√(∫‖A_k‖²)` | prime mean square, near-diagonal weight `p/log p` | `√(e^k/log x)` |
| aggregate | `sum_cells_inv_normSq_le` against `V` | `V·x^σ·√(7/σ²+1)` |
| `√(primeCellMass B)` | `∑_{q ≤ x^{e^{1−k}}}(log q)/q` | `√(e^{1−k}log x)` |

Product: `V·x^σ·√(7e/σ² + e)` — **no `log x`, no `T`**.  The `e^{±k}` cancel, which is what the
dyadic partition of the outer prime range exists to arrange, and the near-diagonal weight `p/log p`
is what makes `I₁` come out as `∑_p (log p)/(p log²(x/p))` rather than `∑_p (log p)²/(p log²(x/p))`.

Every factor of the GHS bound is now a corpus theorem.  What is left is bookkeeping: instantiate
`A = ghsOuter` restricted to `P_k`, `B = ghsInner`, evaluate the two Mertens-type prime sums, and
sum over `k`.  No analytic input remains.

## 2026-08-10 unit 4: both prime sums evaluated — `Sieve/GhsCellMass`

The bookkeeping side is now done too.  One module, unconditional, axioms
`[propext, Classical.choice, Quot.sound]`, wired, `RHTower` builds clean (18230 jobs).

### The additive term of the cell mass is free

`primeCellMass c s = (5/4)∑_q (700 q/log q + 1)‖c q‖²` carries an additive `+1` that would need a
second (convergent but separate) prime sum.  It does not: `1 ≤ q/log q` for every prime
(`one_le_div_log_of_prime`, from `log q ≤ q − 1`), so

```text
primeCellMass_le_weighted : primeCellMass c s ≤ (5/4)·701·∑_{q ∈ s} (q/log q)·‖c q‖² .
```

One weighted sum, nothing else.

### The two weights

```text
primeCellMass_ghsInner_le :  ‖f‖ ≤ 1, σ ≥ 1, M ≥ 1 →
  primeCellMass (ghsInner f M · n^{−σ}) (primesLE M) ≤ (5/4)·701·(log M + log 4)

primeCellMass_ghsOuter_le :  ‖f‖ ≤ 1, σ ≥ 1 →
  primeCellMass (ghsOuter f N · n^{−σ}) (primesLE N)
    ≤ (5/4)·701·∑_{p ≤ N} log p/(p·log²(N/p))
```

The first is Mertens' first theorem (`mertensFirst_upper`, already in the tree).  The second is
exactly the `I₁` of the GHS argument.  Both go through the same three steps: the weight's modulus,
`p^{−σ} ≤ 1/p` past the abscissa one (`rpow_neg_le_inv`), and the cancellation
`(p/log p)·((log p/L)/p)² = log p/(p L²)`.  The degenerate outer primes (`N/p < 2`, where
`ghsOuter` vanishes) need no side condition: both sides are zero.

**The `log p` rather than `(log p)²` in the outer sum is the whole point** — it is the prime
near-diagonal weight `q/log q` of `PrimeWindowSharpLevel`, and it is what makes `I₁ ≍ e^k/log N`
after the dyadic partition instead of `≍ e^k`.

### And the mean square over a range

```text
integral_normSq_LSeries_le_cells :
  ∫_b^{b+m} ‖L(a, σ+iy)‖² dy ≤ m · 2π · primeCellMass (a·n^{−σ}) s
```

the constant-envelope case of the cell aggregate: for a prime-supported polynomial the mean square
over any range is the number of cells times one cell's mass — no height, no sieve level.

### Status of unit 4

Every analytic *and* arithmetic ingredient of the GHS bound is now an unconditional corpus theorem:

| GHS object | corpus theorem |
|-|-|
| `√(∫‖A_k‖²)` | `integral_normSq_LSeries_le_cells` + `primeCellMass_ghsOuter_le` |
| the `A`-vs-`B·f` split | `integral_Icc_norm_perron_triple_regrouped_le` |
| `L(x)²` (the aggregate) | `exists_cell_aggregate_normSq_LSeries_le`, `exists_cell_bound_integral_norm_perron_triple` |
| length-independence | `sum_cells_inv_normSq_le` |
| Lemma 1 (prime MVT) | `integral_Icc_normSq_logPoly_le_prime_sharp` |
| `√(∫‖B‖²)` | `primeCellMass_ghsInner_le` |

What remains is the dyadic partition `P_k` of the outer prime range and the evaluation
`∑_{p ∈ P_k} log p/(p log²(N/p)) ≍ e^k/log N`, then summing the `k`-pieces.  Pure Mertens
bookkeeping on a restricted prime range.

## 2026-08-10 unit 4: the block estimate and the scale-`δ` count

Two modules, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18234 jobs).

### `Sieve/GhsOuterBlock` — the outer sum on a block

```text
mertensFirst_general_block :  1 ≤ A ≤ B →
  ∑_{A < p ≤ B} log p/p ≤ log B − log A + mertensBlockGapConst

sum_block_outer_le :  1 ≤ A ≤ B, 2 ≤ N/B →
  ∑_{A < p ≤ B} log p/(p·log²(N/p)) ≤ (log B − log A + mertensBlockGapConst)/log²(N/B)
```

with `mertensBlockGapConst = log 4 + 1 + 2·logSqTailConst` absolute.  The first differences the
two-sided Mertens theorem at the two endpoints (the corpus had only the dyadic case,
`sum_prime_log_div_block_le`); the second needs only that natural division is antitone in its
denominator, so `N/B ≤ N/p` throughout the block.

At the argument's ranges `A = x^{1−e^{1−k}}`, `B = x^{1−e^{−k}}` this is
`e^{−k}(e−1)log x / (e^{−k}log x)² = (e−1)e^{k}/log x` — the `I₁` shape that cancels the inner
factor's `e^{−k}log x`.

### `Sieve/PrimeWindowSharpDelta` — the count at the scale the height forces

The unit-scale count was not enough: the almost-diagonal mean value theorem uses `δ = 1/T`.  The
same level `z = (qδ)^{1/4}` works at every scale:

```text
logNeighbourCount_le_sharp_delta :  0 < δ ≤ 1, e⁴ ≤ q·δ →
  #{p : |log p − log q| < δ} ≤ 700·(qδ)/log(qδ) + 1
```

— the window length divided by *its own* logarithm.  The threshold `qδ ≥ e⁴` is exactly where
Brun–Titchmarsh's error `6z(1+log z)³` drops below its main term; below it the window carries `O(1)`
primes anyway.  One new elementary step: `e^δ − e^{−δ} ≤ 4δ` on `(0,1]`, from `1 − δ ≤ e^{−δ}` and
`(1−δ)e^δ ≤ 1`.

Hence the mean square in **affine form with the sharp near-diagonal mass**:

```text
integral_Icc_normSq_logPoly_le_prime_sharp_delta :
  ∫ ‖P‖² ≤ (5·700/4)·∑_q (q/log(qδ))·‖a_q‖²  +  (5/(4δ))·∑_q ‖a_q‖² .
```

This is the shape `I₁` actually needs — height-independent constant plus height-linear rate — and it
is why `I₁` reads `∑_p log p/(p log²(x/p))` and not `∑_p (log p)²/(p log²(x/p))`.  In the argument
`δ = 1/(log x)²` and the outer primes satisfy `p > log⁴x`, so `qδ > log²x ≫ e⁴` and the height-linear
term is negligible.

### Remaining

The `k`-sum: choose the `P_k` endpoints, verify `log(N/B_k) ≥ e^{−k}log N`, and add the pieces.
Every estimate they consume is now a corpus theorem.

## 2026-08-10 unit 4: `I₁` is finished — the sharp affine mean square on the Perron line

One module plus a refactor.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`,
wired, `RHTower` builds clean (18238 jobs).

### `Sieve/PrimeLineSharpAffine`

```text
integral_Icc_normSq_LSeries_le_prime_sharp_delta :
  prime support, 1 ≤ T, e⁴ ≤ q/T for every q →
    ∫_{|y| ≤ T} ‖L(a, σ+iy)‖² dy
      ≤ 2π·[ (5·700/4)·∑_q (q/log(q/T))·‖a_q q^{−σ}‖²  +  (5T/4)·∑_q ‖a_q q^{−σ}‖² ]
```

The scale-`δ` count at `δ = 1/T`, transported to the Perron variable.  **This, not the
constant-envelope bound, is the right `I₁`**: the near-diagonal mass is height-*independent* and the
height enters only through the plain mass.  My first pass used
`integral_normSq_LSeries_le_cells` (`m ·` cell mass), which carries a spurious factor `T` and would
have lost `(log x)²` at the argument's height.

### The outer instantiation

```text
half_log_le_log_div          :  T² ≤ q  →  log q/2 ≤ log(q/T)
sum_sharp_mass_ghsOuter_le   :  ∑_q (q/log(q/T))‖ghsOuter·q^{−σ}‖² ≤ 2·∑_q log q/(q log²(N/q))
sum_sharp_mass_ghsOuter_block_le :
  ∑_{A < q ≤ B} (q/log(q/T))‖ghsOuter·q^{−σ}‖²
    ≤ 2·(log B − log A + mertensBlockGapConst)/log²(N/B)
```

The scale costs a factor two and nothing else, because `T² ≤ q` throughout the block — which the
argument's `T = (log x)²`, `q > log⁴x` gives exactly.  `I₁` for one block is now a closed formula in
`A`, `B`, `N`.

### Refactor

`ghsInner_weighted_term_le` and `ghsOuter_weighted_term_le` hoisted out of the two `primeCellMass`
proofs in `Sieve/GhsCellMass`, so the per-prime estimate is available on its own.  Both capstones
now read `Finset.sum_le_sum fun q hq => …`; nothing was duplicated.

### Remaining

The `k`-sum: pick the `P_k` endpoints, check `log(N/B_k) ≥ e^{−k}log N` and `T² ≤ A_k`, and add.
The per-block bound is
`√(I₁)·√(I₂) ≤ √(2(log B−log A+C)/log²(N/B)) · √(V²x^{2σ}(7/σ²+1)·2π·(5/4)·701·(log(N/A)+log 4))`,
which is `O(V·x^σ)` when `log B − log A ≍ log(N/B)` and `log(N/A) ≍ log(N/B)` — the balance the
dyadic partition is designed to produce.

## 2026-08-10 unit 4: the block polynomial and the cancellation that justifies the partition

One module, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18239 jobs).

### `Sieve/GhsOuterBlockPoly`

```text
ghsOuterBlock f N A B p := if p ∈ primesLE B \ primesLE A then ghsOuter f N p else 0
```

with its support, primality and `= ghsOuter` lemmas, and the block's `I₁`:

```text
integral_Icc_normSq_LSeries_ghsOuterBlock_le :
  1 ≤ A ≤ B, 2 ≤ N/B, T² ≤ q and e⁴ ≤ q/T throughout the block →
    ∫_{|y| ≤ T} ‖L(ghsOuterBlock, σ+iy)‖² dy
      ≤ 2π·[ (5·700/4)·2·(log B − log A + mertensBlockGapConst)/log²(N/B) + (5T/4)·κ_plain ]
```

The plain mass is carried as an explicit parameter `κ_plain`, since it is the only quantity whose
size depends on how the endpoints are chosen; everything else is closed-form in `A`, `B`, `N`, `T`.

### Why the partition exists — `block_balance_le`

```text
1 ≤ S, 0 ≤ C, W ≤ κS, U ≤ κ'S  →  ((W + C)/S²)·(U + log 4) ≤ (κ + C)(κ' + log 4)
```

with `S = log(N/B)` the block's scale, `W = log B − log A` its width and `U = log(N/A)` the inner
range.  **One factor of `S` cancels against one of the two in the denominator**, so a balanced block
contributes a bounded amount *independently of where it sits*.  That is the whole reason for
partitioning the outer prime range: without it the single block `A = 1`, `B = N/2` has `S ≍ 1` while
`W ≍ log N`, and the quotient is `log N` instead of `O(1)`.

Note the two hypotheses are exactly complementary — `W ≤ κS` says the block is not too wide for its
scale, `U ≤ κ'S` says the scale has not collapsed relative to the whole inner range.  A geometric
partition satisfies both with absolute `κ, κ'`; an arithmetic one satisfies neither.

### Remaining

Choose the endpoints: a family `A_k, B_k` with `log B_k − log A_k ≍ log(N/B_k) ≍ log(N/A_k)`,
verify `T² ≤ A_k` and `e⁴ ≤ A_k/T`, bound `κ_plain`, and add over `k`.  Every estimate consumed by
that sum is now a corpus theorem, and `block_balance_le` is the statement that makes the sum
`O(number of blocks)` rather than `O(number of blocks × log N)`.

## 2026-08-10 unit 4: the endpoints are chosen and the blocks are balanced

One module, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18242 jobs).

### `Sieve/GhsScaleSequence`

```text
ghsScale N k     = ⌊N^{1/2^k}⌋
ghsBlockLeft N k  = N / ghsScale N k
ghsBlockRight N k = N / ghsScale N (k+1)
```

The family is geometric **in the logarithm**, which is what `block_balance_le` needs and what an
arithmetic family cannot supply.  Two bounds carry everything:

```text
log_ghsScale_le :  log(ghsScale N k) ≤ (log N)/2^k
le_log_ghsScale :  (log N)/2^k − log 2 ≤ log(ghsScale N k)
```

— the floor costs exactly one `log 2`, once, not per step.

### The blocks are balanced

```text
ghs_block_balanced :  1 ≤ N,  2^{k+1}·4·log 2 ≤ log N,  2·ghsScale N k ≤ N →
  1 ≤ log(N/B_k)
  ∧ log B_k − log A_k ≤ 2·log(N/B_k)
  ∧ log(N/A_k)        ≤ 3·log(N/B_k)
```

so `block_balance_le` applies with `κ = 2`, `κ' = 3` and every block contributes at most
`(2 + mertensBlockGapConst)(3 + log 4)` — an absolute constant, independent of `k` and of `N`.

Two elementary division facts were needed and are now separate lemmas: `le_div_div`
(`D ≤ N/(N/D)`) and `div_div_lt_two_mul` (`N/(N/D) < 2D` once `2D ≤ N`), the second resting on
`lt_div_add_one_mul` (`N < (N/D + 1)·D`), which mathlib does not have under a findable name.

### The count of blocks

The threshold `2^{k+1}·4·log 2 ≤ log N` is what bounds the family: `k` runs up to
`≍ log₂(log N) = ≍ log log N`.  **That is the entire reason for the doubly-geometric partition** —
an arithmetic family of the same balance would need `≍ log N` blocks, and the final estimate
multiplies the per-block constant by the number of blocks.

### Remaining

Bound `κ_plain` for the block (the plain `ℓ²` mass of the outer weight, negligible at the
argument's height), instantiate `sum_cells_inv_normSq_le` for the long factor, and sum the
`≍ log log N` per-block bounds.  All three are arithmetic on estimates already in the tree.

## 2026-08-10 unit 4: the last two parameters are closed

One module, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18244 jobs).  `Sieve/GhsBlockPlainMass`.

### The block's plain mass

```text
sum_plain_mass_ghsOuterBlock_le :  1 ≤ A ≤ B,  2 ≤ N/B →
  ∑_{A < q ≤ B} ‖ghsOuterBlock·q^{−σ}‖² ≤ (log B/log(N/B))²·(1/A)
```

No new estimate was needed: dividing the weighted term bound by its own weight gives
`‖a_q q^{−σ}‖² ≤ (log q)²/(q² log²(N/q))`, then `log q ≤ log B` and `log(N/q) ≥ log(N/B)` freeze the
shape and `∑_{q > A} 1/q² ≤ 1/A` (`AveragedSquarefreeTail.sum_Icc_inv_sq_le`) finishes.  In the
argument `A` is a power of `N`, so this term is smaller than any power of `log N` — the
height-linear part of `I₁` contributes nothing.

### The long factor's aggregate

```text
sum_cells_aggregate_le_of_bound :  ‖L(g, σ+iy)‖ ≤ V for all y →
  ∑_{k<m} ‖L(g, σ+iv_k)‖²·x^{2σ}/‖σ+iv_k‖² ≤ V²·x^{2σ}·(7/σ² + 1)
```

uniformly in `m`, by `sum_cells_inv_normSq_le`.  **This is the step where the height leaves the
estimate**: the route it replaces produces `V²x^{2σ}·log T`.

### Unit 4: every ingredient is now a corpus theorem

| GHS object | corpus theorem |
|-|-|
| triple convolution → Perron | `PartialSumVsTripleConvolution`, `ChebyshevPerronIdentity` |
| Cauchy–Schwarz `A` vs `B·f` | `integral_Icc_norm_perron_triple_regrouped_le` |
| Lemma 1 (prime MVT) | `integral_Icc_normSq_logPoly_le_prime_sharp_delta` |
| `I₁` (affine, sharp mass) | `integral_Icc_normSq_LSeries_ghsOuterBlock_le` |
| `I₁`'s near-diagonal mass | `sum_sharp_mass_ghsOuter_block_le` ← `sum_block_outer_le` ← `mertensFirst_general_block` |
| `I₁`'s plain mass | `sum_plain_mass_ghsOuterBlock_le` |
| `I₂` (cell decomposition) | `exists_cell_aggregate_normSq_LSeries_le` |
| `I₂`'s inner mass | `primeCellMass_ghsInner_le` (Mertens) |
| `L(x)²` against a uniform `V` | `sum_cells_aggregate_le_of_bound` |
| length-independence | `sum_cells_inv_normSq_le` |
| the `k`-partition | `ghsScale`, `ghsBlockLeft/Right`, `ghs_block_balanced` |
| the cancellation | `block_balance_le` |

What is left is one composition — feed the per-block pieces into
`exists_cell_bound_integral_norm_perron_triple` and sum the `≍ log log N` blocks.  No estimate
remains to be proved.

## 2026-08-10 unit 4: the per-block bound composes — `Sieve/GhsBlockPerronBound`

One module, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18248 jobs).  It compiled on the first attempt, which is the right signal: every
input was already a theorem with the shape the composition needed.

```text
ghs_block_perron_bound :
  ‖f‖ ≤ 1, 1 ≤ σ, 0 < x, ‖L(g, σ+iy)‖ ≤ V for all y,
  1 ≤ n, 1 ≤ A ≤ B, 2 ≤ N/B, n² ≤ q and e⁴ ≤ q/n throughout the block, 1 ≤ M →
    ∫_{|y| ≤ n} ‖L(ghsOuterBlock f N A B)·L(ghsInner f M)·L(g)·x^s/s‖ dy
      ≤ √( 2π·[ (5·700/4)·2·(log B − log A + mertensBlockGapConst)/log²(N/B)
                + (5n/4)·κ_plain ] )
        · √( V²·(x^σ)²·(7/σ² + 1) · 2π·(5/4)·701·(log M + log 4) )
```

Nothing asymptotic: both square roots are closed formulas in `A`, `B`, `M`, `N`, `n`, `σ`, `x`, `V`.

* The **first** factor is `I₁` — the outer polynomial's mean square with the sharp near-diagonal
  weight `q/log q`, the height entering only through `κ_plain`, which
  `sum_plain_mass_ghsOuterBlock_le` makes smaller than any power of `log N`.
* The **second** is `I₂` — the long factor's aggregate, `V²x^{2σ}·(7/σ²+1)` and *not*
  `V²x^{2σ}·log n`, times the inner polynomial's Mertens mass `(5/4)·701·(log M + log 4)`.

Combined with `ghs_block_balanced` (`κ = 2`, `κ' = 3` for the geometric blocks) and
`block_balance_le`, the product of the two roots is bounded by an absolute constant times
`V·x^σ`, uniformly in the block index.

### What is left

One step: the outer polynomial decomposes over the blocks,
`L(ghsOuter restricted to ⋃_k block_k) = ∑_k L(ghsOuterBlock … A_k B_k)`, so the triangle
inequality turns the full integral into the sum of the `≍ log log N` per-block integrals, each
bounded above.  That is a decomposition of a finitely supported Dirichlet series along a partition
of its support — no estimate, no analysis.

## 2026-08-10 unit 4: the outer polynomial decomposes — `Sieve/GhsBlockTelescope`

One module, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18250 jobs).

```text
ghsOuterBlock_split :  A ≤ B ≤ C →
  ghsOuterBlock f N A C p = ghsOuterBlock f N A B p + ghsOuterBlock f N B C p

ghsOuterBlock_telescope :  a monotone →
  ghsOuterBlock f N (a 0) (a K) p = ∑_{k < K} ghsOuterBlock f N (a k) (a (k+1)) p

LSeries_ghsOuterBlock_telescope :  a monotone →
  L(ghsOuterBlock f N (a 0) (a K), σ+iy) = ∑_{k < K} L(ghsOuterBlock f N (a k) (a (k+1)), σ+iy)
```

The pointwise split is a four-way case analysis on where `p` sits relative to `A`, `B`, `C` (plus
the non-prime case, where all three vanish); the telescope is induction on `K`.  The passage to the
Dirichlet series needs no summability argument: `LSeries_eq_logPoly_of_support` turns each series
into a *finite* sum over the common support `primesLE (a K) \ primesLE (a 0)`, after which
`Finset.sum_comm` does the work.  `block_subset_of_monotone` is what puts every block inside that
common support.

### Unit 4 is complete as a chain of theorems

```text
∫_{|y|≤n} ‖L(outer over (a 0, a K])·L(ghsInner f M)·L(g)·x^s/s‖ dy
  ≤ ∑_{k<K} ∫_{|y|≤n} ‖L(ghsOuterBlock f N (a k) (a (k+1)))·L(ghsInner f M)·L(g)·x^s/s‖ dy
  ≤ K · (per-block bound of ghs_block_perron_bound)
```

the first line by `LSeries_ghsOuterBlock_telescope` and the triangle inequality, the second by
`ghs_block_perron_bound` with `ghs_block_balanced` and `block_balance_le` making every term the
same absolute constant times `V·x^σ`.  With the geometric scales `K ≍ log log N`.

Every step from the Perron formula to the `log log N` is now an unconditional corpus theorem.  The
remaining assembly is the triangle-inequality line itself — `‖∑_k Z_k · W‖ ≤ ∑_k ‖Z_k · W‖`
integrated over a compact interval — plus the arithmetic of choosing `n`, `M`, `σ`, `x`.

## 2026-08-10 unit 4 CLOSED: the vertical integral splits over the blocks

One module, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18253 jobs).  `Sieve/GhsBlockSumBound`.

```text
integral_norm_perron_triple_sum_blocks_le :  a monotone →
  ∫_{|y| ≤ n} ‖L(ghsOuterBlock f N (a 0) (a K))·L(B)·L(g)·x^s/s‖ dy
    ≤ ∑_{k < K} ∫_{|y| ≤ n} ‖L(ghsOuterBlock f N (a k) (a (k+1)))·L(B)·L(g)·x^s/s‖ dy
```

`norm_perron_triple_integrand` factors the modulus as `‖A‖·(‖B‖‖g‖x^σ/‖s‖)`, so the triangle
inequality applies to the first factor alone and the common tail — nonnegative and continuous —
comes out of the estimate untouched.  `MeasureTheory.integral_finsetSum` then swaps the finite sum
past the integral; every summand is continuous on a compact interval, so integrability is free.

### Unit 4 is closed

Every step of the Granville–Harper–Soundararajan bound is an unconditional corpus theorem:

```text
∫_{|y|≤n} ‖L(outer)·L(inner)·L(g)·x^s/s‖
  ≤ ∑_{k<K} ∫_{|y|≤n} ‖L(block k)·L(inner)·L(g)·x^s/s‖          integral_norm_perron_triple_sum_blocks_le
  ≤ ∑_{k<K} √(I₁(k))·√(I₂)                                       ghs_block_perron_bound
  ≤ K · C · V · x^σ                                              ghs_block_balanced + block_balance_le
```

with `K ≍ log log N` by the geometric scales.  The chain runs from the Perron formula to the
`log log N` without a single hypothesis beyond `‖f‖ ≤ 1`, `1 ≤ σ`, and the numerical thresholds on
the block endpoints.

**Status of the card.** Unit 4 (sharp-cutoff Halász sup) is the last non-region-gated obstruction
listed in the 2026-08-04 route-B freeze, and it is now built.  Units 1–3 were already closed;
unit 3's `κ < 1` requirement was discharged earlier today by the Littlewood region.  What remains
for `MRBilinear` is unit 5 (numeric re-certification of the route-B bookkeeping with these exact
corpus constants) and unit 6 (assembly), both of which consume only estimates that now exist.

## 2026-08-10 unit 6 begun: every block contributes the same constant

`Sieve/GhsBlockShape`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired,
`RHTower` builds clean (18255 jobs).

```text
ghs_block_shape_le :  1 ≤ N,  2^{k+1}·4·log 2 ≤ log N,  2·ghsScale N k ≤ N →
  ((log B_k − log A_k + mertensBlockGapConst)/log²(N/B_k))·(log(N/A_k) + log 4)
    ≤ (2 + mertensBlockGapConst)·(3 + log 4)
```

This is the only `k`-dependent quantity in the per-block Perron bound — everything else (`V`,
`x^σ`, `7/σ² + 1`, the two `2π`'s, the numerical factors `5·700/4` and `(5/4)·701`) is already
independent of `k`.  So the `k`-sum multiplies an absolute constant, and with the geometric scales
the number of terms is `≍ log log N`.

It is `block_balance_le` at the constants `κ = 2`, `κ' = 3` that `ghs_block_balanced` supplies; the
side conditions `0 ≤ log B_k − log A_k` and `0 ≤ log(N/A_k)` come from `ghsBlockLeft_le_right` and
`Nat.div_pos`.

### Where unit 6 stands

The assembly is now four named theorems in sequence, all unconditional:

```text
integral_norm_perron_triple_sum_blocks_le    split the integral over the blocks
ghs_block_perron_bound                       bound each block by √(I₁)·√(I₂)
ghs_block_shape_le                           the k-dependent part of √(I₁ I₂) is an absolute constant
ghs_block_balanced / block_balance_le        (its inputs)
```

What is left of unit 6 is numerical: multiply out the constants, choose `n`, `σ`, `x` and the
number of blocks `K` against `log N`, and check the `κ_plain` term is dominated.  That is unit 5's
re-certification, not new mathematics.

Note: the `RHTower` umbrella build raced once against a concurrent agent's untracked
`RHTower/BeurlingSystemMellin.lean` (written mid-build); the immediate rebuild succeeded.

## 2026-08-10 unit 6: the per-block bound with the shape eliminated

`Sieve/GhsBlockBoundBalanced`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`,
wired, `RHTower` builds clean (18257 jobs).

```text
ghs_block_bound_balanced :
  ‖f‖ ≤ 1, 1 ≤ σ, 0 < x, ‖L(g,σ+iy)‖ ≤ V,
  1 ≤ n, 1 ≤ N, 2^{k+1}·4·log 2 ≤ log N, 2·ghsScale N k ≤ N, 2 ≤ N/B_k,
  n² ≤ q and e⁴ ≤ q/n on the block, 0 ≤ κ_plain and the plain mass ≤ κ_plain  →
    ∫_{|y| ≤ n} ‖L(block k)·L(ghsInner f (N/A_k))·L(g)·x^s/s‖ dy
      ≤ √( (2π)²·V²·x^{2σ}·(7/σ²+1)·(5/4)·701
            · [ 1750·(2 + mertensBlockGapConst)(3 + log 4)
                + (5n/4)·κ_plain·(log(N/A_k) + log 4) ] )
```

Merging the two square roots of `ghs_block_perron_bound` and applying `ghs_block_shape_le` leaves
`k` **only inside `κ_plain`'s coefficient** — and `sum_plain_mass_ghsOuterBlock_le` bounds
`κ_plain` by `(log B_k/log(N/B_k))²/A_k`, smaller than any power of `log N` because `A_k` is a power
of `N`.  Every block therefore contributes the same `O(V·x^σ)`, and the `≍ log log N` blocks sum to
`O(V·x^σ·log log N)`.

The inner cutoff is `M = N/A_k`, tied to the block's left endpoint — that is what makes the second
Cauchy–Schwarz factor's `log M + log 4` the `log(N/A_k) + log 4` that `block_balance_le` consumes.
It is not a free parameter: the balance fixes it.

### Unit 6: what remains

Only the numerical closing — put `n`, `σ`, `x`, `K` in terms of `log N`, check
`(5n/4)·κ_plain·(log(N/A_k) + log 4)` is dominated by the constant term, and read off the
`log log N`.  Every inequality it uses is now a corpus theorem; the work is arithmetic on explicit
constants, which is unit 5's re-certification.

## 2026-08-10 unit 6: the sum over the blocks — and a correction

`Sieve/GhsSumBlocksBound`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired,
`RHTower` builds clean (18258 jobs).

```text
ghsBlockConst σ := √( (2π)²·(7/σ²+1)·(5/4)·701·2·1750·(2 + mertensBlockGapConst)(3 + log 4) )

ghs_block_bound_uniform :  … plus  (5n/4)·κ_plain·(log(N/A_k) + log 4)
                                     ≤ 1750·(2 + mertensBlockGapConst)(3 + log 4)  →
  ∫_{|y| ≤ n} ‖L(block k)·L(ghsInner f (N/A_k))·L(g)·x^s/s‖ dy ≤ V·x^σ·ghsBlockConst σ

ghs_sum_blocks_bound_le :  each block bounded by V·x^σ·ghsBlockConst σ →
  ∑_{k < K} (block k's integral) ≤ K·V·x^σ·ghsBlockConst σ
```

With the geometric scales `K ≍ log log N`, so the total is `O(V·x^σ·log log N)` — the shape the
argument needs.

### Correction to the 2026-08-10 entry "the vertical integral splits over the blocks"

`integral_norm_perron_triple_sum_blocks_le` splits one Perron integral whose **inner factor is
fixed** across the blocks.  The argument does not use that: the inner cutoff must be `N/A_k`, one
per block.  The reason is visible in the balance — the second Cauchy–Schwarz factor contributes
`log M + log 4`, and `block_balance_le` needs it proportional to the block's scale `log(N/B_k)`,
which shrinks geometrically in `k`.  A cutoff held fixed at `N` satisfies that only for the first
few blocks.

So the reassembly of the blocks is at the level of the **arithmetic** sum — each block carries its
own Perron representation — not by splitting a single integral.  `integral_norm_perron_triple_sum_blocks_le`
and the telescope lemmas remain correct and are the right tool for a fixed inner factor; they are
simply not the step this argument takes.  `ghs_sum_blocks_bound_le` is stated for the varying-cutoff
family, which is the one that composes with the balance.

### Unit 6 remaining

The arithmetic decomposition `(∑_{n≤N} f)·log N = ∑_k S_k + O(N log log N)` with `S_k` the block's
triple sum, and the numerical choice of `n`, `σ`, `x`, `K`.  The first is a re-run of
`PartialSumVsTripleConvolution` with the outer prime range restricted to a block; the second is
unit 5.

## 2026-08-10 unit 6: the blocks at the arithmetic level

`Sieve/GhsArithmeticBlocks`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`,
wired, `RHTower` builds clean (18259 jobs).  This is the step the previous entry's correction
identified as missing.

```text
convolution_ghsOuterBlock_telescope :  a monotone →
  (ghsOuterBlock f N (a 0) (a K) ⍟ h)(n) = ∑_{k<K} (ghsOuterBlock f N (a k) (a (k+1)) ⍟ h)(n)

sum_Icc_convolution_ghsOuterBlock_telescope :  the same, summed over n ≤ M

convolution_ghsInner_trunc_eq :  1 ≤ A, n ≤ N, 0 < n →
  (ghsOuterBlock f N A B ⍟ (ghsInner f N ⍟ F))(n)
    = (ghsOuterBlock f N A B ⍟ (ghsInner f (N/A) ⍟ F))(n)
```

The first two are linearity of the convolution in its outer factor, moved through the divisor
antidiagonal by `Finset.sum_comm`.  **The blocks enter here, before Perron** — which is what lets
each block carry its own inner truncation.

The third is why that truncation is legitimate: a term of the triple convolution at `n ≤ N` whose
outer index exceeds `A` has inner index `q` with `q·A ≤ q·p ≤ n ≤ N`, hence `q ≤ N/A`, so cutting
`ghsInner` at `N/A` removes nothing.  No estimate — an identity.

### Unit 6 remaining

The chain is now

```text
(∑_{n≤N} f)·log N  =  ∑_{n≤N}(ghsOuter ⍟ (ghsInner f N ⍟ f))(n) + O(N log log N)   [corpus]
                    =  ∑_{k<K} ∑_{n≤N}(block k ⍟ (ghsInner f N ⍟ f))(n) + …        [telescope]
                    =  ∑_{k<K} ∑_{n≤N}(block k ⍟ (ghsInner f (N/A_k) ⍟ f))(n) + …  [truncation]
                    ≤  ∑_{k<K} (Perron for block k)                                 [corpus]
                    ≤  K·V·x^σ·ghsBlockConst σ                                      [ghs_sum_blocks_bound_le]
```

with `K ≍ log log N`.  What is left is the Perron step per block — instantiating the corpus's
existing triple-convolution Perron identity at the block's weights — and the numerical choice of
`n`, `σ`, `x`, `K`, which is unit 5.

## 2026-08-10 unit 6: the Perron step for one block

`Sieve/GhsBlockSumPerron`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired,
`RHTower` builds clean (18261 jobs).

```text
ghs_block_sum_perron_le :  supports, truncation error ≤ E, vertical integral ≤ V·(N+½)^σ·C →
  ‖∑_{i ≤ min(B'(L·N)) N} (ghsOuterBlock f N A' B' ⍟ (ghsInner f L ⍟ g))(i)‖
    ≤ E + (1/2π)·(V·(N+½)^σ·C)
```

This is the corpus's own `norm_sum_Icc_triple_of_error_and_analytic_le` instantiated at the block's
weights — the architectural bet recorded in `halasz-route-architecture` ("state each level against
parameters, not against the estimate that supplies them") paying off: both inputs slot in
unchanged, and the only new work is `interval_eq_Icc_block_integrand`, the identification of the
interval integral with the `Icc` set integral at `t₀ = n`, `K = 0`.

Support lemmas: `ghsOuterBlock_mem_Icc` (new); `ghsInner_mem_Icc` was already in
`GhsCoefficients` — I wrote a duplicate and the umbrella caught it, which is the collision mode
that per-file checks miss.

### Unit 6 remaining

Only the numerical closing, which is unit 5: choose `n`, `σ`, `x = N + ½`, `K ≍ log log N`; bound
the per-block truncation error `E`; and check the domination hypothesis of
`ghs_block_bound_uniform`.  Every inequality the assembly consumes is now a corpus theorem.

## 2026-08-10 unit 6: the join between the arithmetic and analytic sides

`Sieve/GhsBlocksTotal`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired.

```text
sum_Icc_convolution_ghsOuterBlock_telescope_trunc :  a monotone, 1 ≤ a k, M ≤ N →
  ∑_{n ≤ M} (outer over (a 0, a K] ⍟ (ghsInner f N ⍟ F))(n)
    = ∑_{k < K} ∑_{n ≤ M} (block k ⍟ (ghsInner f (N/a k) ⍟ F))(n)

norm_sum_Icc_ghsOuterBlock_blocks_le :  each block's sum bounded by D →
  ‖∑_{n ≤ M} (outer over (a 0, a K] ⍟ (ghsInner f N ⍟ F))(n)‖ ≤ K·D
```

The first is an identity: the telescope moves the blocks out, and inside block `k` the inner cutoff
drops from `N` to `N/a k` with no loss because a term at `n ≤ N` whose outer index exceeds `a k` has
inner index at most `N/a k`.  The second adds the blocks.

**This is the join.**  The left-hand side is exactly what the logarithmic recursion produces
(`PartialSumVsTripleConvolution`); the summands on the right are exactly what
`ghs_block_sum_perron_le` estimates.  The two halves of unit 6 now meet.

### Unit 6 remaining

Only unit 5's numerics: choose `n`, `σ`, `x = N + ½`, `K ≍ log log N`, bound the per-block
truncation error `E`, and check the domination hypothesis of `ghs_block_bound_uniform`.

Note: the `RHTower` umbrella currently fails on a concurrent agent's untracked
`RHTower/XiMassCriticalSafeEulerGreenWeld.lean` (written one minute before the build, a `rewrite`
that does not fire).  Not touched; `GhsBlocksTotal` builds clean on its own target (9247 jobs).

## 2026-08-10 unit 6: the blocks cover the outer weight — the chain is closed

`Sieve/GhsOuterCovered`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired,
`RHTower` builds clean (18267 jobs — the concurrent agent's file is fixed).

```text
ghsOuterBlock_eq_ghsOuter :  N/2 ≤ C  →  ghsOuterBlock f N 1 C p = ghsOuter f N p

norm_sum_Icc_ghsOuter_blocks_le :
  a monotone, 1 ≤ a k, a 0 = 1, N/2 ≤ a K, M ≤ N, each block's sum ≤ D →
    ‖∑_{n ≤ M} (ghsOuter f N ⍟ (ghsInner f N ⍟ F))(n)‖ ≤ K·D
```

The coverage lemma is the observation that `ghsOuter f N` vanishes unless `2 ≤ N/p`, i.e. unless
`p ≤ N/2`: a family of blocks running from `1` past `N/2` therefore *is* the whole weight, not
merely a part of it.  With it the telescope applies to the object the logarithmic recursion
produces, and the chain closes:

```text
(∑_{n≤N} f)·log N  =  ∑_{n≤N}(ghsOuter f N ⍟ (ghsInner f N ⍟ f))(n) + O(N log log N)
                                                                   [PartialSumVsTripleConvolution]
‖∑_{n≤M}(ghsOuter f N ⍟ (ghsInner f N ⍟ F))(n)‖  ≤  K·D            [norm_sum_Icc_ghsOuter_blocks_le]
D = E + (1/2π)·V·(N+½)^σ·ghsBlockConst σ                            [ghs_block_sum_perron_le]
                                                                    [ghs_block_bound_uniform]
K ≍ log log N                                                       [GhsScaleSequence]
```

Every link is an unconditional corpus theorem.  **Unit 6 is complete as a chain**; what is left is
unit 5 — discharging the numeric hypotheses (`n`, `σ`, the truncation error `E`, the domination of
the plain-mass term) with explicit constants.

## 2026-08-10 unit 6: the top-level capstone

`Sieve/GhsPartialSumBlocks`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`,
wired, `RHTower` builds clean (18268 jobs).

```text
ghsRecursionError N := (9+c)N + N log 4 + (9+c)·N·((log 3 + 2((log 4 + 4) + (8+c)))/log 2)(1 + log log₂ N)

norm_sum_Icc_mul_log_blocks_le :
  f completely multiplicative, ‖f‖ ≤ 1, 2 ≤ N,
  a monotone with a 0 = 1, 1 ≤ a k, N/2 ≤ a K, each block's sum ≤ D →
    ‖(∑_{n ≤ N} f)·log N‖ ≤ ghsRecursionError N + K·D
```

**This is the whole argument in one inequality**, with `D` the only thing left to supply and
everything above it — the two applications of the logarithmic recursion, the block telescope, the
per-block inner truncation, the coverage of the outer weight — discharged.

### The endpoint, checked

At the argument's parameters `D ≍ V·N` and `K ≍ log log N`, so

```text
‖∑_{n≤N} f‖ ≲ N·log log N/log N + N·V·log log N/log N ,
```

and with `V` the damped size `≍ (log N)·e^{−m}` this is `N·e^{−m}·log log N`.  Non-trivial —
`o(N)` — as soon as `m ≥ log log log N + ω(1)`, against the corpus's previous requirement
`m ≥ log log N`.  It is the absolute-value ceiling established earlier today, and it sits within
`log log N/(1 + m)` of Halász's `(1+m)e^{−m}`, the two coinciding at the extremal `m ≍ log log N`.

I re-derived this endpoint before building rather than after: the accounting is what says the chain
was worth assembling.

### Unit 6 remaining

Only the numeric discharge of `D` — instantiate `ghs_block_sum_perron_le` with
`ghs_block_bound_uniform`, choose `n`, `σ`, bound the per-block truncation error `E`, and verify
the domination hypothesis.  Every inequality involved is a corpus theorem.

## 2026-08-10 unit 6: the block's `D`

`Sieve/GhsBlockD`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired,
`RHTower` builds clean (18270 jobs).

```text
ghs_block_D_le :  1 ≤ B', 1 ≤ L, supports, truncation error ≤ E, vertical integral ≤ V·(N+½)^σ·C →
  ‖∑_{i ≤ N} (ghsOuterBlock f N A' B' ⍟ (ghsInner f L ⍟ f))(i)‖
    ≤ E + (1/2π)·(V·(N+½)^σ·C)
```

The connector between the capstone and the Perron step.  The capstone asks for the untruncated `f`
as third factor; the Perron step needs all three finitely supported.  Truncating `f` at `N` costs
nothing (`convolution_triple_truncSeq_eq_of_le` — every index a convolution touches at `n` divides
`n`), and the Perron cutoff `min (B'·(L·N)) N` collapses to `N` as soon as `B'` and `L` are
positive.

### Unit 6: the chain is complete end to end

```text
‖(∑_{n≤N} f)·log N‖ ≤ ghsRecursionError N + K·D           norm_sum_Icc_mul_log_blocks_le
D = E + (1/2π)·V·(N+½)^σ·ghsBlockConst σ                  ghs_block_D_le ∘ ghs_block_bound_uniform
K ≍ log log N                                             GhsScaleSequence
```

Every link unconditional, every constant explicit.  What remains is not a step of the argument but
its instantiation: pick `n` and `σ`, bound `E` from the corpus's truncation lemmas, and verify the
domination hypothesis of `ghs_block_bound_uniform`.  That is unit 5.

## 2026-08-10 unit 6: the mean value, in Halász's shape

`Sieve/GhsMeanValue`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired,
`RHTower` builds clean (18273 jobs).

```text
norm_sum_Icc_le_ghs :
  f completely multiplicative, ‖f‖ ≤ 1, 2 ≤ N,
  a monotone with a 0 = 1, 1 ≤ a k, N/2 ≤ a K,
  each block's sum ≤ E + (1/2π)·V·(N+½)^σ·C  →
    ‖∑_{n ≤ N} f(n)‖
      ≤ ( ghsRecursionError N + K·(E + (1/2π)·V·(N+½)^σ·C) ) / log N
```

This is the argument's final form.  `ghsRecursionError N` is `O(N·log log N)`, so the first term is
`O(N·log log N/log N)`; the second is `O(K·V·N/log N)`.  With `K ≍ log log N` and `V` the damped
size `≍ (log N)·e^{−m}`, the whole is `N·(log log N/log N + e^{−m}·log log N)`.

**Non-trivial as soon as `m ≥ log log log N + ω(1)`**, against `m ≥ log log N` before this thread —
and within `log log N/(1 + m)` of Halász's `(1 + m)e^{−m}`, the two agreeing at the extremal
`m ≍ log log N`, which is exactly where the absolute-value route was shown optimal earlier today.

### Unit 6 is complete

Every step of the Granville–Harper–Soundararajan argument is an unconditional corpus theorem, and
the endpoint is a single named statement whose only remaining input is a per-block bound of the
stated shape.  Supplying that input is instantiation: `ghs_block_D_le` composed with
`ghs_block_bound_uniform`, at a choice of `n` and `σ` and with `E` from the corpus's truncation
lemmas.  Nothing left is an estimate.

## 2026-08-10 unit 6: the last connector — `Sieve/GhsBlockDUniform`

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`, wired, `RHTower` builds clean
(18275 jobs).

```text
ghs_block_D_le_uniform :
  ‖f‖ ≤ 1, 1 ≤ σ, ‖L(truncSeq f N, σ+iy)‖ ≤ V for all y,
  1 ≤ n, 1 ≤ N, 2^{k+1}·4·log 2 ≤ log N, 2·ghsScale N k ≤ N, 2 ≤ N/B_k, 1 ≤ B_k,
  n² ≤ q and e⁴ ≤ q/n on the block, plain mass ≤ κ_plain, the domination hypothesis,
  Perron truncation error ≤ E  →
    ‖∑_{i ≤ N} (block k ⍟ (ghsInner f (N/A_k) ⍟ f))(i)‖
      ≤ E + (1/2π)·V·(N+½)^σ·ghsBlockConst σ
```

`ghs_block_D_le` took the vertical integral as a hypothesis; `ghs_block_bound_uniform` supplies it.
At the geometric endpoints, the inner cutoff `N/A_k`, the third factor `truncSeq f N` and the Perron
cutoff `x = N + ½` the two match with no adaptation.  This is exactly the input
`norm_sum_Icc_le_ghs` asks for, so the two ends of unit 6 are joined.

### The complete chain, all unconditional

```text
norm_sum_Icc_le_ghs            ‖∑_{n≤N} f‖ ≤ (ghsRecursionError N + K·D)/log N
  ← norm_sum_Icc_mul_log_blocks_le
      ← norm_sum_Icc_ghsOuter_blocks_le          (coverage: ghsOuter vanishes above N/2)
          ← sum_Icc_convolution_ghsOuterBlock_telescope_trunc
      ← norm_sum_Icc_mul_log_sub_ghsTriple_le    (the logarithmic recursion, corpus)
  ← ghs_block_D_le_uniform                        D = E + (1/2π)V(N+½)^σ·ghsBlockConst σ
      ← ghs_block_D_le ← ghs_block_sum_perron_le  (corpus's parametrised Perron bound)
      ← ghs_block_bound_uniform ← ghs_block_bound_balanced ← ghs_block_perron_bound
          ← integral_Icc_norm_perron_triple_regrouped_le      (A vs B·f)
          ← exists_cell_aggregate_normSq_LSeries_le           (the cell aggregate)
          ← sum_cells_inv_normSq_le                           (length-independence)
          ← integral_Icc_normSq_logPoly_le_prime_sharp_delta  (prime MVT, q/log q)
          ← primeCellMass_ghsInner_le, sum_sharp_mass_ghsOuter_block_le  (Mertens)
      ← ghs_block_shape_le ← block_balance_le ← ghs_block_balanced  (the k-cancellation)
  K ≍ log log N                                   ← GhsScaleSequence
```

**Unit 6 is closed.**  What remains for `MRBilinear` is unit 5: supply `V`, `E`, `n`, `σ` with
explicit constants and check the two numeric hypotheses.  No structural step is left.

## 2026-08-10 unit 5, part 1: the height forces the partition, and a corrected hypothesis

Four new modules, all unconditional, `[propext, Classical.choice, Quot.sound]`, wired, `RHTower`
builds clean (18283 jobs).

### A hypothesis that could not have been discharged

`ghs_block_bound_uniform` asked for `∀ y : ℝ, ‖L(g, σ+iy)‖ ≤ V` — a bound on the whole line.  No
such `V` exists at the strength the argument needs: `V` is the damped size `dampedSize σ δ z N`,
whose damping `δ` is a lower bound for the multiplicative distance from `f` to the characters
`n ↦ n^{iy}`, and that distance necessarily degrades as `|y|` grows (the gate-free lower bound loses
`(1/4)log(3 + log(4+2|y|))`).  A hypothesis satisfiable only with `V` of trivial size is not a step
of a proof.

The cell aggregate only ever evaluates `L(g, ·)` at the sample points `v_k` of the `2n` unit cells
of `[-n, n]`, so the hypothesis was weakened to `∀ y, |y| ≤ n → …` and `sum_cells_aggregate_le_of_bound`
given the hypothesis `m ≤ 2n` that makes the sample points lie in the segment.  The weakening
propagates through `ghs_block_perron_bound`, `ghs_block_bound_balanced`, `ghs_block_bound_uniform`
and `ghs_block_D_le_uniform` unchanged, and the discharge is then immediate:

```text
ghs_block_D_le_damped :  Sieve/GhsBlockDDamped.lean
  f 1 = 1, f multiplicative on coprimes, ‖f‖ ≤ 1, 1 < σ, 1 ≤ z, 0 ≤ δ,
  δ ≤ 𝔻(f, n^{iy}) for |y| ≤ n, block hypotheses, Perron error ≤ E  →
    ‖∑_{i≤N} (block k ⍟ (ghsInner f (N/A_k) ⍟ f))(i)‖
      ≤ E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConst σ
```

### The height forces a different partition

The mean-square estimate asks every prime of a block to satisfy `n² ≤ q`.  The geometric partition
has `A_k = ⌊N/⌊N^{1/2^k}⌋⌋`, so `A_0 = 1`: its first block is `(1, N^{1/2}]`, which contains the
prime 2.  That block cannot satisfy the hypothesis, and it is not a small perturbation — it holds
half the outer range.  Two modules fix it.

**`Sieve/GhsSmallPrimeBlock.lean`** — the trivial bound, from the summatory swap and `‖f‖ ≤ 1`:

```text
norm_sum_Icc_convolution_triple_trivial_le :
  ‖∑_{i≤N} (a ⍟ (b ⍟ c))(i)‖ ≤ N·(∑_{p≤N} ‖a p‖/p)·(∑_{q≤N} ‖b q‖/q)

norm_sum_Icc_ghs_small_block_le :  1 ≤ P ≤ N, 2 ≤ ⌊N/P⌋, 1 ≤ M ≤ N →
  ‖∑_{i≤N} (blk(1,P] ⍟ (ghsInner f M ⍟ f))(i)‖
    ≤ N·((log P + log 4)/log⌊N/P⌋)·(log M + log 4)
```

both masses being Mertens sums.  At `P = n²` and `M = N` this is `≍ N·log n`, so divided by `log N`
the small primes cost `N·log log N/log N` — the size of the recursion error, and paid once.
`2 ≤ ⌊N/P⌋` is genuinely needed: at `⌊N/P⌋ = 1` the stated bound is `0` while the sum is not, since
a prime `p ≪ P` still has `⌊N/p⌋ ≥ 2`.

**`Sieve/GhsBlockGeneralBound.lean`, `Sieve/GhsBlockDGeneral.lean`** — the endpoints removed.  The
geometric partition entered the per-block bound at exactly one point, `ghs_block_shape_le`.  Making
the shape factor a hypothesis frees the endpoints:

```text
ghsBlockConstOf σ Γ := √((2π)²(7/σ²+1)((5/4)·701)·(2·1750·Γ))
ghsBlockConst σ = ghsBlockConstOf σ ((2 + C)(3 + log 4))              -- definitionally

ghs_block_bound_general :  1 ≤ A ≤ B, 2 ≤ ⌊N/B⌋, 1 ≤ M, n² ≤ q and e⁴ ≤ q/n on the block,
  plain mass ≤ κ, ((log B − log A + C)/log²⌊N/B⌋)·(log M + log 4) ≤ Γ,
  (5n/4)·κ·(log M + log 4) ≤ 1750·Γ  →
    ∫_{|y| ≤ n} ‖L(blk)·L(ghsInner f M)·L(g)·x^s/s‖ dy ≤ V·x^σ·ghsBlockConstOf σ Γ

ghs_block_D_le_general :  the same, with V the damped size and the Perron error E, giving
  ‖∑_{i≤N} (blk ⍟ (ghsInner f M ⍟ f))(i)‖
    ≤ E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ Γ
```

The trimmed first block `(n², N^{1/2}]` has `W = log N^{1/2} − 2 log n ≤ ½log N`,
`S = log⌊N/N^{1/2}⌋ ≈ ½log N`, `L = log(N/n²) + log 4 ≤ log N + log 4`, so its shape factor is
`≈ (½log N + C)/(¼log²N)·log N ≈ 2` — bounded, as the geometric blocks are.

### What is left

Unit 5 is now the assembly, and only the assembly: choose the partition
`1 < n² < A_1 < … < A_K` with `A_K ≥ N/2`, verify `n² ≤ q` and `e⁴ ≤ q/n` on each block (immediate
from the left endpoint), bound each `κ_plain` and each shape factor, bound `E` from the corpus's
truncation lemmas, and feed the result to `norm_sum_Icc_le_ghs`, whose hypothesis is a per-block
bound of exactly the shape `ghs_block_D_le_general` produces.  No estimate remains to be invented.

## 2026-08-10 unit 5, part 2: the partition and the sized block

Two more modules, unconditional, `[propext, Classical.choice, Quot.sound]`, wired, `RHTower` builds
clean (18288 jobs).

### `Sieve/GhsPartition.lean` — the height as an endpoint

```text
ghsPart N n 0       = 1
ghsPart N n (j + 1) = max (n²) (ghsBlockLeft N j)
```

with `ghsScale_zero : ghsScale N 0 = N`, `one_le_ghsScale`, `ghsBlockLeft_zero`,
`ghsBlockRight_eq_left_succ` (definitional — the geometric blocks telescope), `ghsBlockLeft_mono`,
`ghsPart_zero`, `ghsPart_one : ghsPart N n 1 = n²`, `one_le_ghsPart`, `ghsPart_mono`,
`ghsPart_covers`, and

```text
ghsPart_block_eq :  n² ≤ A_j, n² ≤ A_{j+1} →
  ghsOuterBlock f N (ghsPart N n (j+1)) (ghsPart N n (j+2))
    = ghsOuterBlock f N (ghsBlockLeft N j) (ghsBlockRight N j)
ghsPart_inner_eq :  n² ≤ A_j → N / ghsPart N n (j+1) = N / ghsBlockLeft N j
```

So the trimmed partition is the geometric partition wherever the geometric partition is already
above the height; the block `(1, n²]` is the small-prime block; and exactly one block is new,
`(n², ghsBlockLeft N 1]`.

### `Sieve/GhsBlockSized.lean` — three hypotheses collapse to one condition on the height

`lt_of_mem_block : q ∈ primesLE B \ primesLE A → A < q` is all that `hsq` and `hbig` need, and the
plain mass is already `sum_plain_mass_ghsOuterBlock_le`.  With `n² ≤ A` the factor `1/A ≤ 1/n²`
moves the height from the numerator of the domination hypothesis to its denominator:

```text
ghs_block_D_le_sized :
  f 1 = 1, f multiplicative on coprimes, ‖f‖ ≤ 1, 1 < σ, 1 ≤ z, 0 ≤ δ,
  δ ≤ 𝔻(f, n^{iy}) for |y| ≤ n, e⁴ ≤ n, 1 ≤ A ≤ B, 2 ≤ ⌊N/B⌋, 1 ≤ M, n² ≤ A,
  ((log B − log A + C)/log²⌊N/B⌋)·(log M + log 4) ≤ Γ,
  (5/4n)·(log B/log⌊N/B⌋)²·(log M + log 4) ≤ 1750·Γ,
  Perron truncation ≤ E  →
    ‖∑_{i≤N} (blk ⍟ (ghsInner f M ⍟ f))(i)‖
      ≤ E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ Γ
```

Only two inequalities remain per block: the shape bound and the domination.  On the geometric
blocks `log B_k/log⌊N/B_k⌋ ≤ 2^{k+1}` and `log M + log 4 ≤ log N + log 4`, so the domination asks
`(5/4n)·4^{k+1}·log N ≤ 1750Γ`; with `K ≍ log log N` blocks the worst case is `4^K ≍ (log N)²`, so
a height `n ≫ (log N)³` clears every block at once.  That is a weaker demand than the rest of the
argument already makes of `n`.

### What is left

`hshape` on the one new block `(n², ghsBlockLeft N 1]`; the explicit `n` and `σ`; `E` from the
corpus's truncation lemmas; and the sum over `j` of `ghs_block_D_le_sized` fed to
`norm_sum_Icc_le_ghs` through `ghsPart_block_eq`.

## 2026-08-10 unit 5, part 3: `ghs_block_shape_le` never covered the first block

`Sieve/GhsTrimmedBlockShape.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
`RHTower` builds clean (18291 jobs).

A hypothesis audit, not a new estimate: `ghs_block_shape_le` carries `2·ghsScale N k ≤ N`, and
`ghsScale N 0 = N`, so at `k = 0` it reads `2N ≤ N` — **the geometric shape bound is vacuous on the
first block**.  That is not a defect of the proof.  The first geometric block is `(1, N^{1/2}]`,
which is precisely the block the height forbids, so the geometric chain never had to cover it and
never did.  The two facts — the block that violates `n² ≤ q` and the block whose shape is unproved —
are the same block, and both are repaired by the same replacement.

```text
ghsScale_le :  ghsScale N k ≤ N

two_mul_ghsScale_le :  1 ≤ k, 2·log 2 ≤ log N  →  2·ghsScale N k ≤ N
  -- so the geometric hypothesis is automatic for every k ≥ 1, and only k = 0 is special

ghs_trimmed_shape_le :  8·log 2 ≤ log N, n² ≤ ghsBlockRight N 0  →
  ((log⌊N/⌊N^{1/2}⌋⌋ − log n² + C)/log²⌊N/ghsBlockRight N 0⌋)·(log⌊N/n²⌋ + log 4)
    ≤ (3 + C)(3 + log 4)
```

The mechanism: `le_div_div` gives `⌊N/B⌋ ≥ ⌊N^{1/2}⌋`, so `S ≥ (log N)/2 − log 2 ≥ (3/8)log N` once
`log N ≥ 8 log 2`; the width and the inner range are both at most `log N ≤ 3S`; `block_balance_le`
at `κ = κ' = 3` closes it.  Same shape as the geometric blocks, with `2` widened to `3`.

Every block of `ghsPart` now has its shape: `(1, n²]` by the trivial bound,
`(n², ghsBlockRight N 0]` by `ghs_trimmed_shape_le`, and `(A_j, A_{j+1}]` for `j ≥ 1` by
`ghs_block_shape_le` with `two_mul_ghsScale_le` supplying its hypothesis.

### What is left

The explicit `n` and `σ`; `E` from the corpus's truncation lemmas; and the sum over `j`.

## 2026-08-10 unit 5, part 4: one constant for every block

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`, wired, `RHTower` builds
clean (18293 jobs).

### `Sieve/GhsBlockRatio.lean` — the domination is a condition on the height alone

```text
ghs_block_ratio_le :  2^{k+1}·4·log 2 ≤ log N  →
  log B_k / log⌊N/B_k⌋ ≤ (4/3)·2^{k+1}

ghs_block_dom_le :  the same threshold, M ≤ N,
  (5/4n)·(16/9)·4^{k+1}·(log N + log 4) ≤ 1750·Γ  →
    (5/4n)·(log B_k/log⌊N/B_k⌋)²·(log M + log 4) ≤ 1750·Γ
```

`le_div_div` gives `⌊N/B_k⌋ ≥ ghsScale N (k+1)`, whose logarithm is at least
`(log N)/2^{k+1} − log 2`; the threshold makes that `log 2` at most a quarter of the first term, so
`log⌊N/B_k⌋ ≥ (3/4)(log N)/2^{k+1}`.  The block index is the *only* thing left in the domination.

### `Sieve/GhsBlockPackage.lean` — a single `Γ`

`ghsShapeConst := (3 + C)(3 + log 4)` dominates both the geometric shape `(2 + C)(3 + log 4)` and
the trimmed shape `(3 + C)(3 + log 4)`, so one constant serves the whole partition:

```text
ghs_geometric_shape_le :  1 ≤ k, threshold →  geometric shape ≤ ghsShapeConst
   -- two_mul_ghsScale_le supplies ghs_block_shape_le's own hypothesis

ghs_block_D_le_geometric :  k ≥ 1, threshold, 2 ≤ ⌊N/B_k⌋, n² ≤ A_k, e⁴ ≤ n,
  (5/4n)·(16/9)·4^{k+1}·(log N + log 4) ≤ 1750·ghsShapeConst, Perron error ≤ E  →
    ‖∑_{i≤N} (blk_k ⍟ (ghsInner f (N/A_k) ⍟ f))(i)‖
      ≤ E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst

ghs_block_D_le_trimmed :  the same conclusion for the block (n², ghsBlockRight N 0]
```

Both blocks now land on the identical right-hand side.  Every hypothesis except `E` is either a
threshold on `N`, the condition `n² ≤ A_k`, or the single height inequality — and at
`K ≍ log log N` blocks, where `4^{K+1} ≍ (log N)²`, that inequality asks for `n ≫ (log N)³`.

### What is left

`E` from the corpus's truncation lemmas, the explicit `n` and `σ`, and the sum over the blocks.

## 2026-08-10 unit 5, part 5: the truncation error, and a block with nothing open

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`, wired, `RHTower` builds
clean (18296 jobs).

### `Sieve/GhsBlockPerronError.lean`

The corpus already owned every piece: `norm_convolution_triple_le_log_pow_const` (prime-supported
first two factors ⇒ polylogarithmic coefficients, via `ω(n)·log 2 ≤ log n`),
`convolution_mem_Icc_of_support_mul` for the support, and
`norm_sum_Icc_sub_perron_integral_near_le` — the *near-diagonal* Perron error, whose factor
`2(N+1)` has been removed.  That last point is what makes this usable: the uniform-separation form
carries `2(N+1)·B·x^σ·(1+log M)/(πT) ≍ N²`, hopeless at any admissible height, while the
near-diagonal form carries `B·x^σ(5(1+log M) + 4(1+log N))/(πT) ≍ N·(log N)⁵/n`.

```text
norm_ghsOuterBlock_le :  ‖ghsOuterBlock f N A B p‖ ≤ (1/log 2)·log p
norm_ghsBlockTriple_le : ‖(blk ⍟ (ghsInner f M ⍟ truncSeq f N))(i)‖
                           ≤ (log(B·M·N))⁴/(log 2)³        -- uniformly in i
ghs_block_perron_error_le :  the truncated-Perron discrepancy is at most
  ((log(B·M·N))⁴/(log 2)³)·(N+½)^σ·(5(1 + log(B·M·N)) + 4(1 + log N))/(π·n)
```

### `Sieve/GhsBlockExplicit.lean`

```text
ghsPerronError N B M n σ := that closed form

ghs_block_D_geometric_explicit :  k ≥ 1, threshold, 2 ≤ ⌊N/B_k⌋, n² ≤ A_k, e⁴ ≤ n, height →
  ‖∑_{i≤N} (blk_k ⍟ (ghsInner f (N/A_k) ⍟ f))(i)‖
    ≤ ghsPerronError N B_k (N/A_k) n σ
        + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst

ghs_block_D_trimmed_explicit :  the same for (n², ghsBlockRight N 0]
```

**No block hypothesis is left open.**  What remains is a threshold on `N`, the condition `n² ≤ A_k`,
and one inequality on the height.  Counting: `ghsPerronError ≍ N(log N)⁵/n`, so `K ≍ log log N`
blocks give `N(log N)⁵ log log N/n`, which after division by `log N` is `o(N)` once
`n ≫ (log N)⁴ log log N`; the domination asks `n ≫ (log N)³`; and `n² ≤ ghsBlockLeft N 1 ≍ N^{1/2}`
allows `n` up to `N^{1/4}`.  A height that is any fixed power `(log N)^c`, `c ≥ 5`, satisfies all
three.

### What is left

The explicit `n` and `σ`, and the sum over the blocks.

## 2026-08-10 unit 5, part 6: the assembly — no block hypothesis remains

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
`lake build GaloisForLFunctions.RHTower.Sieve.GhsAssembly` succeeds (9270 jobs).
(The full `RHTower` umbrella currently fails in an untracked module of a concurrent agent,
`RHTower/XiShiftedHankelCassiniInverseResponseCurvature.lean`; nothing in this chain touches it.)

### `Sieve/GhsUniformError.lean`

`ghsPerronError N B M n σ` depends on the block only through `log(B·M·N)`, and every block has
`B ≤ N`, `M ≤ N`, so `log(B·M·N) ≤ 3 log N` and

```text
ghsUniformError N n σ := ((3 log N)⁴/(log 2)³)·(N+½)^σ·(5(1 + 3 log N) + 4(1 + log N))/(π n)
ghsPerronError_le_uniform :  B ≤ N, M ≤ N  →  ghsPerronError N B M n σ ≤ ghsUniformError N n σ
```

dominates them all.  This is what lets the capstone be applied unchanged — it asks for one bound
valid for every block, and using the maximum instead of the individual errors costs one factor
`K ≍ log log N`, which the final division by `log N` absorbs.

### `Sieve/GhsAssembly.lean`

```text
norm_sum_Icc_le_ghs_partition :
  f completely multiplicative with f 1 = 1, ‖f‖ ≤ 1, 1 < σ, 1 ≤ z, 0 ≤ δ,
  δ ≤ 𝔻(f, n^{iy}) for |y| ≤ n, e⁴ ≤ n, 2 ≤ N, n² ≤ N, 2 ≤ ⌊N/n²⌋, n² ≤ ghsBlockRight N 0,
  thresholds/height/left-endpoint conditions for k < K, N/2 ≤ ghsPart N n (K+1),
  ghsUniformError N n σ ≤ E, small-block bound ≤ E  →
    ‖∑_{m ≤ N} f(m)‖
      ≤ ( ghsRecursionError N
            + (K+1)·(E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst) )
          / log N
```

The three block types dispatch by index: `k = 0` is `(1, n²]` via `norm_sum_Icc_ghs_small_block_le`,
`k = 1` is the trimmed block via `ghs_block_D_trimmed_explicit`, and `k ≥ 2` is the geometric block
of index `k − 1` via `ghs_block_D_geometric_explicit`, the identification being `ghsPart_succ_eq`
and `ghsBlockRight_eq_left_succ`.

**No hypothesis about any individual block survives.**  Everything left is a condition on
`N, n, σ, δ, z, K, E`.

### What is left

The choice of `n`, `σ`, `z`, `δ`, `K` as functions of `N`, and the verification that the stated
conditions hold for large `N`.  The counting is already fixed: `n = (log N)^c` with `c ≥ 5`,
`K ≍ log log N`, `σ = 1 + 1/log z`, and `E ≍ N(log N)⁵/n + N log n`.
