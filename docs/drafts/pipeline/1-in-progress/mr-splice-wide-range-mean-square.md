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

## 2026-08-10 unit 5, part 7: the geometric partition cannot reach `N/2`

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
`lake build GaloisForLFunctions.RHTower.Sieve.GhsFullAssembly` succeeds (9272 jobs).

A second incompatibility found by trying to instantiate, not by reading:

* the capstone's coverage condition needs the endpoints to reach `N/2` — the value beyond which
  `ghsOuter` vanishes, so `2^K ≥ (log N)/log 3` is forced;
* the geometric threshold `2^{k+1}·4 log 2 ≤ log N` caps `2^K ≤ (log N)/(8 log 2)`.

`(log N)/(8 log 2) ≈ 0.18 log N < 0.91 log N ≈ (log N)/log 3`, so **no admissible `K` does both**.
The geometric partition reaches only `ghsBlockLeft N K ≤ N/256`.

The leftover `(ghsBlockLeft N K, N]` needs no mean-square estimate.  There `log⌊N/p⌋ ≤ log 256` is
bounded, so the sharp denominator is worthless — but Mertens' first theorem *on a block* bounds the
outer weights' `1/p`-mass by `(log B − log A + C)/log 2`, an absolute constant for this block, and
the inner range `N/A` is bounded too.

```text
sum_Icc_norm_ghsOuterBlock_div_le_gap :  1 ≤ A ≤ B ≤ N →
  ∑_{p ≤ N} ‖ghsOuterBlock f N A B p‖/p ≤ (log B − log A + C)/log 2

norm_sum_Icc_ghs_block_trivial_le :  1 ≤ A ≤ B ≤ N, 1 ≤ M ≤ N →
  ‖∑_{i≤N} (blk ⍟ (ghsInner f M ⍟ f))(i)‖
    ≤ N·((log B − log A + C)/log 2)·(log M + log 4)
```

This is the general form of `norm_sum_Icc_ghs_small_block_le`, and neither dominates the other:
for `(1, n²]` the denominator `log⌊N/P⌋ ≍ log N` is large and worth keeping; for the top block it is
bounded and `log 2` is the right denominator.  The argument uses both.

```text
ghsPartTop N n K j := if j ≤ K + 1 then ghsPart N n j else N

norm_sum_Icc_le_ghs_full :
  f completely multiplicative with f 1 = 1, ‖f‖ ≤ 1, 1 < σ, 1 ≤ z, 0 ≤ δ,
  δ ≤ 𝔻(f, n^{iy}) for |y| ≤ n, e⁴ ≤ n, 2 ≤ N, n² ≤ N, 2 ≤ ⌊N/n²⌋, n² ≤ ghsBlockRight N 0,
  threshold/coverage/height conditions for k < K, and three error levels ≤ E  →
    ‖∑_{m ≤ N} f(m)‖
      ≤ ( ghsRecursionError N
            + (K+2)·(E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst) )
          / log N
```

Four block types — small `(1, n²]`, trimmed `(n², ghsBlockRight N 0]`, geometric `(A_k, B_k]` for
`1 ≤ k < K`, top `(ghsPart N n (K+1), N]` — and **no hypothesis about any of them survives**.

### What is left

The choice of `n, σ, z, δ, K` as functions of `N`, and the verification of the remaining conditions
for large `N`.

## 2026-08-10 unit 5, part 8: the parameters reduced

`Sieve/GhsParameterReduction.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`,
wired, builds clean (9273 jobs).

Four of the conditions of `norm_sum_Icc_le_ghs_full` are consequences of the others:

```text
ghsScale_le_ghsBlockRight_zero :  ghsScale N 1 ≤ ghsBlockRight N 0
   -- the square-root scale is below its own complement, since ⌊√N⌋² ≤ N
two_le_div_ghsBlockRight :  2^{k+1}·log 2 ≤ log N →  2 ≤ ⌊N/B_k⌋
```

together with the monotonicity of `ghsBlockLeft` (which turns `n² ≤ ghsBlockRight N 0` into
`n² ≤ A_k` for every `k ≥ 1`) and the monotonicity of `2^{k+1}` and `4^{k+1}` in `k` (which turns
the last block's threshold and height inequality into all of them).  So:

```text
norm_sum_Icc_le_ghs_reduced :
  f completely multiplicative with f 1 = 1, ‖f‖ ≤ 1, 1 < σ, 1 ≤ z, 0 ≤ δ,
  δ ≤ 𝔻(f, n^{iy}) for |y| ≤ n,
  e⁴ ≤ n,  2 ≤ N,  n² ≤ N,  2 ≤ ⌊N/n²⌋,  n² ≤ ghsScale N 1,
  2^K·4·log 2 ≤ log N,
  (5/4n)·(16/9)·4^K·(log N + log 4) ≤ 1750·ghsShapeConst,
  three error levels ≤ E  →
    ‖∑_{m ≤ N} f(m)‖
      ≤ ( ghsRecursionError N
            + (K+2)·(E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst) )
          / log N
```

Every surviving hypothesis is a scalar inequality in `N`, `n`, `K`, `σ`, `E` — no block, no
partition, no index.  Reading them as constraints on the height and the number of scales:

| condition | asks |
|---|---|
| `n² ≤ ghsScale N 1` | `n ≤ N^{1/4}` |
| `2^K·4 log 2 ≤ log N` | `2^K ≤ (log N)/(4 log 2)` |
| height at `4^K` | `n ≳ 4^K·log N ≍ (log N)³` |
| `ghsUniformError ≤ E` | `E ≳ N(log N)⁵/n` |
| small block `≤ E` | `E ≳ N log n` |
| top block `≤ E` | `E ≳ N` |

The three error levels and the two constraints on `n` are simultaneously satisfiable: `n = (log N)^c`
for any `c ∈ [3, ∞)` fits below `N^{1/4}`, and `E ≍ N(log N)^{5−c} + N log log N`.

### What is left

The choice of `n, σ, z, δ, K` as functions of `N` and the asymptotic verification of the six rows
above.

## 2026-08-10 unit 5, part 9: the scale count, the total error, and the height window

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`, wired, both build clean
(9274, 9275 jobs).

### `Sieve/GhsScaleCount.lean`

```text
ghsScaleCount N := Nat.log 2 ⌊(log N)/(4 log 2)⌋
two_pow_ghsScaleCount_le  :  16 ≤ N →  2^K·4·log 2 ≤ log N
four_pow_ghsScaleCount_le :  16 ≤ N →  4^K ≤ ((log N)/(4 log 2))²

ghsTotalError N n K σ := max (uniform Perron error) (max (small-block) (top-block))
norm_sum_Icc_le_ghs_total :  the mean value with the three error hypotheses discharged
```

The scale count is the largest the threshold permits, `Nat.pow_log_le_self` doing the work; the
three error levels are explicit, so their common bound is their maximum, and `hE1, hE2, hE3`
disappear into `le_max_*`.

### `Sieve/GhsHeightWindow.lean`

```text
ghs_height_of_scaleCount :  16 ≤ N, 1 ≤ n,
  (5/4n)·(16/9)·((log N)/(4 log 2))²·(log N + log 4) ≤ 1750·ghsShapeConst  →
    the height inequality at K = ghsScaleCount N

norm_sum_Icc_le_ghs_window :
  f completely multiplicative with f 1 = 1, ‖f‖ ≤ 1, 1 < σ, 1 ≤ z, 0 ≤ δ,
  δ ≤ 𝔻(f, n^{iy}) for |y| ≤ n,
  e⁴ ≤ n,  16 ≤ N,  n² ≤ N,  2 ≤ ⌊N/n²⌋,  n² ≤ ghsScale N 1,
  (5/4n)·(16/9)·((log N)/(4 log 2))²·(log N + log 4) ≤ 1750·ghsShapeConst  →
    ‖∑_{m ≤ N} f(m)‖
      ≤ ( ghsRecursionError N
            + (ghsScaleCount N + 2)
              ·(ghsTotalError N n (ghsScaleCount N) σ
                  + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst) )
          / log N
```

**No partition, no block, no scale index appears in the hypotheses.**  What is left is `N ≥ 16`,
the distance data `(z, δ)`, and a height `n` in the window

```text
(log N)³ ≪ n ≪ N^{1/4} ,
```

the lower end from the height inequality and the upper end from `n² ≤ ghsScale N 1 = ⌊N^{1/2}⌋`.

### What is left

Exhibiting a height in the window for large `N` — an asymptotic comparison of `(log N)³` with
`N^{1/4}` — and the choice of `σ` and of the distance data.

## 2026-08-10 unit 5, part 10: a height inside the window

`Sieve/GhsHeightChoice.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9276 jobs).

```text
ghsHeight N := ⌊(log N)⁴⌋ + 1
log_pow_le_ghsHeight :  (log N)⁴ ≤ ghsHeight N
ghsHeight_le :  1 ≤ (log N)⁴ →  ghsHeight N ≤ 2(log N)⁴

eventually_pow_log_le_ghsScale :  ∀ᶠ N,  4(log N)⁸ ≤ ghsScale N 1
ghs_height_inequality :  3 ≤ log N,  (log N)⁴ ≤ n  →
  (5/4n)·(16/9)·((log N)/(4 log 2))²·(log N + log 4) ≤ 1750·ghsShapeConst
```

Two observations worth keeping.

**The height inequality needs no asymptotics.**  With `n ≥ (log N)⁴` the left-hand side is at most
`10/9`, uniformly in `N` once `log N ≥ 3`, while `ghsShapeConst = (3 + C)(3 + log 4) ≥ 9` makes the
right-hand side at least `15750`.  The margin is a factor `14000`; the condition was never
quantitatively delicate, only structurally necessary.

**One asymptotic comparison carries the whole construction.**  `eventually_pow_log_le_ghsScale` is
`log =o(x^{1/16})` raised to the eighth power, giving `4(log N)⁸ ≤ ½·N^{1/2} ≤ ⌊N^{1/2}⌋`.  Combined
with `ghsHeight N ≤ 2(log N)⁴` it yields `(ghsHeight N)² ≤ ghsScale N 1` — the upper end of the
window.  Everything else in units 5–6 is an inequality between explicit closed forms.

### What is left

Assembling `ghsHeight` into `norm_sum_Icc_le_ghs_window` as an eventual statement, and the choice of
`σ` and the distance data `(z, δ)`.

## 2026-08-10 unit 5 closed: the mean value, eventually

`Sieve/GhsEventual.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9277 jobs).

```text
exp_four_le :  e⁴ ≤ 81

eventually_ghsHeight_admissible :  ∀ᶠ N,
  16 ≤ N ∧ 3 ≤ log N ∧ e⁴ ≤ ghsHeight N ∧ (ghsHeight N)² ≤ N
    ∧ 2 ≤ ⌊N/(ghsHeight N)²⌋ ∧ (ghsHeight N)² ≤ ghsScale N 1

eventually_norm_sum_Icc_le_ghs :
  f completely multiplicative with f 1 = 1, ‖f‖ ≤ 1  →
  ∀ᶠ N,  ∀ z σ δ,  1 < σ → 1 ≤ z → 0 ≤ δ →
    (δ ≤ 𝔻(f, n^{iy}) for |y| ≤ ghsHeight N)  →
      ‖∑_{m ≤ N} f(m)‖
        ≤ ( ghsRecursionError N
              + (ghsScaleCount N + 2)
                ·(ghsTotalError N (ghsHeight N) (ghsScaleCount N) σ
                    + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst) )
            / log N
```

**Unit 5 is closed.**  There is no free parameter and no block hypothesis: the height, the scale
count, the partition and the error level are all defined functions of `N`, and the only input is
the multiplicative distance.

One point of shape deserves recording.  The distance data `(z, σ, δ)` is quantified *inside* the
eventual statement, not before it.  That is forced: `δ` bounds `𝔻(f, n^{iy})` on `|y| ≤ ghsHeight N`,
a range growing with `N`, so a `δ` fixed in advance would have to bound the distance on the whole
line — the same unsatisfiable condition that was removed from `ghs_block_bound_uniform` in part 1.
Halász's theorem has exactly this shape: the `m` in `(1+m)e^{−m}` depends on both `x` and the height.

### What is left for `MRBilinear`

Nothing in the mean-value chain.  What remains is to feed this bound to the Matomäki–Radziwiłł
reduction: instantiate `f` at the relevant multiplicative function, choose `z` and `σ = 1 + 1/log z`,
and read `dampedSize σ δ z N ≍ (log z)e^{−δ²}` against the corpus's distance lower bounds.

## 2026-08-10 correction: the height exponent 4 gives a true but useless bound

`ghsHeight` raised from `⌊(log N)⁴⌋+1` to `⌊(log N)⁶⌋+1`; `GhsHeightChoice` and `GhsEventual`
rebuilt, unconditional, `[propext, Classical.choice, Quot.sound]`, clean (9277 jobs).

Checking the endpoint against the trivial bound — the test that should be run on any chain before
declaring it finished — shows exponent 4 is too small.  At `n ≍ (log N)⁴`:

```text
ghsUniformError ≍ N(log N)⁵/n ≍ N log N ,
```

so `K·ghsUniformError/log N ≍ N·log log N`, **worse than the trivial bound `N`**.  The chain was
correct and the conclusion vacuous.  The requirement is `n ≫ (log N)⁴·log log N`, already recorded
in part 5 but not honoured by the choice made in part 10.

At `n ≍ (log N)⁶` every term is `o(N)`:

| term | size after dividing by `log N` |
|---|---|
| `ghsRecursionError N` | `N·log log N/log N` |
| `K·ghsUniformError` | `N·log log N/(log N)²` |
| `K·(small block)` | `N·(log log N)²/log N` |
| `K·(top block)` | `N·log log N/log N` |
| `K·(1/2π)·dampedSize·(N+½)^σ·C` | `N·log z·e^{−δ²}·log log N/log N` |

The first four are unconditionally `o(N)`; the last is the Halász term and is `o(N)` exactly when
`e^{−δ²}·log z·log log N = o(log N)` — the multiplicative-distance hypothesis, as it should be.

The upper end of the window moves accordingly: `(ghsHeight N)² ≤ 4(log N)¹² ≤ ⌊N^{1/2}⌋`, so
`eventually_pow_log_le_ghsScale` is now `log =o(x^{1/24})` raised to the twelfth power.  The height
inequality is unaffected — it only needs `n ≥ (log N)⁴`, and `(log N)⁶ ≥ (log N)⁴`.

## 2026-08-10 unit 5, part 11: the first two rows of the table, proved

`Sieve/GhsSizeBounds.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9278 jobs).

```text
mertensTail_nonneg :  0 ≤ mertensTail
tendsto_log_log_div_log :  log(log N)/log N → 0            -- log =o(id), composed with log
tendsto_log_natCast_atTop :  log N → ∞
ghsScaleCount_le :  16 ≤ N →  ghsScaleCount N ≤ (log log N)/log 2
tendsto_ghsRecursionError_div :  ghsRecursionError N /(N·log N) → 0
```

`ghsScaleCount_le` is `Nat.pow_log_le_self` read through the logarithm: `2^K ≤ ⌊(log N)/(4 log 2)⌋`
gives `K·log 2 ≤ log((log N)/(4 log 2)) ≤ log log N`.  `tendsto_ghsRecursionError_div` needs
`log(Nat.log 2 N) ≤ log log N + 1`, which is `Nat.log 2 N ≤ (log N)/log 2` together with
`−log(log 2) ≤ 1`, i.e. `log 2 ≥ e^{−1}`.

These are the first two rows of the size table.  Both are `N` times a power of `log log N` over a
power of `log N`, which is the shape of every unconditional term in the bound, so the same two
lemmas serve for the rest.

### What is left

The remaining three rows — `K·ghsUniformError`, `K·(small block)`, `K·(top block)` — and then the
statement `‖∑_{m ≤ N} f(m)‖ = o(N)` under the distance hypothesis.

## 2026-08-10 unit 5, part 12: the truncation row

`Sieve/GhsUniformErrorBound.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9279 jobs).

```text
ghsErrorConst := 5346/((log 2)³·π)

ghsUniformError_le :  3 ≤ log N,  (log N)⁶ ≤ n,  (N+½)^σ ≤ 3N  →
  ghsUniformError N n σ ≤ ghsErrorConst · N/log N

tendsto_ghsScaleCount_div_log :  ghsScaleCount N / log N → 0
```

The chain is `81(log N)⁴/(log 2)³ · 3N · 22 log N / (π (log N)⁶)`: the height's sixth power beats
the numerator's fifth, leaving one power of `log N` in the denominator.  No numerics — the constant
is carried symbolically, since `5·(1+3L) + 4·(1+L) ≤ 22L` already at `L ≥ 3`.

The abscissa enters only through `(N+½)^σ`, hence the hypothesis `(N+½)^σ ≤ 3N`: satisfied by
`σ = 1 + 1/log N`, and by any `σ = 1 + 1/log z` with `z ≥ N`.  That is the third row of the size
table, and with `tendsto_ghsScaleCount_div_log` the product `K·ghsUniformError/(N log N)` is
`ghsErrorConst·(K/log N)·(1/log N) → 0`.

### What is left

The small-block and top-block rows, and then `‖∑_{m ≤ N} f(m)‖ = o(N)` under the distance
hypothesis.

## 2026-08-10 unit 5, part 13: the small-block row

`Sieve/GhsSmallBlockBound.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9280 jobs).

```text
ghs_small_block_le :  3 ≤ log N,  16 ≤ N,  (ghsHeight N)² ≤ ghsScale N 1  →
  N·((log (ghsHeight N)² + log 4)/log⌊N/(ghsHeight N)²⌋)·(log N + log 4)
    ≤ N·(32 log 2 + 96 log log N)
```

The mechanism is that the sharp denominator earns its keep here.  `n² ≤ ghsScale N 1` makes the
complement `⌊N/n²⌋` at least `ghsScale N 1`, so

```text
log⌊N/n²⌋ ≥ (log N)/2 − log 2 ≥ (log N)/4 ,
```

which cancels the last factor `log N + log 4 ≤ 2 log N` outright, leaving only the numerator's
`log n² ≤ 4 log 2 + 12 log log N`.  This is why the small block was given its own bound rather than
being folded into `norm_sum_Icc_ghs_block_trivial_le`: the general form divides by `log 2` and would
have left a full factor `log N`.

Four of the five rows are now proved: `ghsRecursionError = o(N log N)`,
`ghsScaleCount = o(log N)`, `ghsUniformError ≤ ghsErrorConst·N/log N`, and the small block
`≤ N·(32 log 2 + 96 log log N)`.

### What is left

The top-block row — which needs `ghsScale N (ghsScaleCount N)` bounded by an absolute constant,
from `Nat.lt_pow_succ_log_self` — and then `‖∑_{m ≤ N} f(m)‖ = o(N)` under the distance hypothesis.

## 2026-08-10 unit 5, part 14: the last scale is an absolute constant

`Sieve/GhsTopScale.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9281 jobs).

```text
ghsScale_scaleCount_le :  65536 ≤ N →  ghsScale N (ghsScaleCount N) ≤ 2048
ghsBlockLeft_scaleCount_ge :  65536 ≤ N →  ⌊N/2048⌋ ≤ ghsBlockLeft N (ghsScaleCount N)
```

The threshold gives `2^K ≤ (log N)/(4 log 2)` and `Nat.lt_pow_succ_log_self` gives the matching
lower bound `2^K > m/2` for `m = ⌊(log N)/(4 log 2)⌋`; with `m ≥ 4` these combine to
`2^K > 3(log N)/(32 log 2)`, so the exponent obeys `(log N)/2^K < (32 log 2)/3 ≤ 11 log 2` and

```text
ghsScale N K = ⌊N^{1/2^K}⌋ ≤ 2^{11} = 2048 .
```

This quantifies part 7's incompatibility: the geometric partition stops at `ghsBlockLeft N K`, which
is between `N/2048` and `N/256`, never reaching the `N/2` the coverage condition needs.  The gap is
a bounded factor, which is why the top block's trivial bound costs only `O(N)` — the last row of the
size table.

### What is left

The top-block row itself (assembling this constant into `norm_sum_Icc_ghs_block_trivial_le`'s
bound), and then `‖∑_{m ≤ N} f(m)‖ = o(N)` under the distance hypothesis.

## 2026-08-10 unit 5, part 15: the top-block row — the size table is complete

`Sieve/GhsTopBlockBound.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9282 jobs).

```text
ghsTopConst := ((log 4096 + C)/log 2)·(log 4096 + log 4)

ghs_top_block_le :  65536 ≤ N,  n² ≤ N  →
  N·((1/log 2)·(log N − log(ghsPart N n (K+1)) + C))·(log⌊N/ghsPart N n (K+1)⌋ + log 4)
    ≤ N·ghsTopConst
```

Both quantities are bounded because `⌊N/2048⌋ ≤ ghsPart N n (K+1) ≤ N`: the width is
`log N − log(N/4096) = log 4096`, and the inner range is `⌊N/(N/2048)⌋ < 4096` by
`div_div_lt_two_mul`.

### The size table, all five rows proved

| term | bound | reference |
|---|---|---|
| `ghsRecursionError N` | `o(N log N)` | `tendsto_ghsRecursionError_div` |
| `ghsScaleCount N` | `o(log N)` | `tendsto_ghsScaleCount_div_log` |
| `ghsUniformError` | `ghsErrorConst·N/log N` | `ghsUniformError_le` |
| small block `(1, n²]` | `N(32 log 2 + 96 log log N)` | `ghs_small_block_le` |
| top block | `N·ghsTopConst` | `ghs_top_block_le` |

Every unconditional term of the mean value is therefore `o(N·log N)`, and after division by `log N`
the bound reads

```text
‖∑_{m ≤ N} f(m)‖ ≤ o(N) + (K+2)·(1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst .
```

The surviving term is the Halász term and nothing else.

### What is left

Assembling the five rows into `‖∑_{m ≤ N} f(m)‖ = o(N)` under the distance hypothesis
`e^{−δ²}·log z·log log N = o(log N)`.

## 2026-08-10 unit 5, part 16: the five rows collapse into one

`Sieve/GhsTotalErrorBound.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9283 jobs).

```text
tendsto_sq_log_div_atTop :  (log t)²/t → 0
tendsto_sq_log_log_div_log :  (log log N)²/log N → 0

ghsTotalError_le :  3 ≤ log N,  65536 ≤ N,  (ghsHeight N)² ≤ ghsScale N 1,
  (ghsHeight N)² ≤ N,  (N+½)^σ ≤ 3N  →
    ghsTotalError N (ghsHeight N) (ghsScaleCount N) σ
      ≤ N·(ghsErrorConst + ghsTopConst + 32 log 2 + 96 log log N)

tendsto_ghsTotalError_majorant (C) :
  (ghsScaleCount N + 2)·(C + 96 log log N)/log N → 0
```

The maximum of the three error levels is bounded by their sum, and each is `N` times either a
constant or `log log N`.  The majorant then splits into four pieces — `C·K/log N`, `2C/log N`,
`96·K·log log N/log N`, `192·log log N/log N` — of which only the third is new, and it is
`(log log N)²/log N` after `ghsScaleCount_le`.

That is the second and last asymptotic input of the whole construction: `log =o(x^{1/24})` for the
height window, and `(log t)² = o(t)` here.  Everything else is an inequality between closed forms.

### What is left

`‖∑_{m ≤ N} f(m)‖ = o(N)` under the distance hypothesis: combine
`eventually_norm_sum_Icc_le_ghs` with `tendsto_ghsRecursionError_div`, `ghsTotalError_le` and
`tendsto_ghsTotalError_majorant`, leaving only the Halász term
`(K+2)·(1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst / (N log N)`.

## 2026-08-10 unit 5 CLOSED IN FULL: the mean value per unit

`Sieve/GhsMeanValueDiv.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9284 jobs).

```text
ghsErrConstTotal := ghsErrorConst + ghsTopConst + 32 log 2

eventually_norm_sum_Icc_div_le :
  f completely multiplicative with f 1 = 1, ‖f‖ ≤ 1  →
  ∀ᶠ N,  ∀ z σ δ,  1 < σ → 1 ≤ z → 0 ≤ δ → (N+½)^σ ≤ 3N →
    (δ ≤ 𝔻(f, n^{iy}) for |y| ≤ ghsHeight N)  →
      ‖∑_{m ≤ N} f(m)‖/N
        ≤ ghsRecursionError N/(N log N)
          + (ghsScaleCount N + 2)·(ghsErrConstTotal + 96 log log N)/log N
          + (ghsScaleCount N + 2)·(1/2π)·dampedSize σ δ z N·(N+½)^σ
              ·ghsBlockConstOf σ ghsShapeConst/(N log N)

tendsto_ghs_unconditional_part :  the first two terms → 0
```

**The Granville–Harper–Soundararajan chain is complete.**  The mean value per unit is bounded by an
unconditional part that provably vanishes plus one Halász term, and the Halász term is the only
place the multiplicative distance appears.  Explicitly, the bound is `o(1)` as soon as

```text
e^{−δ²}·log z·log log N = o(log N) ,
```

which is the hypothesis Halász's theorem is stated under.

Every constant is explicit: `ghsErrorConst = 5346/((log 2)³π)`,
`ghsTopConst = ((log 4096 + C)/log 2)(log 4096 + log 4)`,
`ghsShapeConst = (3 + C)(3 + log 4)`, `ghsBlockConstOf σ Γ = √((2π)²(7/σ²+1)((5/4)701)(2·1750Γ))`,
with `C = mertensBlockGapConst`.  The whole construction rests on exactly two asymptotic facts,
`log =o(x^{1/24})` and `(log t)² = o(t)`; everything else is arithmetic between closed forms.

### What is left for `MRBilinear`

Nothing in the mean-value chain.  The remaining work is the Matomäki–Radziwiłł reduction itself:
`AveragedShortInterval μ hh`, which is a short-interval statement and needs the Parseval/Dirichlet
polynomial decomposition, not another mean-value estimate.

## 2026-08-10 the frontier after the mean value: where `MRBilinear` actually stands

With the Halász chain closed, an audit of what still separates the corpus from `MRBilinear`.  The
reduction is far shorter than the card's earlier text suggests — the corpus already owns every step
except one analytic theorem.

```text
MRBilinear μ hh
  ← MRBilinear_moebius_of_averaged            (MRFibreReduction)
  ← AveragedShortInterval μ hh
  ← averagedShortInterval_of_meanSquare        (PairFibreMeanSquare; Cauchy–Schwarz over the block)
  ← AveragedMeanSquare μ hh
  ← averagedMeanSquare_of_maximal              (FibreStartSeparation)
  ← MaximalWindowMeanSquare μ hh :
      ∑_{y ∈ [√x/2, √x]} max_{m ≤ h} (∑_{b ∈ [y, y+m]} μ(b))² = o(h²·√x)
```

That last line **is** Matomäki–Radziwiłł.  Everything above it is proved here.  Also already owned:
`innerFibre_eq` (the fibre is the integer interval `[⌈x/a⌉, ⌊(x+h√x)/a⌋]`), Gallagher's lemma
(`gallagher_identity`, `gallagher_le_of_sup`) and Gallagher's Sobolev lemma (`gallagher_sobolev`).

Two obstructions remain, in order:

1. **The supremum over window lengths.**  The fibre length varies with `a`, so the sum really is
   over a *choice* `m(y)` of length per starting point, and no crude removal of the supremum works:
   `max_{m≤H} S_m² ≤ (H+1)∑_{m≤H} S_m²` loses `H²` against the target.  What is needed is
   Rademacher–Menshov — a dyadic decomposition costing only `(log H)²`.
2. **The Gallagher–Halász bridge**: convert `∑_y S(y)²` into `∫ |logPoly|²` and control the
   integral by the large-values/Halász machinery, which is where the mean value just built enters.

### `Sieve/WindowPartialSum.lean` — the first brick

Unconditional, `[propext, Classical.choice, Quot.sound]`, wired, builds clean (9005 jobs).

```text
partialSum f n := ∑_{b ≤ n} f(b)
window_eq_partialSum :  1 ≤ y →  ∑_{b ∈ [y, y+m]} f(b) = P(y+m) − P(y−1)
window_split :  splitting a window is a telescoping identity on P
maxWindowSq_eq_partial :  maxWindowSq f H y = max_{m ≤ H} (P(y+m) − P(y−1))²
```

Every maximal inequality is a statement about partial sums, not windows; with this rewriting the
supremum becomes the maximal deviation of `P` from its value at the left endpoint, which is the
classical setting for Rademacher–Menshov, and window splitting costs nothing.

## 2026-08-10 obstruction 1, first step: the halving step of Rademacher–Menshov

`Sieve/MaximalDeviation.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9006 jobs).

```text
maxDev P J y := max_{k ≤ 2^J} |P(y+k) − P(y)|

maxDev_nonneg, le_maxDev, maxDev_zero :  maxDev P 0 y = |P(y+1) − P(y)|

maxDev_succ_le :
  maxDev P (J+1) y ≤ |P(y+2^J) − P(y)| + max (maxDev P J y) (maxDev P J (y+2^J))
```

The halving step is the whole structural content: a deviation over `2^{J+1}` steps either stays in
the first half, or crosses the midpoint, and then it is the midpoint's own deviation plus a
deviation over `2^J` steps starting at the midpoint.  Iterating `J` times leaves `J` block sums,
and Cauchy–Schwarz turns those into `J·∑(block sum)²` — the `(log H)²` loss.

This is the only route: the crude bounds all fail.  `max_{m≤H} S_m² ≤ (H+1)∑_{m≤H} S_m²` loses `H²`
against the target `o(h²√x)`, and `max_m |S_m| ≤ ∑_m |S_m|` is worse.  The dyadic decomposition is
what makes the loss logarithmic, and the halving step is the induction that produces it.

### What is left

Iterating the halving step into the full Rademacher–Menshov bound
`maxDev P J y ≤ ∑_{j<J} (max over aligned blocks of level j)`, then squaring; and after that
obstruction 2, the Gallagher–Halász bridge.

## 2026-08-10 obstruction 1: Rademacher–Menshov proved

`Sieve/RademacherMenshov.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9007 jobs).

```text
levelMax P J j y := max_{i < 2^{J−j}} |P(y + (i+1)·2^j) − P(y + i·2^j)|

levelMax_mono  :  j ≤ J →  levelMax P J j y ≤ levelMax P (J+1) j y
levelMax_shift :  j ≤ J →  levelMax P J j (y + 2^J) ≤ levelMax P (J+1) j y

maxDev_le_sum_levelMax :
  maxDev P J y ≤ levelMax P J 0 y + ∑_{j < J} levelMax P J j y
```

The supremum over all window lengths is gone, replaced by `J + 1` block maxima, one per dyadic
level.  The induction is the halving step of the previous unit; the two monotonicity lemmas are
what make it close — `levelMax_shift` says the second half's level-`j` blocks are among the whole
window's, by the index identity `y + 2^J + i·2^j = y + (i + 2^{J−j})·2^j`, valid exactly when
`j ≤ J`.

Level `0` appears twice because the induction bottoms out at `maxDev P 0 y = |P(y+1) − P(y)|`,
itself a level-`0` block.

Squaring by Cauchy–Schwarz now costs `J + 1 ≍ log H`, giving the `(log H)²` loss — the only loss
compatible with the target `o(h²√x)`.

### What is left

Squaring and summing over the starting points `y` (turning each `levelMax` into a sum of squares
over its blocks), which reduces `MaximalWindowMeanSquare` to a *plain* dyadic mean square; then
obstruction 2, the Gallagher–Halász bridge.

## 2026-08-10 obstruction 1 CLOSED: the supremum is gone

`Sieve/DyadicMeanSquare.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9008 jobs).

```text
blockSq P J j y := ∑_{i < 2^{J−j}} (P(y + (i+1)·2^j) − P(y + i·2^j))²

levelMax_sq_le :  (levelMax P J j y)² ≤ blockSq P J j y
maxDev_sq_le   :  (maxDev P J y)² ≤ (J + 1)·(blockSq P J 0 y + ∑_{j < J} blockSq P J j y)
```

**The first obstruction is closed.**  The right-hand side has no supremum in it: it is a plain sum
of squares of dyadic block increments, which is what Gallagher's lemma and Parseval evaluate.  The
loss is `(J + 1)² ≍ (log H)²` — one factor from the sum over levels, one from Cauchy–Schwarz — and
the failed crude alternatives showed nothing smaller is available.

The chain from `MRBilinear` now reads

```text
MRBilinear μ hh
  ← AveragedShortInterval  ← AveragedMeanSquare  ← MaximalWindowMeanSquare      (corpus)
  ← maxWindowSq_eq_partial ← maxDev_sq_le                                        (this and prior units)
  ← a plain dyadic mean square of Möbius block sums                              (obstruction 2)
```

### What is left

Obstruction 2 alone: bound `∑_y blockSq` — a mean square of Möbius sums over dyadic intervals — by
Gallagher's lemma and the Halász machinery of units 1–6.  That is the last analytic input.

## 2026-08-10 the two halves join: `MaximalWindowMeanSquare` is a dyadic mean square

`Sieve/MaximalWindowDyadic.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9009 jobs).

```text
maxWindowSq_le_maxDev_sq :  1 ≤ y,  H + 1 ≤ 2^J  →
  maxWindowSq f H y ≤ (maxDev (partialSum f) J (y−1))²

maxWindowSq_le_blockSq :  the same, composed with maxDev_sq_le  →
  maxWindowSq f H y ≤ (J+1)·(blockSq P J 0 (y−1) + ∑_{j<J} blockSq P J j (y−1))

sum_maxWindowSq_le :  1 ≤ A,  H + 1 ≤ 2^J  →
  ∑_{y ∈ [A,B]} maxWindowSq f H y
    ≤ (J+1)·∑_{y ∈ [A,B]} (blockSq P J 0 (y−1) + ∑_{j<J} blockSq P J j (y−1))
```

A window of length at most `H` from `y` is a deviation of the partial sums over at most `H + 1`
steps from `y − 1`; that single observation, together with the Rademacher–Menshov chain, converts
the Matomäki–Radziwiłł hypothesis into

```text
∑_{y ∈ [√x/2, √x]} ∑_{j ≤ log₂ h} ∑_{i} (block sum of μ over a dyadic interval)² = o(h²√x/log²h) ,
```

with no supremum and no varying window length.  Every length is now a power of two, every block is
aligned, and the only analytic input still needed is a mean-square bound for Möbius sums over
dyadic intervals — Gallagher plus the Halász machinery of units 1–6.

### The full reduction, as it now stands

```text
MRBilinear μ hh
  ← MRBilinear_moebius_of_averaged
  ← AveragedShortInterval μ hh          ← averagedShortInterval_of_meanSquare
  ← AveragedMeanSquare μ hh             ← averagedMeanSquare_of_maximal
  ← MaximalWindowMeanSquare μ hh        ← sum_maxWindowSq_le
  ← a dyadic mean square of Möbius block sums                    [obstruction 2, open]
```

Everything above the last line is proved unconditionally in this corpus.

## 2026-08-10 obstruction 2 reduced to a single quantity

`Sieve/DyadicTranslates.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9010 jobs).

```text
fixedWindowSq f ℓ z    := (P(z + ℓ) − P(z))²
dyadicMeanSquare f ℓ A B := ∑_{z ∈ [A,B]} fixedWindowSq f ℓ z

blockSq_eq_sum_fixedWindowSq :
  blockSq P J j y = ∑_{i < 2^{J−j}} fixedWindowSq f (2^j) (y + i·2^j)

sum_Icc_shift :  ∑_{y ∈ [A,B]} g(y + c) = ∑_{z ∈ [A+c, B+c]} g(z)

sum_blockSq_eq_translates :
  ∑_{y ∈ [A,B]} blockSq P J j y
    = ∑_{i < 2^{J−j}} dyadicMeanSquare f (2^j) (A + i·2^j) (B + i·2^j)
```

Exchanging the two summations shows the level-`j` block sums are `2^{J−j}` *translated copies* of
one mean square of windows of the fixed length `2^j`.  So the entire reduction — from `MRBilinear`
down — rests on the single quantity `dyadicMeanSquare f ℓ A B`, at the `log₂ h` dyadic lengths
`ℓ = 2^j`, and nothing else.

That is exactly the object Gallagher's lemma converts into an integral of `|logPoly|²`, and exactly
the object the Matomäki–Radziwiłł theorem estimates.  The reduction is now a single named target
rather than a family of statements about varying windows.

### What is left

A bound for `dyadicMeanSquare μ ℓ A B` — Gallagher plus the Halász machinery of units 1–6.  Every
other step from `MRBilinear` to that target is proved unconditionally in this corpus.

## 2026-08-10 the reduction, in one statement

`Sieve/MaximalWindowReduction.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`,
wired, builds clean (9011 jobs).

```text
sum_maxWindowSq_succ_le_dyadic :  H + 1 ≤ 2^J  →
  ∑_{y ∈ [A+1, B+1]} maxWindowSq f H y
    ≤ (J + 1)·( ∑_{i < 2^J} dyadicMeanSquare f 1 (A+i) (B+i)
                + ∑_{j < J} ∑_{i < 2^{J−j}} dyadicMeanSquare f (2^j) (A + i·2^j) (B + i·2^j) )
```

The left-hand side is what `MaximalWindowMeanSquare` averages.  The right-hand side involves only
`dyadicMeanSquare` at the `J + 1` dyadic lengths `1, 2, …, 2^{J−1}`, each over `O(2^J)` translates
of one range of starting points.  No supremum, no varying length, no unaligned block survives.

### Status of the `MRBilinear` path

| step | status |
|---|---|
| `MRBilinear μ hh ← AveragedShortInterval` | corpus |
| `AveragedShortInterval ← AveragedMeanSquare` | corpus |
| `AveragedMeanSquare ← MaximalWindowMeanSquare` | corpus |
| `maxWindowSq` as a partial-sum deviation | `WindowPartialSum` |
| halving step | `MaximalDeviation` |
| Rademacher–Menshov | `RademacherMenshov` |
| squaring, Cauchy–Schwarz | `DyadicMeanSquare` |
| windows → dyadic blocks | `MaximalWindowDyadic` |
| blocks → translates of one mean square | `DyadicTranslates` |
| the whole reduction, one statement | `MaximalWindowReduction` |
| **`dyadicMeanSquare μ ℓ A B`** | **open — the only remaining input** |

### What is left

One estimate: `dyadicMeanSquare μ ℓ A B` for dyadic `ℓ`.  Gallagher's lemma converts it into an
integral of `|logPoly|²`; the Halász machinery of units 1–6 bounds that integral.  Nothing else on
the path from `MRBilinear` is open.

## 2026-08-10 the dyadic mean square, expanded into pairs

`Sieve/DyadicPairExpansion.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9012 jobs).

```text
fixedWindowSq_eq :  1 ≤ ℓ →  fixedWindowSq f ℓ z = (∑_{b ∈ (z, z+ℓ]} f(b))²

dyadicMeanSquare_eq_pairs :  the square expanded into a double sum

dyadicMeanSquare_eq_count :  1 ≤ ℓ →
  dyadicMeanSquare f ℓ A B
    = ∑_{m, n ∈ (A, B+ℓ]} f(m)·f(n)·#{ z ∈ [A,B] : m, n ∈ (z, z+ℓ] }
```

An exact identity, not an estimate.  The kernel `#{z ∈ [A,B] : m, n ∈ (z, z+ℓ]}` is the discrete
overlap of two windows of common length `ℓ` — the integer analogue of the corpus's
`volume_real_logWindow_inter`, whose value is `(δ − |log m − log n|)₊`.  It vanishes as soon as
`|m − n| ≥ ℓ`, so the double sum is supported on the near-diagonal band, which is the structure the
whole estimate rests on.

The route from here follows the corpus's own Gallagher development: bound the kernel by
`(ℓ − |m − n|)₊`, recognise the resulting bilinear form as the one `gallagher_identity` evaluates,
and pass to `∫ |logPoly|²`.

### What is left

The kernel bound and the passage to `logPoly`, then the Halász estimate for that integral.

## 2026-08-10 the discrete overlap kernel

`Sieve/DyadicOverlapKernel.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9013 jobs).

```text
cast_max_sub_min :  ((max m n − min m n : ℕ) : ℝ) = |m − n|

overlap_card_le :
  #{ z ∈ [A,B] : m, n ∈ (z, z+ℓ] } ≤ (ℓ − |m − n|)₊
```

A starting point `z` serves both `m` and `n` exactly when `z + 1 ≤ min(m,n)` and
`max(m,n) ≤ z + ℓ`, so the admissible `z` form an interval, and its length is `ℓ − |m − n|` — with
the degenerate case handled by the positive part.  This is the integer analogue of the corpus's
`volume_real_logWindow_inter`, which gives `(δ − |log m − log n|)₊` for Gallagher's logarithmic
windows.

The kernel vanishes for `|m − n| ≥ ℓ`, so combined with `dyadicMeanSquare_eq_count` the mean square
is a bilinear form supported on a band of width `ℓ` around the diagonal:

```text
dyadicMeanSquare f ℓ A B ≤ ∑_{m, n ∈ (A, B+ℓ]} |f(m)|·|f(n)|·(ℓ − |m − n|)₊ ,
```

which is exactly the bilinear form `gallagher_identity` evaluates as `∫ (𝓕 triC)·|logPoly|²`.

### What is left

Assembling the two into that inequality, then the passage to `logPoly` and the Halász estimate.

## 2026-08-10 the combinatorial half is complete

`Sieve/DyadicBandBound.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9014 jobs).

```text
dyadicMeanSquare_le_band :  1 ≤ ℓ →
  dyadicMeanSquare f ℓ A B ≤ ∑_{m, n ∈ (A, B+ℓ]} |f(m)|·|f(n)|·(ℓ − |m − n|)₊

band_kernel_eq_zero :  ℓ ≤ |m − n| →  (ℓ − |m − n|)₊ = 0
```

**Everything from `MRBilinear` down to a near-diagonal bilinear form is now proved here, and none of
it is analytic.**  The chain in full:

```text
MRBilinear μ hh
  ← AveragedShortInterval  ← AveragedMeanSquare  ← MaximalWindowMeanSquare   (corpus)
  ← sum_maxWindowSq_succ_le_dyadic                                            (MaximalWindowReduction)
      built from WindowPartialSum, MaximalDeviation, RademacherMenshov,
                 DyadicMeanSquare, MaximalWindowDyadic, DyadicTranslates
  ← dyadicMeanSquare f ℓ A B                                                  (one named quantity)
  ← dyadicMeanSquare_eq_count                                                 (exact pair expansion)
  ← overlap_card_le                                                           (the discrete kernel)
  ← ∑_{m,n} |f(m)||f(n)|(ℓ − |m − n|)₊                                        (near-diagonal band)
```

The remaining work is analytic and has a single shape: bound that band for `f = μ`.  The corpus's
`gallagher_identity` evaluates exactly this bilinear form — with the multiplicative kernel
`(δ − |log m − log n|)₊` — as `∫ (𝓕 triC δ)·|logPoly|²`, and the Halász machinery of units 1–6
bounds that integral.  The additive-to-multiplicative matching over a dyadic range of `m, n` is the
one remaining structural step before the analysis.

## 2026-08-10 the additive and logarithmic bands are matched

`Sieve/AdditiveLogMatching.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9015 jobs).

```text
log_sub_le_div :  A ≤ n ≤ m  →  log m − log n ≤ (m − n)/A
abs_log_sub_le :  A ≤ m, A ≤ n  →  |log m − log n| ≤ |m − n|/A

band_kernel_le_log_kernel :  A ≤ m, A ≤ n  →
  (ℓ − |m − n|)₊ ≤ A·(ℓ/A − |log m − log n|)₊
```

The pair expansion produces the additive kernel; Gallagher's lemma is stated with the multiplicative
one.  On a range bounded below by `A` the logarithm contracts by exactly `1/A` — `log x ≤ x − 1`
applied to `m/n` — so every additive band of width `ℓ` sits inside a logarithmic band of width
`ℓ/A`, at the cost of the single factor `A`.  That factor is the Jacobian of the change of variable,
and it is what makes the two formulations interchangeable on a dyadic range.

Combined with the previous unit:

```text
dyadicMeanSquare f ℓ A B
  ≤ A·∑_{m, n ∈ (A, B+ℓ]} |f(m)|·|f(n)|·(ℓ/A − |log m − log n|)₊ ,
```

and the right-hand side is, term for term, the bilinear form `gallagher_identity` evaluates as
`∫ (𝓕 triC (ℓ/A))·|logPoly|²`.

### What is left

Substituting `gallagher_identity` — the corpus already proves it — and then bounding
`∫ |logPoly|²` for `f = μ` by the Halász machinery of units 1–6.

## 2026-08-10 correction: the band bound cannot carry the estimate — signs must be kept

`Sieve/OverlapExact.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9016 jobs).

Checking `dyadicMeanSquare_le_band` against the target shows it is true but **useless**:

```text
∑_{m,n} |μ(m)|·|μ(n)|·(ℓ − |m − n|)₊ ≍ (B − A)·ℓ² ,
```

which is exactly the trivial size of `dyadicMeanSquare`, while the target is `o((B − A)·ℓ²)`.
Taking absolute values in the pair expansion destroys the cancellation, and no analytic input can
recover it afterwards.  The same failure mode as the height exponent earlier today: a correct
inequality whose conclusion is vacuous.

The usable object is the *identity* `dyadicMeanSquare_eq_count`, with signed products `f(m)·f(n)`.
Gallagher's identity is likewise signed — `(a n · conj (a m)).re` — so the route must evaluate the
kernel, not bound it.

```text
overlap_filter_eq :  1 ≤ m, 1 ≤ n  →
  { z ∈ [A,B] : m, n ∈ (z, z+ℓ] } = [ max(A, max(m,n) − ℓ), min(B, min(m,n) − 1) ]

overlap_card_eq :  its cardinality, exactly

overlap_card_interior :  ℓ ≤ max(m,n), A ≤ max(m,n) − ℓ, min(m,n) − 1 ≤ B  →
  the kernel is (min(m,n) + ℓ) − max(m,n) = (ℓ − |m − n|)₊
```

Both constraints on `z` are one-sided — `z + 1 ≤ min(m,n)` from the windows' right ends and
`max(m,n) ≤ z + ℓ` from their left ends — so the admissible set is an interval and the kernel has an
exact value.  Away from the two edges of `[A,B]` that value is precisely Gallagher's
`(ℓ − |m − n|)₊`, which is what makes the signed comparison with `gallagher_identity` possible.

`dyadicMeanSquare_le_band` and `band_kernel_le_log_kernel` remain in the corpus as correct
statements; they are simply not on the path to the estimate.

### What is left

The signed comparison: `dyadicMeanSquare_eq_count` with the exact kernel against
`gallagher_identity`'s logarithmic kernel, then the Halász bound for `∫ |logPoly|²`.

## 2026-08-10 the signed quadratic form — the correct Gallagher input

`Sieve/DyadicSignedForm.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9017 jobs).

```text
dyadicMeanSquare_mono :  A' ≤ A, B ≤ B'  →
  dyadicMeanSquare f ℓ A B ≤ dyadicMeanSquare f ℓ A' B'

dyadicMeanSquare_full_eq :  1 ≤ ℓ,  f supported in [ℓ, M]  →
  dyadicMeanSquare f ℓ 0 M
    = ∑_{m, n ∈ [1, M+ℓ]} f(m)·f(n)·((min(m,n) + ℓ) − max(m,n))

dyadicMeanSquare_le_signed_form :  1 ≤ ℓ,  B ≤ M,  f supported in [ℓ, M]  →
  dyadicMeanSquare f ℓ A B ≤ ∑_{m, n ∈ [1, M+ℓ]} f(m)·f(n)·(ℓ − |m − n|)₊
```

The mechanism is that every term of `dyadicMeanSquare` is a square, so **enlarging** the range of
starting points only increases it — and enlarging it to cover every start that sees the support of
`f` turns the exact kernel of `overlap_card_eq` into Gallagher's `(ℓ − |m − n|)₊` at every pair that
contributes.

The signs survive.  That is the whole difference from the previous unit: the same inequality with
`|f(m)|·|f(n)|` is the trivial bound and can prove nothing, whereas this one is exactly the form
`gallagher_identity` evaluates as `∫ ‖logWindowSum‖²`, where the cancellation lives.  The price of
enlarging the range is zero — the discarded starting points contribute squares, which only help.

### What is left

Substituting `gallagher_identity` for the signed form, and the Halász bound for `∫ |logPoly|²`.

## 2026-08-10 the window as a sum of translates — entry to the Fourier side

`Sieve/WindowAsShifts.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9018 jobs).

```text
window_eq_sum_shifts :  ∑_{b ∈ (z, z+ℓ]} f(b) = ∑_{j=1}^{ℓ} f(z + j)
fixedWindowSq_eq_shifts, dyadicMeanSquare_eq_shifts :  the same, squared and summed
```

Read as an operator on sequences, the window is convolution with the indicator of `[1, ℓ]`.  So on
the Fourier side the window sum is `F(θ)` times a Dirichlet kernel, and the signed quadratic form of
`DyadicSignedForm` becomes

```text
∑_{z} (∑_{b ∈ (z, z+ℓ]} f(b))² = ∫₀¹ |F(θ)|²·|D_ℓ(θ)|² dθ ,
```

which is the shape the large-values machinery acts on: `|D_ℓ(θ)| ≤ min(ℓ, 1/2‖θ‖)` localises the
integral near `θ = 0` and near rationals of small denominator, and `|F|` there is what Halász
bounds.

A note on which Gallagher to use.  The corpus's `gallagher_identity` is the *multiplicative* form,
with kernel `(δ − |log m − log n|)₊`, feeding `logPoly` and hence units 1–6 directly.  The additive
form reached here has kernel `(ℓ − |m − n|)₊` and feeds the circle-method machinery
(`TrigParseval`, `FejerBounds`, `LargeSieveGallagher`).  `AdditiveLogMatching` relates the two
kernels pointwise, but pointwise kernel comparison does not transfer between *signed* quadratic
forms — so the choice between the two routes is a real decision, not a formality, and it is the
next thing to settle.

### What is left

The Fourier identity `∑_z S_ℓ(z)² = ∫₀¹ |F|²|D_ℓ|²`, then the large-values/Halász bound.

## 2026-08-10 route settled: the multiplicative Gallagher, and the window's log width

`Sieve/WindowLogWidth.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9019 jobs).

**The route is the multiplicative one.**  `gallagher_identity` is available here in that form, and
its output is `logPoly` — the object the Halász chain of units 1–6 already acts on.  The additive
route would need a separate large-values theory on the circle, none of which is built.  Taking the
multiplicative route requires the additive window to be a window in `log`, which it is, exactly:

```text
logWidth ℓ z := log(z+ℓ) − log z

mem_window_iff_log :  1 ≤ z, 1 ≤ b  →
  b ∈ (z, z+ℓ]  ↔  log z < log b ≤ log z + logWidth ℓ z

logWidth_le :  logWidth ℓ z ≤ ℓ/z
le_logWidth :  ℓ/(z+ℓ) ≤ logWidth ℓ z
```

Both width bounds are `log x ≤ x − 1`, used on `(z+ℓ)/z` and on `z/(z+ℓ)`.  Over a dyadic range of
starting points the width therefore varies by at most a factor two.

That it varies *at all* is exactly why the two Gallagher forms are not interchangeable for free: a
fixed-`δ` logarithmic family is not the additive family, and signed quadratic forms do not compare
under pointwise kernel bounds — the trap that made `dyadicMeanSquare_le_band` true and useless.
Pinning the width between `ℓ/(z+ℓ)` and `ℓ/z` is what turns that from an obstruction into a
factor-two loss.

### What is left

The comparison of the varying-width family with a fixed-`δ` one (Gallagher's Sobolev lemma,
`gallagher_sobolev`, already in the corpus), then `gallagher_identity` and the Halász bound for
`∫ |logPoly|²`.

## 2026-08-10 the bridge onto Gallagher's machinery

`Sieve/WindowToLogWindowSum.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9021 jobs).

```text
mem_logWindow_iff :  u ∈ logWindow δ n  ↔  u < log n ≤ u + δ

window_sum_eq_logWindowSum :  1 ≤ z,  s ⊇ (support of f inside the window),  0 ∉ s  →
  ∑_{b ∈ (z, z+ℓ]} f(b) = logWindowSum f s (logWidth ℓ z) (log z)
```

The corpus's `logWindowSum a s δ u` selects exactly the `n ∈ s` with `u < log n ≤ u + δ`; at
`u = log z` and `δ = logWidth ℓ z` that is the additive window `(z, z+ℓ]`, by `mem_window_iff_log`.
So the additive short sums of the Matomäki–Radziwiłł reduction *are* the corpus's logarithmic ones,
evaluated at the points `log z` with the width `logWidth ℓ z`.

From here `gallagher_identity` applies verbatim:

```text
∫_ℝ ‖logWindowSum a s δ u‖² du = ∫_ℝ (𝓕 (triC δ) w).re · ‖logPoly a s w‖² dw ,
```

and `logPoly` is the object units 1–6 bound.  The one remaining structural step is the passage from
the *discrete* family `{log z : z ∈ [A,B]}` with varying width to the *continuous* integral at fixed
width — Gallagher's Sobolev lemma, already in the corpus as `gallagher_sobolev`, plus the factor-two
control of `logWidth` proved in the previous unit.

### What is left

The discrete-to-continuous passage, then the Halász bound for `∫ |logPoly|²`.

## 2026-08-10 the discrete-to-continuous passage is free — and a design finding

`Sieve/WindowRealStep.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9022 jobs).

```text
windowReal f ℓ v := ∑_{b ∈ (⌊v⌋, ⌊v⌋+ℓ]} f(b)

windowReal_eq :  z ≤ v < z+1  →  windowReal f ℓ v = ∑_{b ∈ (z, z+ℓ]} f(b)
windowReal_sq_eq :  the same, squared, is `fixedWindowSq f ℓ z`
```

The window sum extended to a real start is **constant on each unit cell**, because the integers in
`(v, v+ℓ]` do not move while `v` crosses no integer.  So the discrete sum over integer starts and
the integral over `[A, B+1]` agree exactly: the discrete-to-continuous passage costs nothing in the
additive variable and needs no Sobolev lemma at all.

**The design finding.**  The corresponding statement in the logarithmic variable is *false* at fixed
width, because the right endpoint `e^{u+δ}` sweeps continuously as `u` moves.  That asymmetry is why
`logWidth` had to be pinned rather than fixed — and it points at something about the reduction
itself: the fibres are naturally multiplicative.  `innerFibre` at `a` is
`(x/a, (x/a)(1 + h/√x)]`, whose *relative* length `h/√x` is independent of `a`, while its absolute
length `h√x/a` is not.  The dyadic decomposition of `RademacherMenshov` was carried out in absolute
lengths, which is what introduced the varying `logWidth`; a decomposition dyadic in the
*multiplicative* variable would keep the width fixed and make `gallagher_identity` apply with one
`δ` throughout.

That is a real choice, not a detail, and it is worth settling before the analytic step rather than
after: the present chain is correct but pays a factor-two width variation at every level, whereas
the multiplicative decomposition would pay none.

### What is left

Either (a) carry the factor-two variation through the Gallagher step, or (b) redo the dyadic
decomposition multiplicatively.  Then `gallagher_identity` and the Halász bound for `∫ |logPoly|²`.

## 2026-08-10 the design question, settled: the fibres already have a fixed width

`Sieve/FibreFixedWidth.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9023 jobs).

```text
fibreWidth x h := log(1 + h/√x)

innerFibre_log_bounds :  4 ≤ x, 0 ≤ h, a ∈ outerBlock x h, 1 ≤ b, b ∈ innerFibre x h a  →
  log(x/a) ≤ log b ≤ log(x/a) + fibreWidth x h

fibreWidth_pos :  0 < x, 0 < h  →  0 < fibreWidth x h
```

The fibre above `a` is `[⌈x/a⌉, ⌊(x + h√x)/a⌋]`, whose absolute length `h√x/a` depends on `a` — but
its endpoints are `x/a` and `(x/a)·(1 + h/√x)`, so its **relative** length does not.  Every fibre is
a logarithmic window of one common width `log(1 + h/√x)`, translated to a different start `log(x/a)`.

This settles the question raised by the previous unit.  The varying `logWidth` was an artefact of
decomposing in absolute lengths; the reduction's own objects are already at fixed multiplicative
width, which is exactly the parametrisation `gallagher_identity` is stated in.  The `√x` starting
points `log(x/a)`, `a` ranging over the dyadic block, are what the mean square runs over.

### Consequence for the route

The Rademacher–Menshov chain (`WindowPartialSum` … `MaximalWindowReduction`) removes the supremum
over window *lengths* and is independent of this: it applies to any family of windows, and its
output `dyadicMeanSquare` can be read at the multiplicative scales just as well as the additive
ones.  What changes is that the Gallagher step now sees one `δ` rather than a factor-two range, so
no width-variation loss is incurred at any level.

### What is left

`gallagher_identity` at `δ = fibreWidth x h`, and the Halász bound for `∫ |logPoly|²`.

## 2026-08-10 the fibre, characterised in the logarithmic variable

`Sieve/FibreLogCharacterisation.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`,
wired, builds clean (9024 jobs).

```text
mem_innerFibre_of_log :  the converse inclusion
mem_innerFibre_iff_log :  4 ≤ x, 0 ≤ h, a ∈ outerBlock x h, 1 ≤ b  →
  b ∈ innerFibre x h a  ↔  log(x/a) ≤ log b ≤ log(x/a) + fibreWidth x h
```

An equivalence, not just a containment: the fibres of the Matomäki–Radziwiłł reduction **are** the
logarithmic windows of the single width `log(1 + h/√x)`, at the `√x` starting points `log(x/a)`.

One boundary discrepancy is worth recording rather than discovering later.  The corpus's
`logWindow δ n = [log n − δ, log n)` is half-open, while the fibre is closed at both ends, so the
fibre sum and `logWindowSum` differ by at most the two endpoint terms.  For a unit-bounded weight
that is `O(1)` per fibre and `O(√x)` over the block — negligible against the target `o(h²√x)` once
`h → ∞`, but not zero, so it has to be carried explicitly rather than waved through.

### What is left

The endpoint bookkeeping, `gallagher_identity` at `δ = fibreWidth x h`, and the Halász bound for
`∫ |logPoly|²`.

## 2026-08-10 the endpoint discrepancy, carried explicitly

`Sieve/WindowEndpoint.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9025 jobs).

```text
card_filter_log_eq_le_one :  at most one positive integer has a given logarithm
abs_sum_le_one_of_card_le_one :  a unit-bounded sum over ≤ 1 term is ≤ 1

abs_sum_closed_sub_open_le :  |f| ≤ 1,  T ⊆ [1, ∞)  →
  | ∑_{b ∈ T, c ≤ log b ≤ d} f(b) − ∑_{b ∈ T, c < log b ≤ d} f(b) | ≤ 1
```

The fibre is closed at its left end and the corpus's `logWindow` is half-open, so they differ by the
integers with `log b = c` — of which there is at most one, `log` being injective on the positives.
For a unit-bounded weight that is one term.

Over the `√x` fibres of a block the total discrepancy is `O(√x)`, against a target `o(h²√x)`:
negligible once `h → ∞`, but not zero.  It is now a named lemma rather than an unstated assumption,
which is the difference between a proof and a sketch.

### What is left

`gallagher_identity` at `δ = fibreWidth x h`, and the Halász bound for `∫ |logPoly|²`.

## 2026-08-10 the fibre sum is the corpus's window sum

`Sieve/FibreToLogWindow.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9026 jobs).

```text
abs_fibre_sum_sub_open_le :  |f| ≤ 1,  4 ≤ x,  0 ≤ h,  a ∈ outerBlock x h,
  s ⊇ innerFibre x h a,  s ⊆ [1, ∞)  →
    | ∑_{b ∈ innerFibre x h a} f(b)
        − ∑_{b ∈ s, log(x/a) < log b ≤ log(x/a) + fibreWidth x h} f(b) | ≤ 1
```

The fibre is the closed logarithmic window at `log(x/a)` of width `fibreWidth x h`; the corpus's
`logWindow` is half-open; they differ by at most one integer.  The right-hand sum is `logWindowSum`
in the corpus's sense, so `gallagher_identity` applies to it directly — **at one width for the whole
block**, which is what `FibreFixedWidth` bought.

### The path, end to end

```text
MRBilinear μ hh
  ← AveragedShortInterval ← AveragedMeanSquare ← MaximalWindowMeanSquare        (corpus)
  ← the Rademacher–Menshov chain: WindowPartialSum, MaximalDeviation,
      RademacherMenshov, DyadicMeanSquare, MaximalWindowDyadic, DyadicTranslates,
      MaximalWindowReduction                                                    (this session)
  ← dyadicMeanSquare, expanded exactly:  DyadicPairExpansion, OverlapExact,
      DyadicSignedForm                                                          (this session)
  ← the fibres as fixed-width logarithmic windows:  WindowLogWidth,
      WindowToLogWindowSum, WindowRealStep, FibreFixedWidth,
      FibreLogCharacterisation, WindowEndpoint, FibreToLogWindow                (this session)
  ← gallagher_identity  →  ∫ (𝓕 triC δ)·|logPoly|²                              (corpus)
  ← the Halász bound for that integral                                          [open]
```

Every arrow except the last is proved unconditionally here.

### What is left

The Halász bound for `∫ |logPoly|²` — the analytic core, and the place where units 1–6 enter.

## 2026-08-10 the starting points are separated

`Sieve/FibreStartSeparated.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9027 jobs).

```text
div_le_log_sub :  0 < n ≤ m  →  (m − n)/m ≤ log m − log n

log_start_separated :  4 ≤ x,  a, a' ∈ outerBlock x h,  a ≠ a'  →
  1/(2√x) ≤ |log(x/a) − log(x/a')|
```

Distinct indices differ by at least one and `log` expands by at least the relative gap, so the `√x`
starting points `log(x/a)` are separated by `1/(2√x)`.  Spread over an interval of length `log 2`,
that makes them within a constant factor of equally spaced.

Separation is the input every passage from a discrete family to an integral needs — the large-sieve
step, the spacing step of Gallagher's proof, or a direct cell count — and here it is exact and free.
Note it is the *reverse* inequality to `abs_log_sub_le`: that one says `log` contracts by at most
`1/A`, this one that it expands by at least `1/a`.  Both come from `log t ≤ t − 1`, applied to
reciprocal arguments.

### What is left

The discrete-to-continuous passage using this separation, then `gallagher_identity` and the Halász
bound for `∫ |logPoly|²`.

## 2026-08-10 separated points are few

`Sieve/SeparatedCount.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9028 jobs), lint gate clean.

```text
card_le_of_separated :  0 < g,  0 ≤ L,  points pairwise g-separated,  all in [c, c+L]  →
  card ≤ L/g + 1
```

The counting core of every spacing argument, proved as a cell count rather than by ordering:
`i ↦ ⌊(u i − c)/g⌋` is injective, because two points in a common cell of length `g` are less than
`g` apart, and its image lies in `{0, …, ⌊L/g⌋}`.

**A sharpness check.**  Applied to the starting points `log(x/a)` — separation `1/(2√x)` from
`log_start_separated`, span `log 2` — this gives at most `2√x·log 2 + 1` points, while the block has
`≍ √x` of them.  The two agree up to the constant `2 log 2`, so the separation bound is sharp and
the passage to an integral loses nothing.  Had the count come out with a spare factor of `log x`,
the whole spacing route would have been the wrong one; this is the check that says it is not.

### What is left

The discrete-to-continuous passage itself, then `gallagher_identity` and the Halász bound for
`∫ |logPoly|²`.

## 2026-08-10 a better route: expand in the outer variable, skip the integral entirely

`Sieve/FibreMeanSquarePairs.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9029 jobs).

```text
innerFibre_subset_range :  innerFibre x h a ⊆ [1, ⌊x + h√x⌋]

sum_fibreSq_eq_count :
  ∑_{a ∈ outerBlock} (∑_{b ∈ innerFibre a} f(b))²
    = ∑_{m, n} f(m)·f(n)·#{ a ∈ outerBlock : m, n ∈ innerFibre a }
```

An identity, in the variable the mean square actually runs over.  The kernel counts the outer
indices whose fibre contains both `m` and `n`; since `b ∈ innerFibre x h a ↔ x ≤ ab ≤ x + h√x`,
that is the number of `a` in an intersection of two intervals — explicitly computable, the exact
analogue of `overlap_card_eq`.

**This supersedes the sampling route.**  The previous units were heading for "sample the step
function `u ↦ logWindowSum` at the points `log(x/a)`, then compare with its integral" — the
discrete-to-continuous step, which is the delicate part of Gallagher's proof and needs control of
the step function's cell lengths.  Expanding in `a` instead needs none of it: the identity is exact,
the signs are kept, and no integral appears.

The work on the sampling route is not wasted — `FibreFixedWidth`, `FibreLogCharacterisation`,
`WindowEndpoint`, `FibreStartSeparated` and `SeparatedCount` are the facts one needs to *choose*
between the routes, and `SeparatedCount`'s sharpness check is what showed the sampling route would
have been viable but not simpler.

### What is left

The kernel `#{a ∈ outerBlock : m, n ∈ innerFibre a}` — an interval count in `a` — and then the
bilinear estimate for `μ`.

## 2026-08-10 the fibre kernel: an interval, vanishing off a band

`Sieve/FibreKernelBand.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9030 jobs).

```text
fibre_kernel_subset_Icc :  1 ≤ m, 1 ≤ n  →
  { a ∈ outerBlock : m, n ∈ innerFibre a } ⊆ [ ⌈x/min(m,n)⌉, ⌊(x + h√x)/max(m,n)⌋ ]

fibre_kernel_eq_empty :  (x + h√x)·min(m,n) < x·max(m,n)  →
  { a ∈ outerBlock : m, n ∈ innerFibre a } = ∅
```

An `a` serving both `m` and `n` satisfies `x ≤ a·min(m,n)` and `a·max(m,n) ≤ x + h√x` — two
one-sided constraints, so the admissible `a` form an interval; and there are none unless
`max/min ≤ 1 + h/√x`.

That last condition is `|log m − log n| ≤ fibreWidth x h`: the same near-diagonal band as
`overlap_card_le`'s `|m − n| < ℓ`, now derived directly in the outer variable with no window
machinery.  The bilinear form of `sum_fibreSq_eq_count` is therefore supported on a multiplicative
band of width `1 + h/√x` around the diagonal, which is the structural fact the estimate needs.

### What is left

The kernel's size on the band — `card ≤ (x + h√x)/max(m,n) − x/min(m,n) + 1` from the containment —
and then the bilinear estimate for `μ`.

## 2026-08-10 the fibre kernel's size

`Sieve/FibreKernelSize.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9031 jobs).

```text
fibre_kernel_card_le :  0 ≤ x,  0 ≤ h,  1 ≤ m,  1 ≤ n  →
  #{ a ∈ outerBlock : m, n ∈ innerFibre a }
    ≤ ( (x + h√x)/max(m,n) − x/min(m,n) + 1 )₊
```

The admissible `a` form an interval, so their number is its length plus one.  On the diagonal
`m = n` this is `h√x/m + 1`, the expected count; off the diagonal it decreases, reaching zero exactly
at the band edge `max/min = 1 + h/√x`, in agreement with `fibre_kernel_eq_empty`.

So `sum_fibreSq_eq_count` now reads as a bilinear form with an explicit near-diagonal kernel:

```text
∑_{a ∈ outerBlock} (∑_{b ∈ innerFibre a} μ(b))²
  = ∑_{m,n} μ(m)·μ(n)·K(m,n) ,     0 ≤ K(m,n) ≤ ( (x+h√x)/max − x/min + 1 )₊ ,
```

obtained with no window machinery, no integral, and no discrete-to-continuous passage.  The
diagonal contributes `≍ h√x·∑_m μ(m)²/m ≍ h√x·log x`, which is the trivial size; the whole content
of Matomäki–Radziwiłł is that the off-diagonal cancels it down to `o(h²√x)`.

### What is left

The off-diagonal estimate for `μ` — the analytic core.

## 2026-08-10 the diagonal, and where the kernel lives

`Sieve/FibreDiagonal.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9032 jobs).

```text
fibre_kernel_diag_le :  0 ≤ x, 0 ≤ h, 1 ≤ m  →  K(m,m) ≤ h√x/m + 1

fibre_kernel_support :  0 < x, a ∈ outerBlock x h, m ∈ innerFibre x h a  →
  √x/2 ≤ m ≤ √x + h
```

On the diagonal the interval bound collapses to `h√x/m + 1`; and since `a ∈ outerBlock` means
`√x ≤ a ≤ 2√x`, the constraint `x ≤ am ≤ x + h√x` confines `m` to `[√x/2, √x + h]`.

Together these fix the diagonal contribution at

```text
∑_{m ≍ √x} (h√x/m + 1) ≍ h√x + √x ,
```

which is the **trivial size of the whole mean square** — the target being `o(h²√x)`, and `h → ∞`.
So the diagonal alone already exceeds nothing, but it is of the same order as the trivial bound
divided by `h`: the entire content of Matomäki–Radziwiłł is the off-diagonal cancellation, and no
bound on individual terms can produce it.  That is worth having as a proved statement rather than an
expectation, because it rules out every route that estimates the kernel termwise — including the
one that made `dyadicMeanSquare_le_band` vacuous.

### What is left

The off-diagonal estimate for `μ` — the analytic core.

## 2026-08-10 the bilinear form, split

`Sieve/FibreDiagonalSplit.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9033 jobs).

```text
fibre_diag_kernel_eq_zero :  m outside [√x/2, √x + h]  →  K(m,m) = 0

sum_fibreSq_diag_split :
  ∑_{a ∈ outerBlock} (∑_{b ∈ innerFibre a} f(b))²
    = ∑_m f(m)²·K(m,m) + ∑_m ∑_{n ≠ m} f(m)·f(n)·K(m,n)
```

The first sum is bounded by `FibreDiagonal` and carried by the `≍ √x` integers in `[√x/2, √x + h]`,
giving `≍ h√x + √x`.  Everything the Matomäki–Radziwiłł theorem asserts beyond that lives in the
second.

### State of the card

Unit 5 and unit 6 are closed: the Halász mean value is
`GhsMeanValueDiv.eventually_norm_sum_Icc_div_le`, with every unconditional term proved `o(N)` and
one Halász term carrying the distance.  The `MRBilinear` path is reduced, unconditionally and
entirely within this corpus, to the off-diagonal estimate

```text
∑_m ∑_{n ≠ m} μ(m)·μ(n)·#{ a ∈ outerBlock : m, n ∈ innerFibre a } = o(h²√x) ,
```

with the kernel explicitly an interval count, supported on the multiplicative band
`max/min ≤ 1 + h/√x`, and with the diagonal separately bounded.  That single statement is the whole
remaining content.

## 2026-08-10 the diagonal sum, assembled

`Sieve/FibreDiagonalSum.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9034 jobs).

```text
fibre_diag_sum_le :  |f| ≤ 1,  0 < x,  0 ≤ h  →
  ∑_m f(m)²·K(m,m) ≤ ∑_{⌈√x/2⌉ ≤ m ≤ ⌊√x + h⌋} ( h√x/m + 1 )
```

The terms outside `[√x/2, √x + h]` vanish by `fibre_diag_kernel_eq_zero`; inside, `f(m)² ≤ 1` and
`K(m,m) ≤ h√x/m + 1`.  The right-hand side is `≍ h√x·log 2 + √x ≍ h√x + √x`.

So the diagonal side of the bilinear form is completely settled, unconditionally, with explicit
constants.  Against the target `o(h²√x)` it is smaller by a factor `h`.

### The remaining statement

```text
∑_m ∑_{n ≠ m} μ(m)·μ(n)·#{ a ∈ outerBlock : m, n ∈ innerFibre a } = o(h²√x)
```

with `K(m,n)` an explicit interval count (`fibre_kernel_card_le`), supported on the multiplicative
band `max/min ≤ 1 + h/√x` (`fibre_kernel_eq_empty`) and on `m, n ∈ [√x/2, √x + h]`
(`fibre_kernel_support`).  That is the whole of Matomäki–Radziwiłł that is not proved here.

## 2026-08-10 the off-diagonal lives at shifts of size `h` — and the reduction is faithful

`Sieve/FibreShiftBand.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9035 jobs).

```text
fibre_kernel_symm :  K(m,n) = K(n,m)

fibre_shift_band :  0 < x, 0 ≤ h, m and n in a common fibre  →
  |m − n| ≤ h + h²/√x
```

The multiplicative band `max/min ≤ 1 + h/√x` becomes an additive one once the localisation
`m, n ∈ [√x/2, √x + h]` is used: `x·n ≤ (x + h√x)·m` and `m ≤ √x + h` give
`n − m ≤ h·m/√x ≤ h + h²/√x`.

So the off-diagonal part of the bilinear form is a weighted sum of **binary correlations of `μ` at
shifts `|k| ≲ h`**:

```text
∑_{k ≠ 0, |k| ≲ h} K(n+k, n)·∑_n μ(n)·μ(n+k) ,
```

and the kernel's value near the diagonal is `≍ h − |k|` — Gallagher's triangular weight, recovered
in the outer variable.

**Why this matters for the reduction's honesty.**  The individual correlations `∑_n μ(n)μ(n+k)` are
Chowla's conjecture and open.  What is required here is only their *average* over `|k| ≤ h` with the
triangular weight, as `h → ∞` — which is precisely Matomäki–Radziwiłł's theorem, no more and no
less.  A reduction landing on individual correlations would have been a reduction to an open
problem strictly harder than the target; this one lands on a statement of exactly the right
strength.

### What is left

That averaged-correlation statement, and nothing else.

## 2026-08-10 the off-diagonal is twice its lower half

`Sieve/SymmetricOffDiagonal.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9036 jobs).

```text
sum_offdiag_eq_two_mul :  g symmetric  →
  ∑_m ∑_{n ≠ m} g(m,n) = 2·∑_m ∑_{n < m} g(m,n)
```

The summand `f(m)·f(n)·K(m,n)` is symmetric — coefficients commute, and `fibre_kernel_symm` gives
the kernel — so the punctured double sum halves.  The proof splits the punctured row by trichotomy
and exchanges the two summations by `Finset.sum_comm'`.

Written this way the off-diagonal is literally a sum over **positive** shifts `k = m − n`, with
`1 ≤ k ≲ h` by `fibre_shift_band` and weight `K(n+k, n) ≍ h − k`:

```text
∑_{a ∈ outerBlock} (∑_{b ∈ innerFibre a} μ(b))²
  = [diagonal, ≍ h√x + √x]  +  2·∑_{k ≥ 1} ∑_n μ(n)·μ(n+k)·K(n+k, n) .
```

The whole remaining content is that the second term is `o(h²√x)` — the triangular-weighted average
of binary correlations of `μ` over shifts up to `h`.

### What is left

That statement.  Every other step from `MRBilinear` is proved unconditionally in this corpus.

## 2026-08-10 the diagonal, with explicit constants — the reduction closes on the off-diagonal

`Sieve/FibreDiagonalExplicit.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9037 jobs).

```text
fibre_diag_sum_explicit_le :  |f| ≤ 1,  4 ≤ x,  0 ≤ h  →
  ∑_m f(m)²·K(m,m) ≤ (√x/2 + h + 1)·(2h + 1)
```

On `[⌈√x/2⌉, ⌊√x + h⌋]` every term is at most `h√x·(2/√x) + 1 = 2h + 1`, and the range holds at most
`√x/2 + h + 1` integers.  Expanded, the bound is `h√x + √x/2 + 2h² + 3h + 1`.

Divided by the normalisation `h²√x` of `AveragedMeanSquare`:

```text
1/h + 1/(2h²) + 2/√x + 3/(h√x) + 1/(h²√x)  →  0   whenever h → ∞ .
```

**The diagonal is unconditionally harmless**, with explicit constants and no asymptotic input beyond
`h → ∞`.  So `AveragedMeanSquare μ hh` — and with it `MRBilinear`, and with it the two Route E
sign-density theorems — follows from the single statement

```text
∑_{k ≥ 1} ∑_n μ(n)·μ(n+k)·K(n+k, n) = o(h²√x) ,
```

the triangular-weighted average of binary correlations of `μ` over shifts `1 ≤ k ≲ h`.

### Session summary for this card

Units 5 and 6 (the Halász mean value) are closed.  The `MRBilinear` path is reduced, unconditionally
and entirely within this corpus, from `MRBilinear μ hh` to that one averaged-correlation statement,
through: the Rademacher–Menshov chain (7 modules), the exact pair expansion (3 modules), the
fixed-width fibre identification (7 modules), and the outer-variable expansion with its kernel
analysis (8 modules).  Every intermediate step is a named unconditional theorem with explicit
constants.

## 2026-08-10 CAPSTONE: the reduction closes on the off-diagonal

`Sieve/AveragedFromOffDiagonal.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`,
wired, builds clean (9038 jobs).

```text
OffDiagonalVanishes f hh :=
  2·∑_m ∑_{n < m} f(m)·f(n)·#{a ∈ outerBlock : m, n ∈ innerFibre a} / (h²√x) → 0

averagedMeanSquare_of_offDiagonal :  |f| ≤ 1,  hh → ∞,  OffDiagonalVanishes f hh  →
  AveragedMeanSquare f hh
```

The diagonal contributes at most `(3/2)/h + 6/√x` to the normalised quantity, which vanishes
unconditionally; the split and the symmetry do the rest.

### The chain, complete

```text
MRBilinear μ hh
  ← MRBilinear_moebius_of_averaged                              (corpus)
  ← AveragedShortInterval μ hh
  ← averagedShortInterval_of_meanSquare                         (corpus)
  ← AveragedMeanSquare μ hh
  ← averagedMeanSquare_of_offDiagonal                           (this unit)
  ← OffDiagonalVanishes μ hh                                    [the sole open input]
```

`OffDiagonalVanishes μ hh` is the triangular-weighted average of binary correlations of `μ` over
shifts `1 ≤ k ≲ h`, with the weight `K(n+k,n)` an explicit interval count.  Everything else on the
path — and everything in units 1–6 — is a named unconditional theorem of this corpus.

Both Route E sign-density theorems (`route_e_sign_density`, `route_e_signClass_nonempty`) become
unconditional the moment `OffDiagonalVanishes μ hh` is proved, subject to the scope boundary already
recorded: `MRBilinear` yields local sign-class density, not Route E's coherent Hall/seam-flux
theorem.

## 2026-08-10 the trivial size, written down

`Sieve/FibreTrivialBound.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9039 jobs).

```text
card_innerFibre_le_block :  a ∈ outerBlock  →  #(innerFibre x h a) ≤ h + 1
abs_fibre_sum_le :  |f| ≤ 1  →  |∑_{b ∈ innerFibre a} f(b)| ≤ h + 1
sum_fibreSq_trivial_le :  ∑_a (∑_b f(b))² ≤ #(outerBlock)·(h + 1)²
```

The corpus already had `card_innerFibre_le : #(innerFibre x h a) ≤ h√x/a + 1`; on the block `a ≥ √x`
this is `h + 1`.  (I wrote a duplicate of the corpus lemma before finding it — deleted; the module
now derives the block form from the existing one.)

Normalised by `h²√x`, the trivial size is `≍ 2`, so `AveragedMeanSquare` asks for *any* saving over
it.  This is the benchmark against which two routes were discarded today: `DyadicBandBound`'s
absolute-value form and the height exponent `4` in `ghsHeight` both produced, on measurement,
exactly the trivial size.  Both were correct theorems whose conclusions said nothing.  Writing the
benchmark down as a proved statement makes that test mechanical rather than a matter of noticing.

### State

`MRBilinear μ hh` is reduced to `OffDiagonalVanishes μ hh` and nothing else, with the trivial size,
the diagonal, the kernel, its band and its support all proved unconditionally with explicit
constants.

## 2026-08-10 the kernel is uniformly `O(h)` — the endpoint is averaged Chowla

`Sieve/FibreKernelUniform.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9040 jobs).

```text
fibre_kernel_le_two_h :  0 ≤ x, 0 ≤ h, 1 ≤ m, 1 ≤ n, √x/2 ≤ min(m,n)  →
  K(m,n) ≤ 2h + 1
```

The interval length is `(x + h√x)/max − x/min ≤ h√x/min ≤ 2h` on the support, so the kernel carries
no dependence on `m` or `n`.

**This identifies the endpoint with a named theorem.**  Pulling the uniform factor out of the
off-diagonal,

```text
|off-diagonal| ≤ 2(2h + 1)·∑_{1 ≤ k ≲ h} | ∑_n μ(n)·μ(n+k) | ,
```

so `OffDiagonalVanishes μ hh` follows from

```text
∑_{k ≤ 2h} | ∑_{n ≤ √x} μ(n)·μ(n+k) | = o(h√x) ,
```

the **averaged form of Chowla's conjecture** — proved by Matomäki, Radziwiłł and Tao for `h → ∞`.

The strength is exactly right, and now checkable against the literature rather than against
intuition: the individual correlations `∑_n μ(n)μ(n+k)` are Chowla and open; their average over
`k ≤ h` is a theorem.  Note this also shows the absolute values may be taken in `k` at no cost —
there are only `≍ h` terms and the target has a factor `h²` — but *not* inside each correlation,
where the cancellation is essential.

### State

`MRBilinear μ hh` ⟸ `OffDiagonalVanishes μ hh` ⟸ averaged Chowla over shifts `k ≤ 2h`.
Every step is unconditional here except the last, which is a published theorem not yet formalised in
this corpus.

## 2026-08-10 the lower triangle, reindexed by shift

`Sieve/LowerSumAsShifts.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9041 jobs).

```text
sum_lower_eq_shifts :
  ∑_m ∑_{n < m} g(m,n) = ∑_{k ≥ 1} ∑_{n : n + k ≤ M} g(n + k, n)
```

A bijection on the sigma type, `(m,n) ↦ (m − n, n)`.  With `g(m,n) = μ(m)·μ(n)·K(m,n)` the inner sum
is a correlation of `μ` at shift `k`, weighted by the kernel:

```text
off-diagonal = 2·∑_{k ≥ 1} ∑_n μ(n+k)·μ(n)·K(n+k, n) .
```

The correlation shape is now literal rather than descriptive.  What stands between this and the
averaged Chowla theorem is the kernel's dependence on `n` inside the inner sum: `K(n+k,n)` must be
removed by partial summation before `∑_n μ(n)μ(n+k)` can be quoted.  `fibre_kernel_le_two_h` gives
the uniform size `2h + 1`, and `fibre_kernel_subset_Icc` gives the exact value as an interval count,
which is what a partial summation would act on.

### What is left

Partial summation in `n` to strip the kernel, then the averaged Chowla theorem.

## 2026-08-10 Abel's inequality without monotonicity

`Sieve/AbelVariation.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9042 jobs).

```text
abs_sum_mul_le_of_bounded_partial_bv :  (∀ k, |∑_{j<k} g(j)| ≤ B)  →
  |∑_{i<n} w(i)·g(i)| ≤ B·( |w(n−1)| + ∑_{i<n−1} |w(i+1) − w(i)| )
```

The corpus's `abs_sum_mul_le_of_bounded_partial` requires the weight nonincreasing, which the kernel
is not: `K(n+k, n)` is a *difference* of two decreasing functions, `(x + h√x)/(n+k)` and `x/n`, so it
has bounded variation but no monotonicity.  Summation by parts never used the monotonicity — only
the total variation, which in the monotone case telescopes to `w(0) − w(n−1)`.

With this the kernel can be stripped from the correlation sums of `LowerSumAsShifts`, leaving
`∑_n μ(n)·μ(n+k)` to be quoted from the averaged Chowla theorem.  The variation of `K(·+k, ·)` over
the range is `O(h)` — each of the two decreasing pieces varies by `O(h)` across `[√x/2, √x + h]` —
so the stripping costs the same factor `h` the uniform bound would, and no more.

### What is left

The variation estimate for the kernel, and the averaged Chowla theorem.

## 2026-08-10 the variation of a difference of monotones

`Sieve/VariationOfDifference.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9043 jobs).

```text
variation_le_of_sub_antitone :  u, v nonincreasing  →
  ∑_{i < n} |(u − v)(i+1) − (u − v)(i)| ≤ (u(0) − u(n)) + (v(0) − v(n))
```

Each increment splits as `|Δu − Δv| ≤ |Δu| + |Δv| = (−Δu) + (−Δv)`, and both pieces telescope.

For the kernel `K(n+k, n)`, the two pieces are `(x + h√x)/(n+k)` and `x/n`, each varying by `O(h)`
across `[√x/2, √x + h]`.  So its variation is `O(h)` — the same order as the uniform bound of
`fibre_kernel_le_two_h`, which means the bounded-variation Abel inequality costs nothing beyond what
the uniform bound would have cost, while applying to a kernel that is not monotone.

The three ingredients for stripping the kernel are now in place: the reindexing
(`sum_lower_eq_shifts`), the inequality (`abs_sum_mul_le_of_bounded_partial_bv`), and the variation
bound (this unit, plus the monotonicity of the two pieces).

### What is left

Assembling them — which reduces `OffDiagonalVanishes μ hh` to the averaged Chowla theorem — and
that theorem itself.

## 2026-08-10 stripping the kernel from a correlation

`Sieve/WeightedCorrelation.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9044 jobs).

```text
abs_weighted_correlation_le :  0 ≤ B,  partial sums of g ≤ B,  |w(n−1)| ≤ W,  variation ≤ V  →
  |∑_{i<n} w(i)·g(i)| ≤ B·(W + V)

abs_weighted_correlation_le_of_sub_antitone :  u, v nonincreasing  →
  |∑_{i<n} (u(i) − v(i))·g(i)|
    ≤ B·( |u(n−1) − v(n−1)| + (u(0) − u(n−1)) + (v(0) − v(n−1)) )
```

With `g(i) = μ(i)·μ(i+k)` and `u − v` the kernel `K(i+k, i)`, both the last value and the total
swing are `O(h)`, so the weighted correlation is `O(h)` times the largest partial correlation sum.
Hence

```text
OffDiagonalVanishes μ hh  ⟸  ∑_{k ≤ 2h} max_j | ∑_{i<j} μ(i)·μ(i+k) | = o(h√x) ,
```

the averaged Chowla theorem in maximal-partial-sum form.

### The reduction, stated once more in full

```text
MRBilinear μ hh
  ⟸ AveragedShortInterval ⟸ AveragedMeanSquare                         (corpus)
  ⟸ averagedMeanSquare_of_offDiagonal                                   (this session)
  ⟸ OffDiagonalVanishes μ hh
  ⟸ sum_offdiag_eq_two_mul, sum_lower_eq_shifts                         (this session)
  ⟸ abs_weighted_correlation_le_of_sub_antitone + fibre_kernel_le_two_h (this session)
  ⟸ ∑_{k ≤ 2h} max_j | ∑_{i<j} μ(i)·μ(i+k) | = o(h√x)                   [averaged Chowla]
```

Every arrow is an unconditional theorem of this corpus except the last, which is a published
theorem (Matomäki–Radziwiłł–Tao) not yet formalised here.

## 2026-08-10 the shift-sum interface

`Sieve/ShiftSumBound.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9045 jobs).

```text
CorrelationPartialBound f K B :=
  ∀ k ∈ [1, K], ∀ j,  | ∑_{i<j} f(i)·f(i+k) | ≤ B k

abs_shift_sum_le :  CorrelationPartialBound f K B,  B ≥ 0,
  every weight's last value plus variation ≤ W  →
    | ∑_{k=1}^{K} ∑_{i<n} w(k,i)·f(i)·f(i+k) | ≤ W·∑_{k=1}^{K} B k
```

This is the interface the off-diagonal consumes.  For the fibre kernel `W = O(h)`, so

```text
OffDiagonalVanishes μ hh  ⟸  ∑_{k ≤ 2h} B k = o(h√x) ,
```

with `B k` the largest partial correlation sum at shift `k` — the averaged Chowla theorem in the
maximal-partial-sum form that partial summation requires.  (The maximal form follows from the plain
one by applying it at each truncation point; that step is not yet formalised here.)

The last link is now a named `Prop` with an explicit interface, not prose.

### Lint note

`scripts/formal_tools.py lint` reports four unreachable modules — `DeningerSuspendedAlternating`,
`HedenmalmThetaAllShiftedTails`, `HedenmalmThetaSourceDeterminantMultiplicity` and one more — all
untracked files of a concurrent agent.  None of the ~40 modules added for this card is among them;
every one is wired into `GaloisForLFunctions.RHTower`.

## 2026-08-10 truncation does not increase variation

`Sieve/VariationTruncation.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9046 jobs).

```text
abs_max_zero_sub_le :  |max a 0 − max b 0| ≤ |a − b|
variation_max_zero_le :  the same, summed
variation_max_zero_of_sub_antitone :  u, v nonincreasing  →
  ∑_{i<n} |max((u−v)(i+1),0) − max((u−v)(i),0)| ≤ (u(0) − u(n)) + (v(0) − v(n))
```

The fibre kernel is a *count*, so it is the positive part of a difference of two monotone functions,
not the difference itself: `⌊(x + h√x)/(n+k)⌋ + 1 − ⌈x/n⌉` where that is nonnegative, `0` where it is
not.  Positive part is `1`-Lipschitz (`max a 0 = (a + |a|)/2`, and both pieces are), so the
truncation cannot increase the variation.

That closes the last gap between the abstract Abel machinery and the kernel as it actually is:
`abs_weighted_correlation_le` now applies to the real kernel, not to an idealised version of it.
This is the kind of detail that is invisible in a sketch — a count is not a difference of monotone
functions, and pretending otherwise would have left a hole.

### What is left

The numerical assembly (monotonicity of the two pieces, the `O(h)` swing, the sum over `k`), and the
averaged Chowla theorem.

## 2026-08-10 the kernel's two pieces are monotone

`Sieve/KernelPieceMonotone.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9047 jobs).

```text
antitone_div_natAdd :  c ≥ 0, k ≥ 1  →  c/((n+1)+k) ≤ c/(n+k)
antitone_div_succ :  c ≥ 0  →  c/(n+2) ≤ c/(n+1)
antitone_floor_of_antitone :  u nonincreasing  →  ⌊u(i+1)⌋ ≤ ⌊u(i)⌋
antitone_ceil_of_antitone :  u nonincreasing  →  ⌈u(i+1)⌉ ≤ ⌈u(i)⌉
```

Both pieces of the exact kernel are therefore nonincreasing in `n`, and their swings across
`[√x/2, √x + h]` are `O(h)` each.  Chained with `variation_max_zero_of_sub_antitone` this gives the
kernel total variation `O(h)`, and `abs_weighted_correlation_le` strips it at that cost.

The partial-summation apparatus is now complete and applies to the kernel exactly as defined:

```text
sum_lower_eq_shifts          reindex the off-diagonal by shift
abs_sum_mul_le_of_bounded_partial_bv   Abel without monotonicity
variation_le_of_sub_antitone           variation of a difference of monotones
variation_max_zero_of_sub_antitone     … surviving truncation to a count
antitone_*                             both pieces are monotone
abs_shift_sum_le                       the sum over shifts
```

### What is left

The numerical assembly, and the averaged Chowla theorem.

## 2026-08-10 correction: the two-piece variation bound is a factor `√x/h` too lossy

`Sieve/VariationBimonotone.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9048 jobs).

Yesterday's claim that the kernel's variation is `O(h)` "same order as the uniform bound" was wrong
*for the route as built*.  `variation_le_of_sub_antitone` bounds the variation by the sum of the two
pieces' swings, and each of `(x + h√x)/(n+k)` and `x/n` swings by `≍ √x` across `[√x/2, √x + h]`.
So that route gives variation `O(√x)`, and `abs_shift_sum_le` would then demand

```text
∑_{k ≤ 2h} B k = o(h²) ,
```

with `B k` a partial correlation sum of trivial size `√x` — a demand stronger than the truth by a
factor `√x/h`, and not provable.

The kernel's *difference* is `O(h)` throughout and has at most one turning point in `n` — its
increments change sign once, near `n ≍ k√x/h`.  For such a function the variation telescopes on each
side of the turn:

```text
variation_le_two_range_of_bimonotone :  w increasing up to c, decreasing after,  L ≤ w ≤ U  →
  ∑_{i<n} |w(i+1) − w(i)| ≤ 2·(U − L)
```

giving variation `O(h)` as required.  The failed accounting is worth recording alongside the fix:
"variation ≤ sum of the pieces' swings" is true and useless here, and the gap between the two routes
is exactly the factor the theorem is about.

### What is left

Locating the turning point for the kernel (an explicit `c ≍ k√x/h`), the numerical assembly, and the
averaged Chowla theorem.

## 2026-08-10 the integer kernel cannot be Abel-summed — split it instead

`Sieve/KernelSmoothSplit.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9049 jobs).

A second look at the previous correction shows the bimonotone bound does not rescue the *integer*
kernel either.  `K(n) = ⌊B(n)⌋ + 1 − ⌈A(n)⌉` with `A`, `B` each dropping by `≍ √x` across the range;
their unit drops occur at different `n`, so the increments do not cancel step by step and the true
variation is `≍ √x`.  No refinement of the variation estimate avoids that — the integer kernel is
simply not of bounded variation at scale `h`.

The resolution is to split rather than to estimate:

```text
kernelSmooth A B := max(B − A + 1, 0)

abs_count_sub_length_le :  |⌊B⌋ + 1 − ⌈A⌉ − (B − A + 1)| ≤ 2
abs_count_sub_smooth_le :  |⌊B⌋ + 1 − ⌈A⌉ − kernelSmooth A B| ≤ 2
```

* the **smooth part** `kernelSmooth` has variation `O(h)`: its untruncated form has one turning
  point and range `O(h)` (`variation_le_two_range_of_bimonotone`), and truncation does not increase
  variation (`variation_max_zero_le`).  Abel summation applies at cost `O(h)`;
* the **error** is bounded by the absolute constant `2`, so its contribution is bounded *trivially*
  by `2√x` per shift, hence `4h√x` over all `k ≤ 2h`, which is `o(h²√x)`.

The error is affordable precisely because its bound is a constant rather than `O(h)`: the trivial
estimate for it already sits a factor `h` below the target.  That asymmetry — smooth part needs
cancellation, bounded error does not — is the reason the split works at all.

### What is left

The turning point of `B − A`, the numerical assembly, and the averaged Chowla theorem.

## 2026-08-10 the bounded error costs nothing

`Sieve/ErrorShiftSum.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9050 jobs).

```text
abs_error_shift_sum_le :  |e| ≤ E,  |g| ≤ 1  →
  | ∑_{k=1}^{K} ∑_{i<N} e(k,i)·g(k,i) | ≤ E·K·N
```

The counterpart to `abs_shift_sum_le`.  For the fibre kernel `E = 2`, `K ≍ 2h`, `N ≍ √x`, so the
error contributes `O(h√x)` — a factor `h` below the target `o(h²√x)`.

Both halves of the smooth/error split now have their bound:

| part | size | needs |
|---|---|---|
| smooth, `kernelSmooth` | variation `O(h)` | correlation cancellation (`abs_shift_sum_le`) |
| error, `|e| ≤ 2` | `O(h√x)` trivially | nothing (`abs_error_shift_sum_le`) |

The asymmetry is the point: a weight of size `O(h)` must be paid for with cancellation, a weight of
size `O(1)` need not.  Splitting the kernel converts an object with variation `≍ √x` — hopeless for
Abel summation — into one that is `O(h)` in variation plus one that is `O(1)` in size.

### What is left

The turning point of `B − A`, the numerical assembly of the two halves, and the averaged Chowla
theorem.

## 2026-08-10 the turning point exists — concavity is all it takes

`Sieve/ConcaveSignSegment.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9051 jobs).

```text
increment_antitone :  concave  →  the increments are nonincreasing
neg_of_concave_of_neg :  concave,  P(0) ≥ 0,  P(n) < 0  →  ∀ m ≥ n, P(m) < 0
```

The sign of the smooth kernel's increment is governed by

```text
P(n) = x(n+k)(n+1+k) − (x + h√x)·n(n+1) = −h√x·n² + (2kx − h√x)·n + xk(k+1) ,
```

a downward parabola with `P(0) = xk(k+1) > 0`.  So `{n : P(n) ≥ 0}` is an initial segment, which is
exactly the bimonotonicity `variation_le_two_range_of_bimonotone` asks for: the smooth kernel
increases while `P ≥ 0` and decreases after.

The lemma needs nothing about parabolas — only concavity.  The increments of a concave sequence are
nonincreasing, so once the sequence has dropped below its starting value it keeps dropping; the
quadratic enters only to supply `P(n+2) − 2P(n+1) + P(n) = −2h√x < 0`.

### What remains for `MRBilinear`

The numerical assembly — instantiating `P` at the fibre kernel, checking `P(0) > 0` and the
concavity constant, and combining the smooth and error halves — and the averaged Chowla theorem.
Every structural ingredient is now a named unconditional theorem of this corpus.

## 2026-08-10 the turning point, instantiated

`Sieve/KernelTurningPoint.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9052 jobs).

```text
kernelP x h k n := x(n+k)(n+1+k) − (x + h√x)·n(n+1)

kernelP_second_diff :  P(n+2) − 2P(n+1) + P(n) = −2h√x
kernelP_concave :  0 ≤ h  →  P concave
kernelP_zero_nonneg :  0 ≤ x  →  0 ≤ P(0)
kernel_increment_eq :  1 ≤ n, 1 ≤ k  →
  the smooth kernel's increment equals P(n) / (n(n+1)(n+k)(n+1+k))
```

The increment is a single quotient with a positive denominator, so its sign is the sign of `P`; `P`
is concave with `P(0) = xk(k+1) ≥ 0`, so by `neg_of_concave_of_neg` the set where it is nonnegative
is an initial segment.  The smooth kernel therefore increases and then decreases, which is exactly
what `variation_le_two_range_of_bimonotone` consumes, giving variation `O(h)`.

Every structural ingredient of the off-diagonal estimate is now proved:

| ingredient | module |
|---|---|
| off-diagonal = shift sum | `SymmetricOffDiagonal`, `LowerSumAsShifts` |
| kernel = smooth + bounded error | `KernelSmoothSplit` |
| smooth part has one turning point | `KernelTurningPoint`, `ConcaveSignSegment` |
| hence variation `O(h)` | `VariationBimonotone`, `VariationTruncation` |
| Abel without monotonicity | `AbelVariation`, `WeightedCorrelation` |
| shift sum, smooth half | `ShiftSumBound` |
| shift sum, error half | `ErrorShiftSum` |

### What remains

The numerical assembly of these, and the averaged Chowla theorem.

## 2026-08-10 the smooth kernel rises then falls

`Sieve/KernelDiffMonotone.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`, wired,
builds clean (9053 jobs).

```text
kernelDiff x h k n := (x + h√x)/(n+k) − x/n

kernelDiff_increment_eq :  the increment is kernelP over a positive denominator
kernel_increment_den_pos :  that denominator is positive
kernelDiff_mono_of_nonneg :  0 ≤ kernelP  →  kernelDiff rises
kernelDiff_anti_of_nonpos :  kernelP ≤ 0  →  kernelDiff falls
```

With `neg_of_concave_of_neg` making `{n : kernelP ≥ 0}` an initial segment, these two say exactly
that `kernelDiff` rises and then falls — the hypothesis pair of
`variation_le_two_range_of_bimonotone`, whose conclusion gives the smooth kernel variation `O(h)`.

The off-diagonal apparatus is complete: every step from the bilinear form to a weighted sum of
correlations, and every property of the weight that the weighting requires, is a named unconditional
theorem of this corpus.

### What remains

The numerical assembly, and the averaged Chowla theorem.

## Unit 8 — the off-diagonal reduced to averaged correlations (Lean, unconditional)

The numerical assembly is closed.  `MRBilinear μ hh` now follows, unconditionally in Lean, from a
single averaged-correlation input, for any window law with `hh → ∞` and `hh x ≤ √x` eventually.

**New machinery (10 modules, all `[propext, Classical.choice, Quot.sound]`).**

| Module | Statement |
|---|---|
| `Sieve/QuasiConcaveSeq.lean` | `QuasiConcaveOn w n := ∀ i ≤ j ≤ k ≤ n, min (w i) (w k) ≤ w j`; closed under `min`, `+c`, `max (·) c`; monotone/antitone/bimonotone ⟹ QC; QC ⟹ bimonotone (via an argmax); `variation_le_two_range_of_quasiConcave` |
| `Sieve/KernelVariationBound.lean` | refactored: `kernelDiff_bimonotone` (∃ turning point) with `kernelDiff_variation_le` as its corollary |
| `Sieve/FibreKernelExact.lean` | `fibre_kernel_eq_Icc`: the kernel **is** `Icc ⌈max (x/n) √x⌉ ⌊min ((x+h√x)/m) (2√x)⌋` for `1 ≤ n ≤ m ≤ ⌊x+h√x⌋` |
| `Sieve/FibreSmoothWeight.lean` | `fibreSmooth x h k i := kernelSmooth (fibreLow x i) (fibreHigh x h (i+k))`; `abs_card_Icc_sub_smooth_le`; `0 ≤ fibreSmooth ≤ 3h+1`; `abs_kernel_sub_fibreSmooth_le : |K − s| ≤ 2` |
| `Sieve/FibreSmoothQuasiConcave.lean` | `min_sub_max : min B D − max A C = min (B−A, B−C, D−A, D−C)`; `quasiConcaveOn_fibreSmooth`; `fibreSmooth_variation_le ≤ 6h+2` |
| `Sieve/FibreShiftSupport.lean` | kernel `= ∅` for `k > h` and for `n ≥ 3√x`; `fibreSmooth = 0` for `n ≥ 3√x`; `abs_error_shift_sum_supported_le` |
| `Sieve/OffDiagonalReindex.lean` | `sum_offdiag_eq_shift`: the strict lower triangle reindexed by shift (a `Finset.sum_nbij'` on the product) |
| `Sieve/OffDiagonalShiftBound.lean` | `abs_offDiagonal_le : \|off-diag\| ≤ (9h+3)·∑_{k ≤ h} B k + 2h(3√x+1)` |
| `Sieve/OffDiagonalFromCorrelations.lean` | `AveragedCorrelationSmall`; `offDiagonalVanishes_of_correlations` |
| `Sieve/MRFromCorrelations.lean` | `averagedMeanSquare_of_correlations`; **`MRBilinear_moebius_of_correlations`** |

**The mechanism that made it work.**  The discrete kernel genuinely has variation `≍ √x`, so Abel
summation cannot be applied to it directly (unit 7's dead end).  The fix is the smooth/error split
plus one structural observation: an *interval-intersection length* is a **minimum of four endpoint
differences**, and quasi-concavity — not monotonicity, not bimonotonicity — is the property closed
under `min`.  Three of the four differences are monotone; the fourth is `kernelDiff`, unimodal by
the concavity of `kernelP`.  Hence the smooth model is quasi-concave, hence of variation at most
twice its range `[0, 3h+1]`.  The bound `Var ≤ Σ Var(pieces)` is useless here (two pieces have range
`≍ √x`); it is the `min` that keeps the cancellation.

**Parameter accounting.**  Shift support `k ≤ h` (from `a·k ≤ h√x` and `a ≥ √x`); inner support
`n ≤ 3√x`; weight cost `W = (3h+1) + 2(3h+1) = 9h+3`; error cost `2·h·3√x`.  Normalised by `h²√x`:
smooth term `≤ (9 + 3/h)·(∑_k B k)/(h√x)`, error term `≤ 6/h + 2/(h√x)`.  Both vanish exactly when
`∑_{k ≤ h} B k = o(h√x)`.

**Statement of the remaining input.**

```
AveragedCorrelationSmall f hh :=
  ∀ ε > 0, ∀ᶠ x, ∃ B, (∀ k, 0 ≤ B k)
    ∧ (∀ 1 ≤ k ≤ ⌊hh x⌋, ∀ J, |∑_{i<J} f(i+1)·f(i+1+k)| ≤ B k)
    ∧ ∑_{k ≤ ⌊hh x⌋} B k ≤ ε·hh x·√x
```

At `f = μ` this is the **averaged Chowla conjecture** (Matomäki–Radziwiłł–Tao 2015) in
maximal-partial-sum form — a theorem for `h → ∞`, not the open individual Chowla.  The maximal form
is what partial summation consumes; converting the known mean-value form into it is the next step.

**Side condition.**  `hh x ≤ √x` eventually.  This is a constraint on the window law, not an
analytic hypothesis: it says the short interval `[x, x + h√x]` is contained in `[x, 2x]`, which the
balanced-pairs decomposition presupposes.  Every window law used downstream satisfies it.

## Unit 9 — the input weakened to the published statement (Lean, unconditional)

**Correction to unit 8.**  `AveragedCorrelationSmall` quantifies over *all* initial segments
`j ≤ M ≍ x`, because `abs_shift_sum_le` (via `abs_sum_mul_le_of_bounded_partial_bv`) needs a bound
on every partial sum.  Requiring `∑_{k ≤ h} max_{j ≤ x} |∑_{i<j} μμ| = o(h√x)` is *square-root
cancellation at length `x`*, far beyond averaged Chowla.  Unit 8's implication is true but its
hypothesis is not the published theorem.  Unit 9 repairs this.

**The repair.**  The weight is supported on `[√x/2, √x + h]`, so only partial sums of length `≍ √x`
should ever enter.  Two changes make that visible to the proof:

1. **Put the shift-sum inside the summation by parts.**  Then the interface needed is
   `∑_{k ≤ h} |∑_{i<J} f(i)f(i+k)| ≤ P` for each `J` — one bound uniform in `J` — instead of
   `∑_k max_J |·|`.  The price is a majorant of `|Δ_j w(k,j)|` *uniform in `k`*, not merely a
   variation bound at each `k`.
2. **Kill the head term and cut off the majorant.**  The weight vanishes at `j = M − 1` and has no
   increments beyond the window, so `J` is confined to `J ≤ ⌈√x + h⌉ + 5`.

**The shift-uniform majorant.**  `fibreSmooth_decomp` rewrites the model as

```text
max( kernelDiff − (B − 2√x)⁺ − (√x − x/i)⁺ + 1 , 0 ) ,
```

and each piece depends on the shift monotonically:

| piece | shift dependence | consequence |
|---|---|---|
| `kernelDiff` | increment `x/(n(n+1)) − c/((n+k)(n+1+k))` is **nondecreasing in `k`** | `sup_k \|Δ\| ≤ \|Δ₁\| + \|Δ_K\|` |
| `(B_k − 2√x)⁺` | equals `G(i+k)` with `G` **convex** | `sup_k \|Δ\| = \|Δ at k = 1\|` |
| `(√x − x/i)⁺` | shift-free | — |

Summed across the window: `2·(2·20h) + (4h+8) + (h+6) = 85h + 14`.

**New machinery (7 modules, all `[propext, Classical.choice, Quot.sound]`).**

| Module | Statement |
|---|---|
| `Sieve/ShiftSumUniform.lean` | `CorrelationUniformBound f K J₀ P`; `abs_shift_sum_uniform_le : ≤ V·P` with the shift-sum inside, head-vanishing and length cutoff |
| `Sieve/FibreSmoothDecomp.lean` | `min_eq_sub_max_sub`, `max_eq_add_max_sub`, `fibreSmooth_decomp` |
| `Sieve/FibreIncrementUniform.lean` | `div_succ_sub_div_antitone`; `trunc_div_diff_antitone` (convexity of `(c/m − D)⁺`); `kernelDiff_increment_mono_shift`; `fibreIncrRaw`; `abs_fibreSmooth_increment_le` |
| `Sieve/FibreWindowVanish.lean` | `fibreWinLo`, `fibreWinHi`; `fibreSmooth` vanishes below `√x/2 − 1` and above `√x + h + 5`; increments vanish off the window |
| `Sieve/FibreIncrementWindow.lean` | `kernelDiff ∈ [−16h, 4h]` on the window; the two telescoping sums; `fibreIncr`; `sum_fibreIncr_le ≤ 85h + 14` |
| `Sieve/OffDiagonalUniformBound.lean` | `abs_offDiagonal_uniform_le : ≤ (85h+14)·P + 2h(3√x+1)` |
| `Sieve/MRFromUniformCorrelations.lean` | `UniformCorrelationSmall`; **`MRBilinear_moebius_of_uniformCorrelations`** |

**The input now reads**

```
UniformCorrelationSmall f hh :=
  ∀ ε > 0, ∀ᶠ x, ∀ J ≤ ⌈√x + hh x⌉ + 5,
    ∑_{k = 1}^{⌊hh x⌋} | ∑_{i < J} f(i+1)·f(i+1+k) |  ≤  ε · hh x · √x
```

At `f = μ` and `J ≍ √x` this is exactly the averaged Chowla theorem (Matomäki–Radziwiłł–Tao 2015)
at length `J`: for `J ≥ δ√x` it is their `o(HY)` estimate with `Y = J ≍ √x`, and for `J < δ√x` the
trivial bound `|∑_{i<J}| ≤ J < δ√x` already gives `∑_k ≤ δ·h·√x`.  No square-root cancellation is
asked for anywhere.

**Remaining.**  Formalise the passage from the published fixed-length statement to
`UniformCorrelationSmall` (the `δ`-split above), and then the averaged Chowla theorem itself.
