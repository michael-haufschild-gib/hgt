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
