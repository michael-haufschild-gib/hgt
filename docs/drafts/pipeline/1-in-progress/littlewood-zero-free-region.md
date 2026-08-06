# Littlewood zero-free region: Weyl differencing to κ < 1

- **ID:** `littlewood-zero-free-region`
- **Stage:** 1-in-progress
- **Type:** THEOREM PROGRAMME (classical formalization; no external novelty claimed)
- **Consumer:** the κ-criterion of `mr-splice-wide-range-mean-square.md` — the entire MR
  corridor (`MRBilinear` → Route E sign-class density) is gated on one formalized zero-free
  region with exponent κ < 1 (Littlewood's `log log`-refined κ = 1 qualifies); corpus and the
  vendored `PNTPlus` both own only κ = 9.
- **RH used:** no.

## Frozen target

```text
∃ c > 0, ζ(σ + it) ≠ 0  for  σ ≥ 1 − c·log log |t| / log |t|,  |t| ≥ t₀,
```

via the chain: Weyl differencing of growing order for `∑_{N<n≤2N} n^{-it}` →
`ζ(1+it) ≪ log t/log log t` (and the σ-near-1 rectangle versions) → the Landau/3-4-1 pipeline
already implemented in `PNTPlus/ZetaBounds` (with the improved growth input replacing
`ZetaUpperBnd'`'s `log|t|`).

## Asset audit (2026-08-05)

- `PNTPlus/ZetaBounds.lean`: full Landau pipeline (`ZetaUpperBnd'` growth `≪ log|t|` on
  `σ ≥ 1 − A/log|t|`, 3-4-1 lower bounds, `ZetaZeroFree` at κ = 9).  **Read-only vendored
  area**: the upgrade must live in corpus modules importing it, never edits to it.
- Corpus `Sieve/ZeroLinePower`/`ZeroLineSum`: Euler–Maclaurin layer for `∑ n^{iv}` — the k = 1
  base and partial-summation tools.
- mathlib: **no** van der Corput (integral or sum), no Kuzmin–Landau, no Weyl differencing —
  all three are from-scratch builds (elementary, constant-heavy).

## Stage L1 `[DONE]` — numeric pre-certification of the whole chain

Implemented the k-th-derivative-test bound (Titchmarsh 5.13 shape, constants modeled
`A_k = c·2^k`, both terms, validity-free minimization over `k ≤ 80` against the trivial
`log 2` per dyadic block) for `∑_{n≤t} n^{-1-it}`:

```text
log t =    230:  bound/(log t/log log t) = 1.93   (k used ≤ 4)
log t =   2303:  ratio = 1.58                     (k ≤ 6)
log t =  23026:  ratio = 1.38                     (k ≤ 9)
log t = 230259:  ratio = 1.24                     (k ≤ 11)
```

Robust under 10× inflation of the modeled constants (ratio moves ≤ 15%).  The k-schedule the
optimizer selects matches the classical `k ≈ log t/log N + 1` per block with
`k_max ≈ log log t/log 2`.  **The Littlewood shape and constant chain are certified; the
formalization is licensed.**

## Staged plan

- **L2** — paper proof with honest constants: Kuzmin–Landau (monotone phase, geometric bound);
  one Weyl step `|S|² ≤ N + 2∑_h |∑ e(Δ_h f)|`; the k-fold recursion and the packaged k-th
  derivative test with explicit `A_k`; re-run the L1 script with the honest `A_k` to re-certify.
- **L3** — Lean: Kuzmin–Landau.
- **L4** — Lean: the Weyl differencing step and its k-fold iteration.
- **L5** — Lean: the derivative test; dyadic assembly; `ζ(1+it) ≪ log t/log log t` and the
  rectangle version `ζ(σ+it)` for `σ ≥ 1 − c'·log log/log` (same phases, Abel in the
  `n^{-σ}` weight).
- **L6** — corpus module rerunning the `PNTPlus` Landau pipeline with the improved input →
  the Littlewood region; then unit-5 re-certification on the MR card at Littlewood tier and the
  route-B assembly.

## Hostile falsifiers

- The derivative-ratio parameter (`|f^{(k)}|` spans a factor `2^k` on dyadic blocks) must be
  carried explicitly through the test's constants — dropping it silently voids L1's model.
- The Landau pipeline needs `ζ` growth on a rectangle left of `σ = 1`, not only at `σ = 1`;
  L5's rectangle version is load-bearing, not cosmetic.
- If L2's honest constants exceed the modeled `10×` margin, L1 must be re-run before L3–L5
  proceed.

## Log

- 2026-08-05 — card created; asset audit done; L1 certified (script inline in the session,
  results above).

## 2026-08-05 L2 opened: the constant falsifier is retired

Stress-tested L1 under aggressive constant-growth laws for the k-th derivative test
(`A_k ∈ {10·2^k, 4^k, 8^k, 20^k, 2^{k²/4}}`, dyadic strides 1/4/32 at
`log t = 2.3·10³ / 2.3·10⁴ / 2.3·10⁵`):

```text
ratio to log t/log log t stays in [1.24, 1.93] for ALL models and heights,
still decreasing in t; e.g. at log t = 230259: 1.24 (10·2^k) … 1.41 (20^k).
```

Mechanism: the per-block saving exponent is `−log t/(k·2^k)·(1+o(1))` while the constant costs
only `log A_k ≈ k·log c` — the optimizer absorbs any fixed-base exponential (even `2^{k²/4}`)
by a slight downward shift of the k-schedule.  **Consequence: stages L3–L5 may use the crudest
convenient constants at every step; no sharpness anywhere in the Weyl chain is load-bearing.**
The L1 falsifier ("if honest constants exceed the 10× margin…") is retired.

### L2 remaining content (the paper document, next block)

Equation-level derivations with generous constants, in dependency order:
1. **(KL)** Kuzmin–Landau: `g'` monotone, `‖g'‖ ≥ δ` on `I` ⟹ `|∑_I e(g(n))| ≤ C/δ + C`
   (telescoping weights `1/(e(Δg)−1)`, partial summation; Graham–Kolesnik Lemma 4.7 shape).
2. **(D2)** second-derivative test from (KL) by integer-crossing splitting:
   `|S| ≤ C·(hN√λ₂ + 1/√λ₂)` for `λ₂ ≤ |g''| ≤ hλ₂`.
3. **(W)** the exact Weyl step `|S|² ≤ N + 2∑_{h<N}|∑ e(Δ_h g)|`.
4. **(Dk)** the k-th derivative test by induction (Graham–Kolesnik Thm 2.9 chain), crude
   constants; validity bookkeeping of the derivative-ratio `h = 2^k` on dyadic blocks.
5. **(Z)** dyadic assembly with the `1/n`-Abel weights and the `∑_{n≤t}` truncation ⟹
   `ζ(1+it) ≤ C·log t/log log t` (constants per L1).
6. **(R)** the region transfer: Titchmarsh's classical chain from the 1-line bound to
   `σ ≥ 1 − c·log log t/log t` (Borel–Carathéodory/3-4-1, mirroring the PNTPlus pipeline's
   dependency graph so L6 is a drop-in input upgrade); second numeric gate on the transfer
   bookkeeping before L6.

- 2026-08-05 — constant stress test done (this section); L2 document is the next block.

- 2026-08-05 — **L2 paper document complete**: `littlewood-l2-weyl-chain.md` — (KL) with
  constant `1/δ + 1`; (D2) `5hN√λ + 15/√λ`; the windowed Weyl step (W); the k-th derivative
  test (Dk) with the honest exponent pair `(h²λ)^{e_k}` / `N^{1−2^{2−k}}λ^{−2^{1−k}}` and the
  **bounded** constant recursion `A_k ≤ 15√A_{k−1} + 4 ≤ 256` (better than every stress-tested
  growth law); (Z) the dyadic assembly.  Honest-shape re-certification: ratios to
  `log t/log log t` = 2.09 / 1.56 / 1.33 / 1.19 at `log t = 230 … 230259`.  Remaining in L2:
  the stage-(R) region-transfer numeric gate; then L3 (Lean Kuzmin–Landau) begins.

## 2026-08-05 L2 CLOSED: the (R) gate certifies a positive region constant

End-to-end numeric gate (Ford-detector + 3-4-1, log-domain, with the certified honest-shape
Weyl-chain growth `B(x, L)` as the ONLY analytic input; pole term `3/(aδ) + 3`, detected-zero
cot expansion with its `π²(a+1)δ/(8η²)` correction, right-line `log(1/(aδ+η)) + 2`,
prefactor `5/(2η)`):

```text
log t =  2303:  ζ ≠ 0 for σ ≥ 1 − 0.0149·loglog t/log t   (a = 6, η = 4·(loglog t)²/log t)
log t = 23026:  c = 0.0179                                 (a = 6, η = 8·(loglog t)²/log t)
```

The constant increases with height, matching the symbolic balance (the window lives at
`η ≍ (loglog t)²/log t`, where the `φ`-term, the `log(1/η)` right-line term, and the
`loglog` remainders all sit at the same scale; the region constant tends to an absolute
limit).  **The entire Littlewood chain — (KL), (D2), (W), (Dk), (Z), (R) — is now
dependency-closed on paper and numerically certified end-to-end with crude constants.**

Stage status: L1 ✓, L2 ✓ (this entry).  Next: **L3 — `Sieve/KuzminLandau.lean`**, per the
Lean mapping in `littlewood-l2-weyl-chain.md`.

- 2026-08-05 — L2 closed; region constant gate certified positive.

## 2026-08-05 L3 built: Kuzmin–Landau in Lean

`RHTower/Sieve/KuzminLandau.lean` (wired into `RHTower.lean`; targeted build 3272 jobs pass;
axioms only `propext, Classical.choice, Quot.sound`; zero warnings):

- `sin_pi_mul_pos`, `two_mul_le_sin_pi_mul` (Jordan on the band, both halves via
  `Real.mul_le_sin` and `sin_pi_sub`), `cot_pi_mul_antitone` (the `sin_sub` cross-difference
  identity), `cot_pi_mul_le`;
- `klCoeff β = −1/2 − i·cot(πβ)/2` with `klCoeff_mul` (inverts the phase chord; proof via the
  factorization `e(β) − 1 = 2S(−S + Ci)` and `linear_combination` against `I² = −1` and
  `S² + C² = 1`), `norm_klCoeff_le ≤ 1/(4δ)` (through the corpus's `norm_exp_I_sub_one` /
  Jordan chord lemmas from `ChordalSeparation`), `norm_klCoeff_sub` (differences are purely
  imaginary cotangent differences — the telescoping device);
- **`kuzminLandau_band`**: a phase sequence with monotone increments confined to `[δ, 1−δ]`
  has exponential sum `≤ 3/(2δ) + 1`, uniformly in length.  Summation by parts is mathlib's
  partial-sum `Finset.sum_range_by_parts` (which costs the harmless factor 2 relative to the
  paper's `1/δ + 1` — constants are certified irrelevant), and the coefficient variation
  telescopes by `Finset.sum_range_sub'` since the cotangent values are antitone.

Lean traps recorded: `positivity` cannot use sign hypotheses (`0 < π·β` needs `nlinarith`);
mathlib's `sum_range_by_parts` is the partial-sum Abel form (`f·g` with `∑g`-partials), not
the `f·Δg` form; `push_cast` turns `((Real.sin x : ℝ) : ℂ)` into `Complex.sin ↑x` — keep
`ofReal` atoms via `simp only [Complex.ofReal_*]` instead when matching `set`-abbreviations;
`Complex.norm_ofReal` does not exist — use `Complex.norm_real` + `Real.norm_eq_abs`.

Index regeneration deferred to the next module batch (L4) per efficiency discipline.

Stage status: L1 ✓, L2 ✓, **L3 ✓**.  Next: **L4 — the windowed Weyl step (W) and the k-fold
iteration**, pure Cauchy–Schwarz/counting per the L2 mapping.

- 2026-08-05 — L3 built and verified.

## 2026-08-05 L4 (first half) built: the windowed Weyl–van der Corput inequality

`RHTower/Sieve/WeylDifferencing.lean` (wired into `RHTower.lean`; targeted build 3274 jobs;
axioms only `propext, Classical.choice, Quot.sound`; zero warnings):

- `weylCorr a N h` — the `h`-shifted autocorrelation `∑_{n<N−h} a(n+h)·conj(a n)`, with
  `norm_weylCorr_zero_le` (energy `≤ N` for bounded coefficients);
- `weylShift`/`sum_weylShift` — the `if`-supported shifted windows (each sums to the full sum;
  no fibre combinatorics anywhere);
- `sum_weylShift_mul_conj` — two shifted windows correlate to a shifted autocorrelation
  (`Ico`-filter collapse + `sum_Ico_eq_sum_range` reindexing), symmetric via conjugation
  (`norm_sum_weylShift_mul_conj` with the `max/min` distance);
- `sum_norm_weylCorr_row_le` — one row of shifts costs at most twice the distance-indexed sum
  (two explicit `sum_bij'` reindexings);
- **`weyl_vdc`**: for `‖a n‖ ≤ 1` and any window `1 ≤ H ≤ N`,

  ```text
  H·‖∑_{n<N} a n‖² ≤ 4N·(N + ∑_{h=1}^{H−1} ‖weylCorr a N h‖).
  ```

  Chain: averaged representation (`H·S = ∑ T_m` over the enlarged window) → Cauchy–Schwarz
  (`sq_sum_le_card_mul_sum_sq`, needs `import Mathlib.Algebra.Order.Chebyshev`) → energy
  expansion through `re` (`Complex.mul_conj`, `re_le_norm`) → the row bound → zero-shift
  split-off.  The correlation sums run over full truncated ranges — exactly what the (Dk)
  induction consumes when `a` is a smooth phase.

Bug caught by the compiler during the build: the first draft of the row lemma's second
bijection evaluated the distance function at `d + r` instead of `d` — a genuine mathematical
slip, fixed with the `max/min` rewrites.

Stage status: L1 ✓, L2 ✓, L3 ✓, **L4a ✓** (windowed Weyl step).  Next: **L4b — the (D2)
second-derivative test** (Kuzmin–Landau + integer-crossing splitting), then **L5 — the (Dk)
induction** consuming `weyl_vdc` and (D2).

- 2026-08-05 — L4a built and verified.

## 2026-08-05 L4b-i built: Kuzmin–Landau at unit-spaced sample points

`RHTower/Sieve/KuzminLandauInterval.lean` (wired; build 3273 jobs; axioms only
`propext, Classical.choice, Quot.sound`; zero warnings; one-iteration compile):

- `exp_two_pi_I_sub_int` — integer shifts leave the phase `e(y)` unchanged
  (`Complex.exp_int_mul_two_pi_mul_I`);
- **`kuzminLandau_interval`** — for a phase `g` with `HasDerivAt g (g' x) x` on the span,
  `g'` monotone and confined to one integer band `[m+δ, m+1−δ]`:

  ```text
  ‖∑_{j=0}^{M} e(g(x₀+j))‖ ≤ 3/(2δ) + 1,
  ```

  uniformly in `M`.  The bridge: `exists_hasDerivAt_eq_slope` per unit step (with the slope
  denominator normalized by `field_simp; ring`), interlacing of the mean-value points for the
  increment monotonicity, per-goal `obtain`s (no global choice needed — the increments are
  canonical, the MVT only bounds them), and the integer shift `φ j = g(x₀+j) − m·j` feeding
  the discrete `kuzminLandau_band`.

Stage status: L1–L3 ✓, L4a ✓ (Weyl step), **L4b-i ✓** (calculus bridge).  Remaining in L4b:
(ii) the monotone-fibre interval splitting (fibres of a monotone `ℤ`-classification on
`range N` are integer intervals; image count bounded by the classification range), and
(iii) the (D2) assembly via the region index `I(y) = ⌊y−δ⌋ + ⌊y+δ⌋` (even = band → the
interval lemma above; odd = gap → trivial count from the slope at the fibre's endpoints).

- 2026-08-05 — L4b-i built and verified.

## 2026-08-05 L4b-ii built: monotone-fibre interval splitting

`RHTower/Sieve/MonotoneFibers.lean` (wired into `RHTower.lean`; targeted build 8693 jobs;
axioms only `propext, Classical.choice, Quot.sound`; zero warnings). Also re-audited
`KuzminLandauInterval.lean` after the span weakening (`Icc x₀ (x₀+M)` instead of `x₀+M+1` —
the D2 fibres only control the derivative up to the last sample point): both build clean.

- `sum_eq_sum_image_fibers` / `norm_sum_le_sum_image_fibers` — a sum over `range N` splits
  over the fibres of any `ℤ`-classification (`Finset.sum_fiberwise_of_maps_to`);
- `filter_eq_Ico_of_monotone` — fibres of a monotone classification are integer intervals
  (`min'`/`max'` endpoints + the monotone squeeze `K min' ≤ K n ≤ K max'` forces membership);
- `card_image_le_of_monotone` — the number of distinct values is `≤ K(N−1) − K(0) + 1`
  (image ⊆ `Icc (K 0) (K (N−1))`, `Int.card_Icc`, cast bridge via
  `congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg _)` — `push_cast` alone mangles the
  `toNat` coercion inconsistently between hypothesis and goal; lift the ℤ-equation to ℝ by
  `congrArg` first, then `push_cast; ring`).

Stage status: L1–L3 ✓, L4a ✓, L4b-i ✓, **L4b-ii ✓**.  Next: **L4b-iii — the (D2) assembly**
via the region index `I(y) = ⌊y−δ⌋ + ⌊y+δ⌋` (monotone in `y`; even values = bands
`[m+δ, m+1−δ)` with `m = v/2` → `kuzminLandau_interval` per fibre; odd values = gaps →
fibre length `≤ 2δ/λ + 1` from the slope lower bound at the fibre's endpoints; value count
`≤ 2Nhλ + 3` from `card_image_le_of_monotone`; `δ = √λ/2`; target
`‖S‖ ≤ 12hN√λ + 18/√λ`).

- 2026-08-05 — L4b-ii built and verified.

## 2026-08-05 L4b CLOSED: the (D2) second-derivative test in Lean

`RHTower/Sieve/SecondDerivativeTest.lean` (wired into `RHTower.lean`; targeted build 8694
jobs; axioms only `propext, Classical.choice, Quot.sound`; zero warnings):

- `regionIdx δ y = ⌊y−δ⌋ + ⌊y+δ⌋` with `regionIdx_mono`, `regionIdx_diff_le`
  (`≤ 2·(y'−y) + 2`), and the parity dichotomy for `2δ ≤ 1`: `regionIdx_even_band`
  (`= m+m ⟹ y ∈ [m+δ, m+1−δ]`) and `regionIdx_odd_gap` (`= 2m+1 ⟹ y ∈ [m+1−δ, m+1+δ)`) —
  proved by the two-floor squeeze `⌊y−δ⌋ ≤ ⌊y+δ⌋ ≤ ⌊y−δ⌋+1` plus `omega` parity;
- **`second_derivative_test`**: for `λ ≤ g'' ≤ h·λ` on the span, `0 < λ ≤ 1`,

  ```text
  ‖∑_{n<N} e(g(x₀+n))‖ ≤ (2Nhλ + 3)·(3/√λ + 1),
  ```

  with `δ = √λ/2`; even fibres feed `kuzminLandau_interval` (band transferred from the two
  fibre endpoints to the whole run by `MonotoneOn g'`), odd fibres are counted by the
  MVT slope (`λ·M < 2δ` across the gap), the fibre count by `card_image_le_of_monotone` +
  `regionIdx_diff_le` + the upper MVT bound;
- **`second_derivative_test'`**: the expanded form `‖S‖ ≤ 8Nh√λ + 12/√λ` (better than the
  paper target `12hN√λ + 18/√λ`); `1 ≤ h` is derived, not assumed, from `λ ≤ g''(x₀) ≤ hλ`.

Lean traps: `Real.sqrt_le_one` is now an iff (`.mpr`); `⌊·⌋`-definitions must be
`noncomputable`; never `rw [← hsqsq]` when the goal contains `Real.sqrt lam` (it rewrites
`lam` inside the sqrt — use `linear_combination c * hsqsq` instead); division bounds done
inv-form (`div_eq_mul_inv` + `mul_inv_cancel₀` + `nlinarith`) to avoid the deprecated
`lt_div_iff` family.

Stage status: L1–L3 ✓, L4a ✓, **L4b ✓ (D2 complete)**.  Next: **L5 — the (Dk) induction**
consuming `weyl_vdc` + `second_derivative_test'` (statement per
`littlewood-l2-weyl-chain.md`: `A_k ≤ 256`, window `H := ⌈(h²λ)^{−e'/(1+e')}⌉ ⊓ N`,
exponent identity `e_k = (1/2)·e'/(1+e')`, trivial branch when `h²λ > 1`).

- 2026-08-05 — L4b closed (D2 built and verified).

## 2026-08-05 L5 (Dk) CLOSED: the k-th derivative test in Lean

Two new modules (wired into `RHTower.lean`; targeted build 8697 jobs; axioms only
`propext, Classical.choice, Quot.sound`; zero warnings):

`RHTower/Sieve/PhaseCorrelation.lean`:
- `exp_mul_conj_exp` (phases multiply against conjugates by phase subtraction),
- `weylCorr_phase` — the shifted autocorrelation of `n ↦ e(g(x₀+n))` IS the exponential sum
  of the difference phase `x ↦ g(x+h) − g(x)` over `range (N−h)`,
- `norm_weylCorr_le`, `norm_phase_sum_le_card` (trivial bounds).

`RHTower/Sieve/KthDerivativeTest.lean`:
- **`kth_derivative_test`**: for a derivative chain `G` (`HasDerivAt (G i) (G (i+1) x) x`,
  `i < k`) with `λ ≤ G k ≤ h·λ` on the span, `0 < λ ≤ 1 ≤ h`, `k ≥ 2`:

  ```text
  ‖∑_{n<N} e(G 0(x₀+n))‖ ≤ 256·( N·(h²λ)^{1/(2^k−2)} + N^{1−4/2^k}·λ^{−2/2^k} ),
  ```

  by `Nat.le_induction` (base = `second_derivative_test'`, 8Nh√λ+12/√λ ≤ 256(...)).
  Step: window `H := min ⌈(h²λ)^{−e'/(1+e')}⌉₊ N` in `weyl_vdc`; each correlation is the
  difference phase via `weylCorr_phase` and consumes the IH at `(λ', h') = (h'λ, h)` — same
  ratio one order down (MVT slope) — with the trivial bound absorbed by `(h²h'λ)^{e'} ≥ 1`
  when `h'λ > 1`, and `h²λ ≥ 1` handled before windowing.  Case split cap/no-cap; the
  exponent identities `e'/(1+e') = 2e_{k+1}`, `2β' = 1+β`, `2γ' = γ` square the bound back;
  the final constants are `√2052 ≤ 256` (no cap) and `√2052 ≤ 256` (cap).

Lean traps recorded: `rw [pow_succ]` on the goal grabbed `hgrow^2` (first-match
instantiation!) — pin with `rw [show ((2:ℝ)^(k+1)) = (2:ℝ)^k*2 from pow_succ 2 k]`;
`set`-bound locals make `linarith`/`nlinarith` zeta-unfold rpow towers — `clear_value` the
whole batch once their defining equations are banked, and use `linarith only [...]`
everywhere in the giant context (the bare simplex ran past 1.6M heartbeats);
`le_or_lt` is gone — `le_or_gt`; `div_le_div_iff` → `div_le_div_iff₀`; `rw` closes
`weylCorr_phase`-goals by rfl through let-bound difference phases (don't add congr steps).

Stage status: L1–L4 ✓, **L5 (Dk) ✓**.  Next: **(Z) — the dyadic assembly**: block data
`g(x) = −(t/2π)·log x` on `(N, 2N]` (`λ = (t/2π)(k−1)!(2N)^{−k}`, `h = 2^k`, `(h²)^{e_k} ≤ 4`),
Abel `1/n` weights, per-block k-minimization vs the trivial `log 2`, `∑_{n≤t}` truncation →
`ζ(1+it) ≤ C·log t/loglog t` and the rectangle version; then L6 (Ford transfer).

- 2026-08-05 — L5 (Dk) built and verified.

## 2026-08-05 (Z) opened: block layer built (Z1 concrete phase, Z2 Abel)

Two new modules (wired; targeted builds 8698/8699 jobs; axioms clean; zero warnings):

`RHTower/Sieve/LogPhaseBlock.lean` (Z1):
- `logPhase t = -(t/2π)·log`, `logPhaseChain t` (i-th member `(t/2π)(−1)^i(i−1)!·x^{−i}`),
  `logPhaseChain_hasDerivAt` (honest chain on `(0,∞)`; `HasDerivAt.inv` on `x^{i+1}`),
  `logPhaseChain_signed_bounds` (the sign-corrected member pinned on `[A,B]`),
  `norm_phase_sum_neg` (negated phase = conjugated sum; norms equal),
  `natCast_cpow_neg_I_mul` (`n^{-it}` IS the phase `e(g_t(n))`);
- **`dirichlet_block_bound`**: for `k ≥ 2`, `λ = (t/2π)(k−1)!/(2N)^k ≤ 1`, a run of `L`
  phases inside `[N, 2N]`: `‖∑_{j<L}(N+j)^{-it}‖ ≤ 256(L(4^kλ)^{e_k} + L^{1−4/2^k}λ^{−2/2^k})`
  — even `k` feeds the chain to `kth_derivative_test` directly, odd `k` negates it.

`RHTower/Sieve/DirichletBlockAbel.lean` (Z2):
- `sum_weight_mul_eq_abel` (discrete Abel identity on `Ico N M`, ℂ-valued, prefix sums
  against backward weight differences plus boundary),
- `abel_block_bound` (**Abel's inequality**: decreasing nonneg weight × uniformly bounded
  prefixes ≤ `P·w(N)`),
- `dirichlet_block_one_bound` (`n^{-1-it} = (1/n)·n^{-it}` via `cpow_add`; ≤ `P/N`),
- **`dirichlet_block_one_full`**: the composed dyadic bound
  `‖∑_{N≤n<M} n^{-1-it}‖ ≤ 256((M−N)(4^kλ)^{e_k} + (M−N)^{1−4/2^k}λ^{−2/2^k})/N`
  for `N ≤ M ≤ 2N+1` (every prefix run through Z1; monotone in the run length).

Remaining in (Z): **Z3** — the schedule: head `∑_{n≤X₀} 1/n ≤ log X₀ + 1` with
`X₀ ≈ t^{1/m}`, `m ≈ loglog t`; per tail block `k(N) := ⌈log t/log N⌉ + 1` (or its
`t ≤ N^{k−1/2}` refinement) with the `λ ≤ 1` gate `(k−1)! ≤ 2π·2^k·√N` and per-block bound
`≤ C/log t`; sum over `≤ log₂ t` blocks.  **Z4** — the `∑_{n≤t}` truncation from the
PNTPlus `ZetaSum/Zeta0EqZeta` layer (`riemannZeta0_apply` at `s = 1+it`).  **Z5** — the
rectangle version (`w n = n^{−σ}` in the same `abel_block_bound`).

- 2026-08-05 — Z1+Z2 built and verified.

## Z3a/Z3b built (2026-08-05)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSaving.lean` — built, wired into the
`RHTower` umbrella, axioms `[propext, Classical.choice, Quot.sound]`, zero warnings.

- `dirichlet_block_one_normalized` — absorbs the block-length factor of
  `dirichlet_block_one_full`. For `N <= M <= 2N+1`, `k >= 2`, `lam <= 1`:

  ```text
  ‖∑_{Ico N M} n^(-1-It)‖ <= 512*(4^k*lam)^(1/(2^k-2)) + 512*N^(-4/2^k)*lam^(-2/2^k)
  ```

  with `lam = (t/2pi)*(k-1)!/(2N)^k`. The bound now depends only on `(N, k, lam)`.

- `block_saving` — the balanced window. If `4^k*lam <= N^(-1)` and `N^(-3/2) <= lam` then the
  normalised bound is at most `1024*N^(-1/2^k)`.

Both conditions are what the k-schedule must deliver, and they are simultaneously satisfiable
exactly when `4^k <= N^(1/2)`, i.e. `2^k <= N^(1/4)` — comfortably true on the tail blocks
`N >= t^(1/m)`, `m ~ loglog t`, where `k <= m`. This is the formal version of the card's warning not
to overshoot `k` by a full unit: the branch `t </> N^(k0-1/2)` is precisely the choice that keeps
`lam` inside `[N^(-3/2), 4^(-k) N^(-1)]`.

Remaining in Z3: the schedule itself (choose `k(N)` per block and verify the two window
inequalities from a branch on `t` versus `N^(k0-1/2)`), then the head/tail split against
`Sieve/HarmonicLogBound` and summation of `1024*N^(-1/2^k)` over dyadic `N`.

### Correction: the narrow window is unusable; use `block_saving_wide`

`block_saving`'s window has multiplicative width `4^(-k)*N^(1/2)` in `lam`, but `lam` jumps by the
factor `2N/k` when `k` increases by one. Width < step, so no integer schedule is guaranteed to land
in it. That window is therefore a dead end for Z3.

`block_saving_wide` (same module) relaxes the target saving from `N^(-1/2^k)` to `N^(-1/(3*2^k))`
and widens the window to

```text
N^(-5/3) <= lam <= N^(-1/3),
```

of multiplicative width `N^(4/3)`, which exceeds the step `2N` as soon as `N >= 8`. Conclusion:

```text
512*(4^k*lam)^(1/(2^k-2)) + 512*N^(-4/2^k)*lam^(-2/2^k) <= 2560*N^(-1/(3*2^k)).
```

The balance point `lam ~ N^(-4/3)` sits in the middle of this window, matching the classical choice
`k ~ log t/log N + 4/3`. Z3's remaining step is the existence of an integer `k >= 2` putting
`lam_k = (t/2pi)(k-1)!/(2N)^k` into `[N^(-5/3), N^(-1/3)]`, which is now a width-versus-step
argument rather than a balancing act.

## Z3 schedule step closed (2026-08-05)

`formal/GaloisForLFunctions/HTGeometry/RatioBoundedWindowLanding.lean` and
`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSchedule.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `exists_mem_window_of_ratio_lower_bound` (HTGeometry, reusable) — a sequence starting at or above
  `L`, satisfying `c * u (m-1) <= u m` above the start index, and eventually dropping to `U` or
  below, hits `[L, U]` provided `L <= c * U`. Proof: take the least index at which it drops below
  `U`; at that index the previous value was above `U`, so the ratio bound keeps the value above
  `c * U >= L`. No optimisation, no balancing.
- `blockLambda`, `blockLambda_ratio` — the derivative scale
  `lam_k = (t/2pi)(k-1)!/(2N)^k` satisfies `lam_m >= lam_(m-1)/N` for every `m >= 3`
  (the exact ratio is `(m-1)/(2N) >= 1/N`).
- `exists_blockLambda_in_window` — instantiation: the width condition is
  `N^(-5/3) <= (1/N) * N^(-1/3) = N^(-4/3)`, true for every `N >= 1`. So the schedule needs only
  `lam_2 >= N^(-5/3)` and some `k >= 2` with `lam_k <= N^(-1/3)`.
- `exists_dirichlet_block_saving` — the capstone: under those two hypotheses,

  ```text
  exists k >= 2, ‖sum_{Ico N M} n^(-1-It)‖ <= 2560 * N^(-1/(3*2^k)).
  ```

Note the `N >= 8` heuristic in the previous entry is not needed for the formal statement: only
`L <= c*U` is used, which holds for all `N >= 1`. The `N >= 8` remark was about the width exceeding
the step in the informal picture.

Remaining in Z3: the head/tail split against `Sieve/HarmonicLogBound`, discharging the two schedule
hypotheses from a `t`-versus-`N` branch on the tail blocks, and summing `2560*N^(-1/(3*2^k))` over
dyadic `N`.

## Z3 per-block estimate now fully explicit (2026-08-05)

`Sieve/DirichletBlockSchedule.lean` extended; `HTGeometry/RatioBoundedWindowLanding.lean`
strengthened to also bound the landing index. Built, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `exists_mem_window_of_ratio_lower_bound` now takes the drop witness `k0` explicitly and returns
  `k <= k0` as well. This matters: the produced order is the least one, so the saving exponent is
  controlled by the witness.
- `blockLambda_two_ge` : `8*pi*N^(1/3) <= t` implies `lam_2 >= N^(-5/3)`.
  (`lam_2 = t/(8*pi*N^2)`, and `N^2 * N^(-5/3) = N^(1/3)`.)
- `blockLambda_le_of_order` : `2 <= k`, `k-1 <= N`, `t <= 2*pi*2^k*N^(2/3)` imply
  `lam_k <= N^(-1/3)`. Mechanism: `(k-1)! <= N^(k-1)` when `k-1 <= N`, so
  `lam_k <= (t/2pi)/(2^k*N)`.
- `dirichlet_block_saving_of_range` — the capstone with **checkable hypotheses only**:

  ```text
  8*pi*N^(1/3) <= t <= 2*pi*2^(k0)*N^(2/3),  k0 >= 2,  k0-1 <= N,  N <= M <= 2N+1
    ==>  ‖sum_{Ico N M} n^(-1-It)‖ <= 2560 * N^(-1/(3*2^(k0))).
  ```

No existential order hypothesis survives: the schedule is discharged internally, and the saving is
expressed in the caller's own `k0`. Choosing `k0 ~ log_2(t/(2*pi*N^(2/3))) + 1` gives the classical
`k ~ log t/log N` and the saving `exp(-c*log N/2^(k0))`.

Remaining in Z3: head/tail split against `Sieve/HarmonicLogBound`, and summing the per-block bound
over dyadic `N` with the per-block `k0` schedule.

## Correction: the crude factorial estimate is lossy; sharp interface added (2026-08-05)

`dirichlet_block_saving_of_range` above is true but **not usable for the Littlewood saving**. Its
window-top hypothesis `t <= 2*pi*2^(k0)*N^(2/3)` came from the crude estimate
`(k-1)! <= N^(k-1)` (valid when `k-1 <= N`), which throws away the whole gap between `(k-1)!` and
`N^(k-1)`. It forces `2^(k0) >~ t/N^(2/3)`, i.e. `k0 ~ log_2 t`, whereas the classical schedule
needs `k ~ log t / log N`. With `k0 ~ log_2 t` the saving `N^(-1/(3*2^(k0)))` is essentially 1.

The honest condition is the exact one. Added to `Sieve/DirichletBlockSchedule.lean`:

- `blockLambda_le_iff` :
  `lam_k <= U  <->  t*(k-1)! <= 2*pi*(2N)^k*U`.
  No factorial estimate is baked in; the caller supplies whichever estimate its range of `k`
  supports.
- `blockLambda_le_of_factorial_bound` : the `U = N^(-1/3)` specialisation.
- `dirichlet_block_saving_of_factorial_range` : same conclusion as the earlier capstone, with the
  window-top hypothesis in exact form:

  ```text
  8*pi*N^(1/3) <= t,   t*(k0-1)! <= 2*pi*(2N)^(k0)*N^(-1/3),   k0 >= 2,   N <= M <= 2N+1
    ==>  ‖sum_{Ico N M} n^(-1-It)‖ <= 2560 * N^(-1/(3*2^(k0))).
  ```

Taking logs, the hypothesis reads `k0*log(2N) - log((k0-1)!) >= log t + (1/3)*log N`, and with
`(k0-1)! <= (k0-1)^(k0-1)` this is `k0*(log(2N) - log k0) >~ log t`, i.e. the classical
`k0 ~ log t / log N`. That is the estimate the dyadic assembly must supply per block; the crude
`k-1 <= N` version is retained only as a convenience for blocks with `N` comparable to `t`.

## Classical-scale window condition (2026-08-06)

The exact interface is now instantiated at the scale the assembly actually needs. Added to
`Sieve/DirichletBlockSchedule.lean`, built, axioms `[propext, Classical.choice, Quot.sound]`:

- `blockLambda_le_of_small_factorial` : if `k >= 1`, `(k-1)! <= N` (as naturals), and
  `t <= 2*pi*2^k*N^(k-1)*N^(-1/3)`, then `lam_k <= N^(-1/3)`.
  Mechanism: `t*(k-1)! <= t*N <= 2*pi*2^k*N^(k-1)*N^(-1/3)*N = 2*pi*(2N)^k*N^(-1/3)`.
- `dirichlet_block_saving_of_small_factorial` : the capstone at that scale.

Reading the hypothesis as `t ~ N^(k-4/3)` gives `k ~ log t/log N + 4/3` — exactly the classical
schedule, with no loss.

Why `(k-1)! <= N` is comfortable in the intended range: the assembly uses `N >= t^(1/m)` with
`m ~ loglog t`, so `k <= m` and `(k-1)! <= (loglog t)^(loglog t) = (log t)^(o(1))`, while
`N >= exp(log t/m)`. The factorial is negligible there; it was only the *crude bound*
`(k-1)! <= N^(k-1)` that was catastrophic, not the factorial itself.

Three tiers now exist for the same conclusion, in increasing usability:
`dirichlet_block_saving_of_range` (crude, `k-1 <= N`, forces `k ~ log_2 t` — unusable),
`dirichlet_block_saving_of_factorial_range` (exact, caller supplies any estimate),
`dirichlet_block_saving_of_small_factorial` (classical scale, `(k-1)! <= N`).

## Dyadic tail assembly built (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletDyadicTailAssembly.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `sum_Ico_dyadic` (generic `AddCommMonoid`, no arithmetic content) — iterating
  `Finset.sum_Ico_consecutive` splits `[A, A*2^R)` into the blocks `[A*2^r, A*2^(r+1))`.
  No positivity hypothesis is needed.
- `norm_sum_Ico_dyadic_le` — the triangle inequality across those blocks.
- `dirichlet_tail_dyadic_le` — the tail estimate: given per-block orders `k r` satisfying the
  classical-scale hypotheses at each `N_r = A*2^r`,

  ```text
  ‖sum_{Ico A (A*2^R)} n^(-1-It)‖ <= sum_{r<R} 2560 * (A*2^r)^(-1/(3*2^(k r))).
  ```

Each block has `M = 2N` exactly, so the length constraint `N <= M <= 2N+1` of the per-block
estimate is met with room.

Remaining in Z3: the head `sum_{n < A} 1/n` (owned: `Sieve/HarmonicLogBound.sum_Icc_one_div_le_one_add_log`,
and the per-block trivial bound `Sieve/HarmonicDyadicBlock.sum_Icc_one_div_le_log_sub`), the choice
of `A = t^(1/m)` with `m ~ loglog t` and the per-block schedule `k r ~ log t/log N_r`, and the
resulting numeric comparison against `log t/loglog t`.

## Head/tail split built — Z3 skeleton complete (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletHeadTailSplit.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `norm_dirichletTerm` : on the line `Re s = 1`, `‖n^(-1-It)‖ = 1/n`.
- `norm_dirichlet_head_le` : `‖sum_{Ico 1 A} n^(-1-It)‖ <= 1 + log(A-1)`, via
  `HarmonicLogBound.sum_Icc_one_div_le_one_add_log`.
- `norm_dirichlet_partial_le` : the whole partial sum,

  ```text
  ‖sum_{Ico 1 (A*2^R)} n^(-1-It)‖
      <= (1 + log(A-1)) + sum_{r<R} 2560 * (A*2^r)^(-1/(3*2^(k r))),
  ```

  under the per-block schedule hypotheses of `dirichlet_tail_dyadic_le`.

The Z3 skeleton is now complete: head, blocks, schedule, and assembly are all Lean theorems and the
chain composes. What is left is purely the *choice* of parameters and the numeric comparison:

1. take `A = t^(1/m)` with `m ~ loglog t` and `R` so that `A*2^R ~ t`;
2. take `k r ~ log t/log(A*2^r) + 4/3` and verify the three hypotheses
   (`2 <= k r`, `(k r - 1)! <= A*2^r`, and the two-sided `t` window) from that choice;
3. bound `sum_{r<R} 2560*(A*2^r)^(-1/(3*2^(k r)))` and the head `1 + log(A-1) = 1 + log t/m`
   against `C * log t/loglog t`.

Step 3's head term is already `log t/loglog t` on the nose; the content is that the tail sum stays
`O(log t/loglog t)` rather than `O(log t)`.

## Trivial competitor and per-block choice (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockTrivialBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

The derivative-test saving beats the trivial harmonic bound only on part of the range, so the
assembly must choose per block. Added:

- `norm_dirichlet_block_trivial_le` : `2 <= N <= M` gives
  `‖sum_{Ico N M} n^(-1-It)‖ <= log(M-1) - log(N-1)`, via
  `HarmonicDyadicBlock.sum_Icc_one_div_le_log_sub`. On a dyadic block this is close to `log 2`.
- `dirichlet_tail_dyadic_of_blockBound` — **the primitive the assembly should use**: supply any
  family `b : ℕ → ℝ` of per-block bounds and the tail is bounded by `sum_{r<R} b r`. Each block is
  discharged independently, by the saving bound or the trivial bound, whichever is available there.
  `dirichlet_tail_dyadic_le` is the special case where the saving is used on every block.
- `dirichlet_tail_dyadic_trivial_le` — the all-trivial specialisation.
- `norm_dirichlet_block_min_le` — where both apply, the block obeys their minimum.

This is the piece that makes the parameter choice possible: on blocks with `N` too small for the
schedule the trivial bound is used, and the saving is only claimed where it is actually available.
The count of blocks on which the saving is claimed is what produces the `loglog t` gain.

## Two-regime shape (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTwoRegimeBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `norm_dirichlet_partial_of_blockBound` : a single harmonic term for everything below `C`, plus one
  supplied bound per dyadic block above it:

  ```text
  ‖sum_{Ico 1 (C*2^R)} n^(-1-It)‖ <= (1 + log(C-1)) + sum_{r<R} b r.
  ```

- `norm_dirichlet_partial_two_regime` : the same with the split point written as `A*2^S`, blocks
  indexed by `Ico S R`:

  ```text
  ‖sum_{Ico 1 (A*2^R)} n^(-1-It)‖ <= (1 + log(A*2^S - 1)) + sum_{r in Ico S R} b r.
  ```

Note what happened to the low blocks: they need no telescoping. Applying the harmonic bound *once*
to the whole range below the split point already collapses head plus low blocks into the single term
`1 + log(A*2^S - 1)`. The `log(A-1)` of the head cancels against the lower endpoint of the trivial
tail, which is why the earlier per-block trivial route was unnecessary work for this purpose (it
remains the right tool when a block-by-block comparison is wanted).

The Littlewood estimate is now exactly: choose the split point `A*2^S ~ exp(log t/m)`, supply
`b r` from `dirichlet_block_saving_of_small_factorial` on the blocks above it, and show

```text
1 + log t/m + sum_{r in Ico S R} b r  <=  C * log t / loglog t.
```

## Depth criterion and the final shape (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletUniformTailBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `block_saving_le_of_log_ge` : for `N >= 1` and `eps > 0`,

  ```text
  3 * 2^k * log(2560/eps) <= log N   ==>   2560 * N^(-1/(3*2^k)) <= eps.
  ```

  This is the exact conversion of "the block is deep enough for its order" into "the block
  contributes at most eps". Proof is `N^(-a) = exp(-a log N) <= exp(-log(2560/eps)) = eps/2560`.

- `norm_dirichlet_partial_two_regime_uniform` : with a common `eps` on every block above the split
  point,

  ```text
  ‖sum_{Ico 1 (A*2^R)} n^(-1-It)‖ <= (1 + log(A*2^S - 1)) + (R - S) * eps.
  ```

This is the final Littlewood shape. Reading off the parameters: with the split point
`A*2^S ~ exp(log t/m)`, `R ~ log_2 t`, and `eps ~ 1/m`, the right-hand side is
`1 + log t/m + (log_2 t)/m ~ C * log t/m`, which at `m ~ loglog t` is `C * log t/loglog t`.

The depth criterion also pins the range where the saving is claimable: it needs
`2^k <= log N/(3*log(2560/eps))`, and with `k ~ log t/log N` that is `log N >~ log t/log_2 log t`.
Below that the harmonic term covers the range — which is precisely why the split point sits at
`exp(log t/m)` with `m ~ loglog t`.

Everything in the chain is now a Lean theorem except the arithmetic verification of that parameter
choice.

## Z3 packaged as one theorem (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLittlewoodShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_partial_littlewood_shape` states the whole chain once. Hypotheses, all per dyadic
block `r` in `[S, R)` with `N_r = A*2^r`:

1. `2 <= k r`
2. `(k r - 1)! <= N_r`
3. `8*pi*N_r^(1/3) <= t`
4. `t <= 2*pi*2^(k r)*N_r^(k r - 1)*N_r^(-1/3)`
5. `3*2^(k r)*log(2560/eps) <= log N_r`

Conclusion:

```text
‖sum_{Ico 1 (A*2^R)} n^(-1-It)‖ <= (1 + log(A*2^S - 1)) + (R - S)*eps.
```

Nothing else about `t`, the orders, or the split point enters. (1)-(4) are the schedule conditions
of the k-th derivative test at the classical scale; (5) is the depth criterion.

**Z3 is structurally complete.** The remaining work is one arithmetic verification: exhibit
`A`, `S`, `R`, `k : ℕ → ℕ`, `eps` as functions of `t` satisfying (1)-(5), with
`A*2^S ~ exp(log t/m)`, `R ~ log_2 t`, `k r ~ log t/log N_r + 4/3`, `eps ~ 1/m`, `m ~ loglog t`,
and conclude `<= C*log t/loglog t`. Then Z4 (PNTPlus truncation of `zeta(1+it)` against the partial
sum) and Z5 (the rectangle `sigma`-version, which reuses `abel_block_bound` with `w n = n^(-sigma)`).

## Endpoint reduction of the hypotheses (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletEndpointReduction.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_partial_littlewood_endpoints` — with an **antitone** order schedule
(`k r <= k S` on `[S,R)`), four of the five hypotheses collapse to endpoint checks:

| hypothesis | binds at | reduced form |
|---|---|---|
| `(k r - 1)! <= N_r` | bottom block | `(k S - 1)! <= A*2^S` |
| `8*pi*N_r^(1/3) <= t` | top block | `8*pi*(A*2^(R-1))^(1/3) <= t` |
| `3*2^(k r)*log(2560/eps) <= log N_r` | bottom block | at `r = S` |
| `t <= 2*pi*2^(k r)*N_r^(k r -1)*N_r^(-1/3)` | — | stays per-block |

The mechanism is that raising the block raises `N_r` and lowers `k r`, so the two directions of
monotonicity line up. Only the upper `t`-bound genuinely varies: it is exactly what the order at
each block is chosen to satisfy. `eps <= 2560` is needed so that `log(2560/eps) >= 0` and the
`2^(k r) <= 2^(k S)` comparison points the right way.

## Consistency check of the parameter regime (paper, not yet formal)

Writing `L = log N`, `T = log t`, the hypotheses read

```text
(3)  L <= 3(T - log 8pi)
(4)  T <= log 2pi + k*log 2 + (k - 4/3)*L      i.e.  k >~ T/L + 4/3
(5)  2^k <= L/(3*log(2560/eps))
```

Substituting (4) into (5) with `L = T/m` and `eps = 1/m` gives
`2^m * m * log(2560 m) <~ T/(3*2^(4/3))`, i.e. `m ~ log_2 T = log_2 log t`. The final bound is then
`1 + T/m + (log_2 t)/m ~ C*log t/log_2 log t` — Littlewood, and the regime is consistent. So the
packaged theorem is not vacuous; the remaining work is to realise this regime with explicit
naturals.

## A constant order suffices — all five hypotheses become endpoint checks (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletConstantOrder.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`schedule_upper_bound_mono` : for `K >= 2` and `1 <= N <= N'`,

```text
2*pi*2^K*N^(K-1)*N^(-1/3) <= 2*pi*2^K*N'^(K-1)*N'^(-1/3),
```

because the right-hand side is `2*pi*2^K*N^(K-4/3)` and the exponent `K - 4/3` is positive once
`K >= 2`. So the upper `t`-bound, the one hypothesis the endpoint reduction could not collapse, is
**also** monotone in the base point: satisfying it at the bottom block satisfies it everywhere above.

Consequence, `norm_dirichlet_partial_littlewood_const`: a **constant** order schedule `k r = K`
(trivially antitone) reduces all five hypotheses to endpoint conditions —

```text
2 <= K
(K-1)! <= A*2^S                                              (bottom)
t <= 2*pi*2^K*(A*2^S)^(K-1)*(A*2^S)^(-1/3)                   (bottom)
3*2^K*log(2560/eps) <= log(A*2^S)                            (bottom)
8*pi*(A*2^(R-1))^(1/3) <= t                                  (top)
```

with the same conclusion. No block-dependent order is needed at all.

This is a genuine simplification of the remaining work: the earlier plan carried a per-block
schedule `k r ~ log t/log N_r + 4/3` and a monotonicity argument for it. In fact the classical
per-block optimisation is unnecessary for the Littlewood *exponent* — the constant `K ~ m + 2`
already gives it, since the regime check (previous entry) only ever used the bottom block. The
remaining task is now four numeric inequalities in `A, S, R, K, eps` as functions of `t`.

## Power-of-two split: no logarithm of a composite natural remains (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletPowerTwoShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_partial_littlewood_pow_two` — the constant-order shape at `A = 2`, so every block
base is a power of two and both logarithms collapse to multiples of `log 2`:

```text
2 <= K,   S < R,   0 < eps <= 2560,
(K-1)! <= 2^(S+1),
t <= 2*pi*2^K*(2^(S+1))^(K-1)*(2^(S+1))^(-1/3),
3*2^K*log(2560/eps) <= (S+1)*log 2,
8*pi*(2^R)^(1/3) <= t
  ==>  ‖sum_{n < 2^(R+1)} n^(-1-It)‖ <= 1 + (S+1)*log 2 + (R-S)*eps.
```

The harmonic head is now literally `(S+1)*log 2` and the depth criterion is read against the same
quantity, so the remaining verification is arithmetic in the four integers `S`, `R`, `K` and the
real `eps` — no `Real.log` of a composite natural survives anywhere in the hypotheses or the
conclusion.

Regime, for reference: `R ~ 3*log_2 t` (from the top condition), `S+1 ~ (log_2 t)/m`,
`K ~ m + 2`, `eps ~ 1/m`, with `m ~ log_2 log_2 t` forced by
`3*2^K*log(2560 m) <= (S+1)*log 2`. The conclusion is then
`1 + (log_2 t)(log 2)/m + 3(log_2 t)/m = O(log t/loglog t)`.

## Exponent form: the two t-bounds are a sandwich between powers of two (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExponentShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_partial_littlewood_exponent`:

```text
2 <= K,  S < R,  0 < eps <= 2560,
(K-1)! <= 2^(S+1),
8*pi*2^(R/3) <= t <= 2*pi*2^((S+1)(K-1) - (S+1)/3)*2^K,
3*2^K*log(2560/eps) <= (S+1)*log 2
  ==>  ‖sum_{n < 2^(R+1)} n^(-1-It)‖ <= 1 + (S+1)*log 2 + (R-S)*eps.
```

Both bounds on `t` are now explicit powers of two, so the sandwich is consistent exactly when

```text
2 <= K + (S+1)(K-1) - (S+1)/3 - R/3,
```

the arithmetic compatibility between split point, top of range and order. The only transcendental
constants remaining anywhere in the statement are `pi` and `log 2`.

Chain from the derivative test to here (all built, all in the `RHTower` umbrella):
`KthDerivativeTest` -> `LogPhaseBlock`/`DirichletBlockAbel` -> `DirichletBlockSaving` ->
`DirichletBlockSchedule` -> `DirichletDyadicTailAssembly` -> `DirichletHeadTailSplit` ->
`DirichletTwoRegimeBound` -> `DirichletUniformTailBound` -> `DirichletLittlewoodShape` ->
`DirichletEndpointReduction` -> `DirichletConstantOrder` -> `DirichletPowerTwoShape` ->
`DirichletExponentShape`.

## Consistency and non-vacuity of the exponent form (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExponentConsistency.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `exponent_sandwich_nonempty` : the sandwich `8*pi*2^(R/3) <= t <= 2*pi*2^(...)*2^K` is compatible
  **exactly** when

  ```text
  2 + R/3 <= K + (S+1)(K-1) - (S+1)/3,
  ```

  because both sides are `2*pi` times a power of two and the inequality is the comparison of the
  exponents.
- `exists_t_in_exponent_sandwich` : under that condition the lower endpoint itself is an admissible
  `t`.
- `exists_littlewood_exponent_instance` : **non-vacuity** — `S = 1`, `R = 2`, `K = 3`, `eps = 2560`
  satisfy every hypothesis of the exponent form for an explicit `t`, with no numeric estimate of
  `pi` needed anywhere (the compatibility check is `2 + 2/3 <= 3 + 4 - 2/3`, and the depth criterion
  is `24*log 1 = 0 <= 2*log 2`).

So the fourteen-module chain terminates in a statement that is satisfiable, not merely well-typed.
The witness is deliberately weak (`eps = 2560` gives a trivial bound); its purpose is only to
certify that the five hypotheses are simultaneously realisable. The Littlewood regime is the
opposite end of the same constraint set: `eps ~ 1/m` small, which forces `S+1 ~ (log_2 t)/m` and
`m ~ log_2 log_2 t`.

## Choosing the split point (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSplitPointChoice.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

The upper `t`-bound reads `t <= 2*pi*2^(sigma*(K-4/3) + K)` with `sigma = S+1`, so the least
admissible `sigma` is the ceiling of the balance point

```text
x = (log(t/2pi) - K*log 2) / ((K - 4/3)*log 2).
```

- `splitExponent t K := ceil x` (`Nat.ceil`).
- `le_two_pow_splitExponent` : that choice satisfies `t <= 2*pi*2^(sigma*(K-4/3) + K)`.
- `splitExponent_arg_nonneg` : `x >= 0` as soon as `2*pi*2^K <= t` (and `K >= 2`).
- `splitExponent_le` : `sigma <= x + 1`.

The two together are what the estimate needs from the split point: the upper `t`-bound holds, and
the harmonic head `sigma*log 2` exceeds `x*log 2` by less than `log 2`. Since

```text
x*log 2 = (log(t/2pi) - K*log 2)/(K - 4/3),
```

for `K` of size `m` the head is `log t/m` up to bounded terms — which is exactly where the `loglog`
saving enters the final estimate.

## Choosing the top of the range (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTopExponentChoice.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

The lower `t`-bound is `8*pi*2^(R/3) <= t`, so the largest admissible `R` is the floor of
`3*log(t/(8*pi))/log 2`.

- `topExponent t := floor (3*log(t/(8*pi))/log 2)`.
- `topExponent_arg_nonneg`, `topExponent_le` : `R <= 3*log(t/(8*pi))/log 2` for `t >= 8*pi`.
- `topExponent_bound` : that choice satisfies `8*pi*2^(R/3) <= t`.

Both exponents of the estimate are now fixed as explicit functions of `t` and the order `K`:

```text
sigma = S+1 = ceil( (log(t/2pi) - K*log 2) / ((K - 4/3)*log 2) ),
R     = floor( 3*log(t/(8*pi)) / log 2 ).
```

and the conclusion of the exponent form becomes

```text
1 + sigma*log 2 + (R - S)*eps
  <= 1 + [ (log(t/2pi) - K*log 2)/(K - 4/3) + log 2 ] + [ 3*log(t/(8*pi))/log 2 ]*eps.
```

With `K ~ m` and `eps ~ 1/m` both bracketed terms are `O(log t/m)`, so the whole bound is
`O(log t/m)`; the depth criterion forces `m ~ log_2 log_2 t`. Only `eps` and `K` remain to be tied
to `t`.

## Assembled bound: everything but K and eps is now a function of t (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletAssembledBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_partial_littlewood_assembled` — with `sigma = splitExponent t K`,
`R = topExponent t`, `S = sigma - 1`:

```text
8*pi <= t,  2 <= K,  2*pi*2^K <= t,  0 < eps <= 2560,
1 <= sigma,  sigma - 1 < R,
(K-1)! <= 2^sigma,
3*2^K*log(2560/eps) <= sigma*log 2
  ==>  ‖sum_{n < 2^(R+1)} n^(-1-It)‖
         <= 1 + [ (log(t/2pi) - K*log 2)/((K - 4/3)*log 2) + 1 ]*log 2
              + [ 3*log(t/(8*pi))/log 2 ]*eps.
```

Both exponents are now the canonical choices in terms of `t` and `K`; the only free parameters left
are the order `K` and the target `eps`, and the only remaining hypotheses are the factorial bound
and the depth criterion, both of which are inequalities in `K`, `eps` and `sigma`.

Reading the right-hand side: the head is `log(t/2pi)/(K - 4/3) + O(1)` and the tail is
`3*log(t/8pi)*eps/log 2`. Choosing `eps ~ 1/K` makes both `O(log t/K)`, and the depth criterion
`3*2^K*log(2560 K) <= sigma*log 2 ~ log t/K` caps `K` at `~ log_2 log t`. That is Littlewood, and
every step of it is now a Lean theorem except the final choice of `K` and `eps` as functions of `t`.

## Canonical target: only the order K remains free (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTargetEps.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

The depth criterion `3*2^K*log(2560/eps) <= sigma*log 2` is a *lower* bound on `eps`, so the best
admissible target is the one turning it into an equality:

```text
targetEps sigma K := 2560 * exp( - sigma*log 2 / (3*2^K) ).
```

- `targetEps_pos`, `targetEps_le` : `0 < targetEps <= 2560`.
- `targetEps_deep` : `3*2^K*log(2560/targetEps) = sigma*log 2` — an **equality**, so the depth
  criterion is met exactly, with nothing wasted.
- `norm_dirichlet_partial_littlewood_canonical` : the assembled bound at that target,

  ```text
  ‖sum_{n < 2^(R+1)} n^(-1-It)‖
    <= 1 + [ (log(t/2pi) - K*log 2)/((K - 4/3)*log 2) + 1 ]*log 2
         + [ 3*log(t/(8*pi))/log 2 ] * targetEps (splitExponent t K) K.
  ```

Every parameter except the order `K` is now a function of `t`. The remaining hypotheses are the
three structural ones (`1 <= sigma`, `sigma - 1 < R`, `(K-1)! <= 2^sigma`) plus the two size
conditions on `t`.

Reading the tail term: `3*log(t/8pi)/log 2 * 2560 * exp(-sigma*log 2/(3*2^K))` with
`sigma ~ log t/(K*log 2)`, i.e. exponent `~ -log t/(3*K*2^K)`. For the tail to be `O(log t/K)` one
needs `exp(-log t/(3*K*2^K)) = O(1/K)`, i.e. `log t/(3*K*2^K) >= log K`, i.e.
`2^K*K*log K <~ log t/3` — the same cap `K ~ log_2 log t` the earlier regime analysis produced,
now visible directly in the formula.

## Two of the three structural hypotheses discharged (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletStructuralHypotheses.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `one_le_splitExponent` : `K >= 2` and `2*pi*2^K < t` give `1 <= sigma`. (The ceiling of a
  positive real is at least one; positivity of the balance point is exactly `t > 2*pi*2^K`.)
- `splitExponent_sub_one_lt_topExponent` : `K >= 2`, `16*pi <= t`, `2*pi*2^K <= t`, `1 <= sigma`
  give `sigma - 1 < R`.

The second is where the two exponent choices are compared, and the comparison is sharper than it
looks. The balance point is *decreasing* in `K` (numerator falls, denominator rises), so it is
largest at `K = 2`, where it equals `3(L - 2 log 2)/(2 log 2)` with `L = log(t/2pi)`. The top of the
range exceeds `3*log(t/8pi)/log 2 - 1`, and `log(t/8pi) = L - 2 log 2`, so the whole comparison
reduces to

```text
(3/2)(L - 2 log 2) + log 2 <= 3(L - 2 log 2)   <==>   L >= (8/3) log 2   <==>   t >= 2*pi*2^(8/3),
```

and `16*pi` suffices since `2^(8/3) < 8`. No numeric estimate of `pi` is needed anywhere.

Remaining structural hypothesis: the factorial bound `(K-1)! <= 2^sigma`. With `sigma ~ log t/(K log 2)`
and `K ~ log_2 log t` this is `(log_2 log t)! <= t^(1/K)`, comfortable but not yet formal.

## The factorial hypothesis discharged — all three structural hypotheses now follow from t (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletFactorialHypothesis.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`factorial_le_two_pow_splitExponent` : for `K >= 2`,

```text
(K-1)*(K - 4/3)*log(K-1) + K*log 2 <= log(t/2pi)   ==>   (K-1)! <= 2^sigma.
```

Mechanism: `sigma >= x` (ceiling), `(K-1)! <= (K-1)^(K-1) = exp((K-1)*log(K-1))`, and the condition
says exactly that `(K-1)*log(K-1) <= x*log 2`.

All three structural hypotheses of the assembled bound are now consequences of explicit largeness
conditions on `t`:

| hypothesis | sufficient condition |
|---|---|
| `1 <= sigma` | `2*pi*2^K < t` |
| `sigma - 1 < R` | `16*pi <= t` (plus `2*pi*2^K <= t`) |
| `(K-1)! <= 2^sigma` | `(K-1)(K-4/3)log(K-1) + K*log 2 <= log(t/2pi)` |

The third dominates the first (it implies `K*log 2 <= log(t/2pi)`, i.e. `2*pi*2^K <= t`), so the
whole set reduces to `16*pi <= t` together with

```text
(K-1)(K-4/3)log(K-1) + K*log 2 < log(t/2pi).
```

In the intended regime `K ~ log_2 log t` the left side is `~ (loglog t)^2 * logloglog t`, far below
`log t`. What remains for Z3 is only to pick `K` as a function of `t` satisfying that single
inequality together with the depth cap, and to read off `O(log t/loglog t)`.

## Capstone: two conditions on (t, K) give the estimate outright (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLittlewoodCapstone.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_partial_littlewood_capstone` :

```text
16*pi <= t,   2 <= K,   (K-1)(K-4/3)log(K-1) + K*log 2 < log(t/2pi)
  ==>  ‖sum_{n < 2^(topExponent t + 1)} n^(-1-It)‖
         <= 1 + [ (log(t/2pi) - K*log 2)/((K - 4/3)*log 2) + 1 ]*log 2
              + [ 3*log(t/(8*pi))/log 2 ] * targetEps (splitExponent t K) K.
```

`two_pow_lt_of_factorial_cond` is the small lemma that makes the collapse work: for `K >= 2` all
three factors of `(K-1)(K-4/3)log(K-1)` are nonnegative, so the largeness condition implies
`K*log 2 < log(t/2pi)`, i.e. `2*pi*2^K < t`, which is what the split-exponent positivity and the
endpoint comparison both need.

Every hypothesis of the whole chain — fourteen modules from the k-th derivative test down — is now
one of two explicit conditions on `t` and `K`. The Z3 programme reduces to a single remaining
question: choose `K = K(t)` satisfying

```text
(K-1)(K-4/3)log(K-1) + K*log 2 < log(t/2pi)        (largeness)
2^K * K * log K <~ log t / 3                        (depth cap, for the tail to be O(log t/K))
```

and read off the right-hand side as `O(log t/loglog t)`. Both are satisfied by `K ~ log_2 log t`.

## Closed-form right-hand side (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExplicitRHS.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`targetEps_splitExponent_le` bounds the canonical target using only `sigma >= x`:

```text
targetEps (splitExponent t K) K <= 2560 * exp( -(L - K*log 2) / (3*2^K*(K - 4/3)) ),  L = log(t/2pi).
```

`norm_dirichlet_partial_littlewood_explicit` then gives, under `16*pi <= t`, `K >= 2` and the single
largeness condition:

```text
‖sum_{n < 2^(topExponent t + 1)} n^(-1-It)‖
  <= 1 + log 2 + L/(K - 4/3)
     + [3*log(t/(8*pi))/log 2] * 2560 * exp( -(L - K*log 2) / (3*2^K*(K - 4/3)) ).
```

**No auxiliary definition survives on the right** — `splitExponent` and `targetEps` are both gone;
only `topExponent` remains, and only inside the summation range. The two competing terms are now
manifest:

- head `L/(K - 4/3)` — decreasing in `K`;
- tail `~ (3L/log 2) * 2560 * exp(-L/(3*2^K*K))` — increasing in `K`.

Balancing them is the whole remaining content: the head is `O(L/K)`, and the tail is `O(L/K)` as
soon as `exp(-L/(3*2^K*K)) <= 1/(2560*3*K/log 2)`, i.e. `L >= 3*2^K*K*log(7680*K/log 2)`, which for
`K ~ log_2 log t` reads `log t >~ (loglog t)^2 * logloglog t` — true with room.

## The two terms balanced — Littlewood shape reached (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTailDominated.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `tail_le_head` : for `K >= 2`, `0 <= L`, `M <= L`, and

  ```text
  log(7680*(K - 4/3)/log 2) <= (L - K*log 2)/(3*2^K*(K - 4/3)),
  ```

  the tail `3*M/log 2 * 2560 * exp(-(L - K*log 2)/(3*2^K*(K - 4/3)))` is at most `L/(K - 4/3)`.

- `norm_dirichlet_partial_littlewood_balanced` : consequently, under `16*pi <= t`, `K >= 2`, the
  largeness condition and that balance condition,

  ```text
  ‖sum_{n < 2^(topExponent t + 1)} n^(-1-It)‖  <=  1 + log 2 + 2*log(t/2pi)/(K - 4/3).
  ```

This is the Littlewood shape. The right-hand side is `O(log t / K)` with an explicit constant `2`,
and the two hypotheses on `(t, K)` are

```text
(K-1)(K-4/3)log(K-1) + K*log 2 < log(t/2pi)                  (largeness)
3*2^K*(K-4/3)*log(7680*(K-4/3)/log 2) <= log(t/2pi) - K*log 2  (balance)
```

both of which hold for `K ~ log_2 log t`, since their left-hand sides are then
`~ (loglog t)^2 * logloglog t` while the right is `~ log t`.

The structural half of the Littlewood programme is complete: every step from the k-th derivative
test to an `O(log t/K)` bound on the partial sum is an unconditional Lean theorem. What remains is
the arithmetic of choosing `K = K(t)` to satisfy those two inequalities simultaneously and reading
`K ~ log_2 log t`, then Z4 (PNTPlus truncation of `zeta(1+it)` against the partial sum) and Z5 (the
rectangle `sigma`-version).

## Threshold form: an arbitrarily small constant for each order (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletThreshold.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

Both conditions on `(t, K)` say "a quantity depending on `K` alone is below `log(t/2pi)`", so for
each fixed order there is an explicit threshold past which both hold:

```text
largenessBound K := (K-1)(K-4/3)log(K-1) + K*log 2
balanceBound  K := 3*2^K*(K-4/3)*log(7680*(K-4/3)/log 2) + K*log 2

littlewood_threshold (K) (hK : 2 <= K) :
  forall t, max (16*pi) (2*pi*exp(max (largenessBound K) (balanceBound K) + 1)) <= t ->
    ‖sum_{n < 2^(topExponent t + 1)} n^(-1-It)‖
      <= 1 + log 2 + 2*log(t/2pi)/(K - 4/3).
```

The constant `2/(K - 4/3)` is arbitrarily small as `K` grows, so the family of fixed-order bounds
already gives the qualitative statement that the partial sum is `o(log t)` — with **no** construction
of `K` as a function of `t`. That construction is needed only for the quantitative Littlewood
exponent `O(log t/loglog t)`, where `K` must be allowed to grow with `t` at the rate the two
thresholds permit.

This is the natural stopping point for the structural work: the chain from the k-th derivative test
now terminates in a clean, self-contained, unconditional statement with an explicit threshold.

## The partial sum is o(log t) — qualitative half of Littlewood, unconditional (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLittleOh.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `orderForAccuracy eps := max 2 (ceil (4/3 + 2/eps))`, with `orderForAccuracy_spec` :
  `2/(orderForAccuracy eps - 4/3) <= eps`.
- `littlewood_littleOh (heps : 0 < eps)` :

  ```text
  exists T, forall t >= T,
    ‖sum_{n < 2^(topExponent t + 1)} n^(-1-It)‖ <= 1 + log 2 + eps*log(t/2pi).
  ```

Choosing the order from the target accuracy rather than from `t` is what makes this work: `K` is
fixed once `eps` is chosen, and the threshold is the explicit
`max(16pi, 2pi*exp(max(largenessBound K, balanceBound K) + 1))`.

**This is the qualitative half of Littlewood's estimate, unconditional and formal.** The
quantitative exponent `O(log t/loglog t)` still needs the order to grow with `t`; that is the only
remaining gap in Z3, and it is now cleanly isolated as an optimisation over `K` rather than
entangled with the structure.

Chain summary (27 modules, all built, all in the `RHTower` umbrella, all axioms
`[propext, Classical.choice, Quot.sound]`):
`PhaseCorrelation` -> `KthDerivativeTest` -> `LogPhaseBlock`/`DirichletBlockAbel` ->
`DirichletBlockSaving` -> `DirichletBlockSchedule` -> `DirichletDyadicTailAssembly` ->
`DirichletHeadTailSplit` -> `DirichletTwoRegimeBound` -> `DirichletUniformTailBound` ->
`DirichletLittlewoodShape` -> `DirichletEndpointReduction` -> `DirichletConstantOrder` ->
`DirichletPowerTwoShape` -> `DirichletExponentShape` -> `DirichletExponentConsistency` ->
`DirichletSplitPointChoice` -> `DirichletTopExponentChoice` -> `DirichletAssembledBound` ->
`DirichletTargetEps` -> `DirichletStructuralHypotheses` -> `DirichletFactorialHypothesis` ->
`DirichletLittlewoodCapstone` -> `DirichletExplicitRHS` -> `DirichletTailDominated` ->
`DirichletThreshold` -> `DirichletLittleOh`
(plus `DirichletBlockTrivialBound` side branch and `HTGeometry/RatioBoundedWindowLanding`).

## Z4 opened: truncation that keeps the partial sum intact (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/ZetaPartialSumTruncation.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

**Asset audit correction.** The card's Z4 line said truncation would come from `PNTPlus`'s
`Zeta0EqZeta`/`riemannZeta0_apply`. In fact the corpus already owns the truncated formula:
`Sieve/ZetaTruncated.riemannZeta_eq_sum_add_tail` gives, for `re w > 0`, `w != 1`, `N >= 1`,

```text
zeta(w) = sum_{k <= N} k^(-w) + N^(1-w)/(w-1) - w * int_N^inf fract(x) x^(-w-1) dx.
```

What was missing is that the existing bound `norm_riemannZeta_le_truncated` immediately applies
`norm_sum_le` to the head, replacing the complex sum by the sum of moduli — **which discards all
cancellation and can only ever give the trivial logarithmic size**. The whole point of the Z3 chain
is a bound on the oscillating sum, so the head must survive as a complex sum.

Added:

- `norm_riemannZeta_le_partialSum` : the same identity bounded one step earlier —

  ```text
  ‖zeta(w)‖ <= ‖sum_{k <= N} k^(-w)‖ + N^(1-re w)/‖w-1‖ + ‖w‖*(N^(-re w)/re w).
  ```

- `norm_riemannZeta_one_add_I_mul_le` : on the line, for `t > 0` and `N >= 1`,

  ```text
  ‖zeta(1+It)‖ <= ‖sum_{k <= N} k^(-(1+It))‖ + 1/t + ‖1+It‖/N.
  ```

The two tail terms are harmless at the Z3 truncation point: with `N = 2^(topExponent t + 1) - 1`,
`N ~ 2*(t/8pi)^3`, so `‖1+It‖/N ~ t/N ~ 0` and `1/t -> 0`. `Finset.Icc 1 N = Finset.Ico 1 (N+1)`
matches the Z3 range exactly.

Z4 is therefore reduced to a cast/index reconciliation plus these two vanishing terms.

## Z4 index/cast bridge (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/ZetaLineIndexBridge.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `sum_Icc_cpow_eq_sum_Ico` : the truncation's head and the derivative test's range are the same
  sum,

  ```text
  sum_{k in Icc 1 M} ((k:R):C)^(-(1+It)) = sum_{n in Ico 1 (M+1)} (n:C)^(-1-It).
  ```

  (`Finset.Ico_add_one_right_eq_Icc` for the range; base cast and exponent rearrangement termwise.)

- `cube_le_two_pow_topExponent` : the chain's truncation point is large,

  ```text
  8*pi <= t  ==>  (t/(8*pi))^3 <= 2^(topExponent t + 1).
  ```

  (`Nat.lt_floor_add_one` on the definition of `topExponent`, then compare exponentials.)

Together these close the two mismatches identified when Z4 was opened. With
`M + 1 = 2^(topExponent t + 1)` the truncation reads

```text
‖zeta(1+It)‖ <= ‖sum_{n in Ico 1 (2^(topExponent t + 1))} n^(-1-It)‖ + 1/t + ‖1+It‖/M,
```

whose head is exactly what `littlewood_littleOh` bounds, and whose last term is at most
`(1+t)/((t/8pi)^3 - 1)`, which tends to 0. The remaining step is to assemble these into a statement
about `zeta(1+It)` itself.

## Z4 closed: a bound on zeta(1+It) itself (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/ZetaLineLittleOh.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

```text
lineTruncation t := 2^(topExponent t + 1) - 1

norm_riemannZeta_line_littleOh (heps : 0 < eps) :
  exists T, forall t >= T,
    ‖zeta(1 + It)‖ <= 1 + log 2 + eps*log(t/2pi) + 1/t + (1+t)/((t/(8pi))^3 - 1).
```

The head is the derivative-test bound transported through the truncation; the two tail terms are
explicit and both tend to 0 (the second because the chain's truncation point grows like the **cube**
of `t` while `‖1+It‖` grows linearly — an enormous margin, not a delicate one).

**This is a bound on `zeta` itself, not on a partial sum**, and it is unconditional. Together with
`cube_sub_one_le_lineTruncation` and the index bridge, the Z3+Z4 chain now runs from the k-th
derivative test to the qualitative statement

```text
zeta(1 + It) = o(log t).
```

Remaining on the card: the quantitative exponent (`K` growing with `t`, giving
`O(log t/loglog t)`), and Z5 (the rectangle `sigma`-version, which reuses `abel_block_bound` with
`w n = n^(-sigma)`). The Landau/3-4-1 pipeline in `PNTPlus/ZetaBounds` then consumes the rectangle
version to produce the zero-free region.

## Z5 opened: the block bound off the line (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSigma.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`dirichlet_block_sigma_bound` : for `sigma >= 0`, `1 <= N <= M`, and any prefix bound `P` on the
pure phase sum,

```text
(forall m in [N,M], ‖sum_{Ico N m} n^(-It)‖ <= P)
  ==>  ‖sum_{Ico N M} n^(-sigma-It)‖ <= P * N^(-sigma).
```

This is the exact analogue of `dirichlet_block_one_bound`, and the proof is the same Abel step with
`w n = n^(-sigma)` in place of `n^(-1)`: the weight is antitone for `sigma >= 0` and nonnegative, so
`abel_block_bound` applies unchanged.

**Nothing in the derivative test changes.** The `k`-th derivative test controls the pure phase sum
`sum n^(-It)`, which is independent of `sigma`; the weight is what carries it off the line. So the
whole Z3 chain is `sigma`-independent up to the final Abel step, and the rectangle version costs
only this substitution plus re-running the assembly with `N^(-sigma)` in place of `N^(-1)`.

Next: the `sigma`-analogue of `dirichlet_block_one_full` (same prefix bound from
`dirichlet_block_bound`, new weight), then the assembly.

## Z5: prefix bound extracted, full sigma block bound (2026-08-06)

Added to `formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSigma.lean` — built, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `phase_prefix_bound` : the derivative-test prefix bound on a dyadic block,

  ```text
  forall m in [N,M], ‖sum_{Ico N m} n^(-It)‖ <= 256*((M-N)*X + (M-N)^(1-4/2^k)*Y)
  ```

  with `X = (4^k lam)^(1/(2^k-2))`, `Y = lam^(-2/2^k)`, `lam = (t/2pi)(k-1)!/(2N)^k`.

  `dirichlet_block_one_full` establishes exactly this inside its own proof, where it is not reusable.
  Stating it separately lets one derivative-test input serve any weight; the `sigma = 1` case can be
  refactored onto it later.

- `dirichlet_block_sigma_full` : the full block bound off the line — same bracket, with `N^(-sigma)`
  in place of `N^(-1)`. Proof is one line: `dirichlet_block_sigma_bound` applied to
  `phase_prefix_bound`.

This confirms the structural claim from the previous entry: **the derivative-test half of the chain
is entirely `sigma`-independent.** The rectangle version differs from the line version only in the
weight of the final Abel step.

Remaining for Z5: re-run the assembly (saving, schedule, dyadic tail, head/tail split) with
`N^(-sigma)` in place of `N^(-1)`. Each step is the same argument; the only change is that the
harmonic head becomes `sum n^(-sigma)` and the block savings acquire the factor `N^(-sigma)`.

## Z5: the sigma-dependence is a single factor (2026-08-06)

`dirichlet_block_sigma_normalized` added to `Sieve/DirichletBlockSigma.lean` — built, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

```text
‖sum_{Ico N M} n^(-sigma-It)‖
  <= N^(1-sigma) * ( 512*(4^k lam)^(1/(2^k-2)) + 512*N^(-4/2^k)*lam^(-2/2^k) )
```

The bracket is **exactly** the right-hand side of `dirichlet_block_one_normalized`. So:

> the entire `sigma`-dependence of the block estimate is the single prefactor `N^(1-sigma)`.

Consequently `block_saving_wide` applies to the bracket verbatim, giving, in the balanced window,

```text
‖sum_{Ico N M} n^(-sigma-It)‖ <= 2560 * N^(1-sigma) * N^(-1/(3*2^k)).
```

For `sigma` slightly below 1 — the regime the Landau/3-4-1 pipeline needs — `N^(1-sigma)` is
`exp((1-sigma) log N)`, which stays bounded as long as `1-sigma <= c/log N`. That is precisely the
shape of a zero-free region: the rectangle version costs nothing until `sigma` recedes from 1 by
more than `1/log N`, and the width at which it starts to cost is what the region's `c/log^kappa`
will be.

Remaining for Z5: re-run the schedule/tail/head assembly carrying the factor `N^(1-sigma)`, with the
harmonic head replaced by `sum n^(-sigma)`.

## Z5: per-block saving off the line, at the classical scale (2026-08-06)

Added to `Sieve/DirichletBlockSigma.lean` — built, axioms `[propext, Classical.choice, Quot.sound]`,
zero warnings.

- `dirichlet_block_sigma_saving` : in the balanced window,

  ```text
  ‖sum_{Ico N M} n^(-sigma-It)‖ <= 2560 * N^(1-sigma) * N^(-1/(3*2^k)).
  ```

- `dirichlet_block_sigma_saving_of_small_factorial` : the same at the classical scale, with the
  order supplied by the schedule —

  ```text
  8*pi*N^(1/3) <= t <= 2*pi*2^(k0)*N^(k0-1)*N^(-1/3),  (k0-1)! <= N,  k0 >= 2,  N <= M <= 2N+1
    ==>  ‖sum_{Ico N M} n^(-sigma-It)‖ <= 2560 * N^(1-sigma) * N^(-1/(3*2^(k0))).
  ```

**The schedule is reused verbatim.** `exists_blockLambda_in_window`, `blockLambda_two_ge` and
`blockLambda_le_of_small_factorial` all concern `lam` alone, which does not involve `sigma`; the
order-choosing half of the chain needed no `sigma`-analogue at all. Only the two Abel-weighted
statements did.

So the `sigma` version of the chain up to the per-block estimate is complete, and it cost two
theorems (`dirichlet_block_sigma_bound`, `dirichlet_block_sigma_normalized`) plus two one-line
corollaries — against twelve modules for the line case.

## Z5: dyadic tail off the line, and a generic assembly (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaTail.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `norm_sum_Ico_dyadic_of_blockBound` : for an **arbitrary** summand `f : ℕ → E` in a normed group,

  ```text
  (forall r < R, ‖sum_{Ico (A*2^r) (A*2^(r+1))} f‖ <= b r)
    ==>  ‖sum_{Ico A (A*2^R)} f‖ <= sum_{r<R} b r.
  ```

  The dyadic assembly never inspects the summand — it is just the triangle inequality across the
  blocks of `sum_Ico_dyadic`. Stating it generically serves both the line and the rectangle;
  `dirichlet_tail_dyadic_of_blockBound` is now visibly the `n^(-1-It)` instance of it.

- `dirichlet_tail_sigma_dyadic_le` : the tail off the line,

  ```text
  ‖sum_{Ico A (A*2^R)} n^(-sigma-It)‖
    <= sum_{r<R} 2560 * (A*2^r)^(1-sigma) * (A*2^r)^(-1/(3*2^(k r))).
  ```

Running total for the `sigma` version: **three theorems and three corollaries**, reusing the
schedule and now the dyadic assembly unchanged. The pattern is consistent — everything in the chain
that concerns the *phase* is `sigma`-free, and only the weight-carrying statements needed analogues.

## Z5: head off the line — the flagged obstacle was already corpus-owned (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaHead.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

The previous entry flagged the harmonic head as the one place Z5 would cost real work, since
`ZetaTruncated.sum_rpow_neg_le_harmonic` needs `sigma >= 1`. **That was wrong** — the same file
already contains the integral-comparison bound below the abscissa:

```text
sum_rpow_neg_le_of_lt_one (0 < sigma) (sigma < 1) (2 <= N) :
  sum_{Icc 1 N} k^(-sigma) <= 1 + (N^(1-sigma) - 1)/(1-sigma) + N^(-sigma).
```

So the head cost only the modulus computation. Added:

- `norm_dirichletSigmaTerm` : `‖n^(-sigma-It)‖ = n^(-sigma)`.
- `norm_dirichlet_sigma_head_le` : `‖sum_{Icc 1 B} n^(-sigma-It)‖ <= 1 + (B^(1-sigma)-1)/(1-sigma) + B^(-sigma)`.
- `norm_dirichlet_sigma_partial_of_blockBound` : head plus generic dyadic tail, the `sigma`-analogue
  of `norm_dirichlet_partial_of_blockBound`.

Lesson repeated: grep before declaring an obstacle. `ZetaTruncated.lean` carries both the
`sigma >= 1` and `sigma < 1` partial-sum bounds; only the first was in the memory notes.

The `sigma` chain now matches the line chain through the head/tail split, at a total cost of six
theorems and four corollaries.

## Z5: depth off the line — the width appears (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaUniform.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

- `block_sigma_saving_le_of_log_ge` : for `N >= 1`, `eps > 0`,

  ```text
  log(2560/eps) <= (1/(3*2^k) - (1-sigma)) * log N
    ==>  2560 * N^(1-sigma) * N^(-1/(3*2^k)) <= eps.
  ```

- `norm_dirichlet_sigma_partial_uniform` : head plus `R * eps`, the `sigma`-analogue of
  `norm_dirichlet_partial_two_regime_uniform`.

**This is where the zero-free region's width becomes visible.** The bracket
`1/(3*2^k) - (1-sigma)` is positive exactly when

```text
1 - sigma < 1/(3*2^k),
```

so the rectangle estimate survives off the line only within that distance of `Re s = 1`. The saving
exponent `1/(3*2^k)` of the derivative test — the same quantity that produced the `loglog` gain on
the line — is precisely what limits how far left the rectangle may reach. The region's width and the
line's saving are one number, not two.

That also says plainly what the region tier will be: with `2^k ~ log t` the width is `~ 1/(3 log t)`
(de la Vallee Poussin shape), and improving it to Littlewood's `loglog t / log t` requires `2^k` to
be held near `log t / loglog t` rather than `log t` — which is exactly the tension the two
threshold conditions on `(t, K)` encode.

## Z5 structural chain complete: the rectangle shape (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_sigma_littlewood_shape` — the `sigma`-analogue of
`norm_dirichlet_partial_littlewood_shape`. For `0 < sigma < 1`, `t > 0`, `3 <= C`, `K >= 2`,
`eps > 0`, with per dyadic block `r < R` at `N_r = C*2^r`:

```text
(K-1)! <= N_r
8*pi*N_r^(1/3) <= t
t <= 2*pi*2^K*N_r^(K-1)*N_r^(-1/3)
log(2560/eps) <= (1/(3*2^K) - (1-sigma)) * log N_r
  ==>  ‖sum_{n < C*2^R} n^(-sigma-It)‖
         <= (1 + ((C-1)^(1-sigma) - 1)/(1-sigma) + (C-1)^(-sigma)) + R*eps.
```

The first three hypotheses are identical to the line case (they concern only `lam`, which has no
`sigma`); the fourth is the depth criterion carrying the width term `1 - sigma`.

**The Z5 structural chain is complete.** From the k-th derivative test to a rectangle bound, off the
line, the cost was eight theorems and five corollaries — against roughly twenty-five modules for the
line case — because everything about the *phase* is `sigma`-free and only the Abel weighting, the
head, and the depth criterion needed analogues.

What remains for the zero-free region: choose the parameters as functions of `(t, sigma)` — the
analogue of the `splitExponent`/`topExponent`/`targetEps` layer — and feed the result to the
Landau/3-4-1 pipeline in the vendored `PNTPlus/ZetaBounds`, which converts a growth bound on a
rectangle left of `Re s = 1` into the region itself.

## Z5: endpoint reduction off the line (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaEndpoints.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_sigma_littlewood_endpoints` — with a constant order, all four per-block hypotheses
of the rectangle shape become endpoint checks:

| hypothesis | binds at | reduced form |
|---|---|---|
| `(K-1)! <= N_r` | bottom | `(K-1)! <= C` |
| `t <= 2*pi*2^K*N_r^(K-1)*N_r^(-1/3)` | bottom | at `N = C` |
| depth | bottom | at `N = C` |
| `8*pi*N_r^(1/3) <= t` | top | at `N = C*2^(R-1)` |

reusing `schedule_upper_bound_mono` from the line case verbatim for the third row.

The depth criterion is monotone **only when its bracket is nonnegative**, i.e.

```text
1 - sigma <= 1/(3*2^K),
```

which appears here as an explicit hypothesis `hwidth`. That is not bookkeeping: it is the width of
the strip on which the estimate holds at all, and it now sits in the statement rather than being
implicit in the arithmetic.

The Z5 chain now mirrors the line chain through the endpoint reduction. What is left before the
region: the constant-order/power-of-two/exponent-form layer off the line (which should again be
mechanical, since those steps only rearrange the same inequalities), the parameter choices as
functions of `(t, sigma)`, and then the Landau/3-4-1 pipeline.

## Z5: a strip of uniform validity (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaStrip.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings.

`norm_dirichlet_sigma_littlewood_strip` — the depth criterion's bracket
`1/(3*2^K) - (1-sigma)` degenerates as `sigma` approaches `1 - 1/(3*2^K)`. Halving the allowance
decouples the two: on the strip

```text
1 - 1/(6*2^K) <= sigma < 1,
```

the bracket is at least `1/(6*2^K)`, so a **single depth check, free of `sigma`**, serves every
`sigma` in the strip:

```text
log(2560/eps) <= (1/(6*2^K)) * log C
```

replaces the `sigma`-dependent condition, and the rectangle bound holds uniformly across the strip.

**This is the form a zero-free region argument consumes**: a growth bound valid uniformly on a
rectangle left of `Re s = 1`, whose width `1/(6*2^K)` is a fixed function of the order. The
Landau/3-4-1 pipeline in `PNTPlus/ZetaBounds` takes exactly such a rectangle bound and returns the
region.

Z5's structural work is now finished. The remaining steps are parameter selection (`C`, `R`, `K`,
`eps` as functions of `t`) and the pipeline hand-off — no new mathematics, only the same
optimisation already isolated on the line.

## Z6: parameter selection off the line (2026-08-06)

The strip bound `norm_dirichlet_sigma_littlewood_strip` still carried four free parameters
(`C`, `R`, `K`, `eps`). Three of them are now fixed by `t` exactly as on the line, and the fourth by
the depth check itself.

**The target.** `RHTower/Sieve/DirichletSigmaTarget.lean`. The uniform depth check
`log (2560/eps) <= (1/(6*2^K)) * log C` is a lower bound on `eps`, so the best admissible value
makes it an equality:

```
stripTargetEps C K := 2560 * exp (- log C / (6 * 2^K)).
```

`stripTargetEps_deep` is that equality; `norm_dirichlet_sigma_littlewood_canonical` is the strip
bound at it. This is the exact analogue of `targetEps` on the line — same shape, `log C` in place of
`S * log 2` and `6` in place of `3`, the halving that bought the uniform strip.

**The head.** `RHTower/Sieve/DirichletSigmaHeadSimplify.lean`. The head
`1 + ((C-1)^(1-sigma) - 1)/(1-sigma) + (C-1)^(-sigma)` has a middle term that degenerates to
`log (C-1)` as `sigma -> 1`, which is invisible to any crude bound. The elementary inequality

```
rpow_sub_one_div_le :  (x^a - 1)/a  <=  x^a * log x       (x >= 1, a > 0)
```

— the difference quotient of `a |-> x^a` at `0` is below its derivative at `a`, proved from
`exp u - 1 <= u exp u` — collapses the whole head to `2 + C^(1-sigma) * log C`. At `sigma = 1` this
is `2 + log C`, the head on the line, so nothing was lost off it.

**The exponents.** `RHTower/Sieve/DirichletSigmaAssembled.lean`. Setting `C = 2^S` with
`S = splitExponent t K` and running the range to `2^(T+1)` with `T = topExponent t` (so
`R = T + 1 - S`), the two `t`-bounds of the rectangle shape become *literally* the two the line case
already solves:

- `8*pi*(C*2^(R-1))^(1/3) <= t` is `8*pi*(2^T)^(1/3) <= t`, i.e. `topExponent_bound`;
- `t <= 2*pi*2^K*C^(K-1)*C^(-1/3)` is `t <= 2*pi*2^(S(K-4/3)+K)`, i.e. `le_two_pow_splitExponent`.

No new choice of split point or top exponent is needed off the line: the derivative-test half is
sigma-independent, and the sigma-dependence sits entirely in the head and the depth bracket, both of
which the strip condition already absorbs. `norm_dirichlet_sigma_littlewood_assembled` is the result.

**The trade-off.** Writing `stripTheta t K := S/(6*2^K)`, the assembled bound reads

```
||sum_{n < 2^(T+1)} n^(-sigma-it)||  <=  2 + 2^theta * S * log 2  +  R * 2560 * 2^(-theta),
```

`norm_dirichlet_sigma_littlewood_theta`. One exponent controls both terms with opposite signs:
raising the split point widens the head linearly-times-`2^theta` and shrinks every block's
contribution by `2^(-theta)`. This is the whole optimisation, and it is the same optimisation as on
the line — the line is `theta` with `sigma = 1`, where the head term `2^theta` is absent.

All nine declarations audit to `[propext, Classical.choice, Quot.sound]`.

**What is left.** Only the quantitative choice `K = K(t)`. The two thresholds are unchanged from the
line (`largenessBound`, `balanceBound` in `DirichletThreshold.lean`), and `K ~ log_2 log t` is what
turns the bound into `O(log t / log log t)`; on the strip that same `K` fixes the width
`1 - sigma <= 1/(6*2^K) ~ 1/log t`, which is the classical zero-free region width. The rectangle
bound then hands off to `PNTPlus/ZetaBounds`' Landau / 3-4-1 pipeline.

## Z7: the order as a function of `t` (2026-08-06)

`RHTower/Sieve/DirichletOrderChoice.lean`. Until now the order `K` was chosen from the target
accuracy, so `littlewood_littleOh` produced a *family* of bounds. The order can instead be read off
`t` itself:

```
orderThreshold K   := max (largenessBound K) (balanceBound K) + 1
littlewoodOrder t  := Nat.findGreatest (fun K => orderThreshold K <= log (t/2pi)) (ceil (log (t/2pi)))
```

The search bound is legitimate, and that is the only nontrivial point. `Nat.findGreatest` needs a
cap, and the cap must not truncate the optimum. It does not, because **an order never exceeds its
own threshold**:

- `one_le_balance_log` — the logarithm inside `balanceBound` is `>= 1` for `K >= 2`
  (`7680(K-4/3)/log 2 >= 5120 > e`, using `log 2 <= 1` and `Real.exp_one_lt_d9`);
- `two_mul_two_pow_le_balanceBound` — hence `balanceBound K >= 3*2^K*(2/3)*1 = 2*2^K`;
- `cast_le_orderThreshold` — with `K < 2^K`, therefore `K <= orderThreshold K`.

So every admissible order satisfies `K <= log(t/2pi) <= ceil(log(t/2pi))`, and the capped search
finds the true greatest one.

Consequences, all unconditional:

- `orderThreshold_littlewoodOrder_le` — the chosen order is admissible;
- `two_le_littlewoodOrder` — it is at least `2` once `t` clears the order-2 threshold
  (`orderThreshold 2 >= 9`, `nine_le_orderThreshold_two`);
- `norm_dirichlet_partial_littlewood_order` — the estimate at the chosen order:
  `||sum|| <= 1 + log 2 + 2 log(t/2pi)/(littlewoodOrder t - 4/3)`;
- `littlewood_littleOh_explicit_order` — one function of `t` realises **every** accuracy, because a
  fixed order is eventually admissible and `littlewoodOrder t` is at least as large.

**Lean note.** `Nat.findGreatest_spec` will not unify `P (findGreatest P n)` against a goal stated
through a definition wrapping `findGreatest`; supply `(P := ...)` explicitly. `Nat.le_findGreatest`
unifies fine because the predicate is fixed by the supplied `P m` argument.

**Next: the rate.** `Nat.findGreatest_is_greatest` gives `log(t/2pi) < orderThreshold (K+1)`. With
the crude envelope `orderThreshold M <= 35 M^2 2^M` and the already-proved `2^K <= log(t/2pi)`
(so `K <= log_2 log(t/2pi)`), this inverts to

```
K  >  log_2 L  -  log_2 (70 (log_2 L + 1)^2),      L = log(t/2pi),
```

i.e. `K = log_2 log t - O(log log log t)`, and the estimate becomes `O(log t / log log t)` — the
Littlewood exponent. The same `K(t)` fixes the strip width `1 - sigma <= 1/(6*2^K) ~ 1/log t` of
Z5/Z6, which is the classical zero-free region width.

## Z8: the Littlewood exponent, proved (2026-08-06)

`RHTower/Sieve/DirichletOrderRate.lean`. `littlewoodOrder t` is the *greatest* admissible order, so
the next one already fails:

```
log_lt_orderThreshold_succ :  log (t/2pi)  <  orderThreshold (littlewoodOrder t + 1).
```

(`Nat.findGreatest_is_greatest`, with the cap check `K + 1 <= ceil (log (t/2pi))` supplied by
`K + 1 <= 2^K < log (t/2pi)` — the same "an order is below `2^` of itself" fact that made the search
legitimate in Z7.)

To read a lower bound on `K` off that failure one needs an upper envelope for `orderThreshold`:

```
orderThreshold_le_envelope :  orderThreshold M  <=  34561 * M^2 * 2^M       (M >= 2).
```

Both halves come from `log x <= x - 1` alone: `log (M-1) <= M` gives
`largenessBound M <= M^3 + M <= M^2 2^M + M`; and `log 2 > 2/3` (`Real.log_two_gt_d9`) gives
`7680(M-4/3)/log 2 <= 11520 M`, hence `balanceBound M <= 34560 M^2 2^M + M`. No numerical evaluation
of any logarithm is used.

Applying the envelope at `M = K+1` and absorbing the square with `K + 1 <= 2^K`:

```
log_lt_two_pow_three_mul :  log (t/2pi)  <  69122 * 2^(3 * littlewoodOrder t),
```

so, with `orderLowerBound L := log (L/69122) / (3 log 2)`,

```
orderLowerBound_lt :  orderLowerBound (log (t/2pi))  <  littlewoodOrder t.
```

The order is `log_2 log t` up to a factor `3` and an additive constant. Substituting:

```
norm_dirichlet_partial_littlewood_rate :
  ||sum_{n < 2^(topExponent t + 1)} n^(-1-it)||
     <=  1 + log 2  +  2 log(t/2pi) / (orderLowerBound (log (t/2pi)) - 4/3)
```

for `t >= 16 pi` clearing the order-2 threshold and with `orderLowerBound (log(t/2pi)) > 4/3`. The
error term is `6 log 2 * L / log L * (1 + o(1))` with `L = log(t/2pi)` — **Littlewood's
`O(log t / log log t)`**, unconditional, `[propext, Classical.choice, Quot.sound]`.

The factor `3` (and the constant `69122`) are artefacts of absorbing `(K+1)^2 <= (2^K)^2`; the sharp
form would keep `(K+1)^2` and invert `L < 70(K+1)^2 2^K` by bootstrapping on `K <= log_2 L`. That
changes the constant, not the exponent, so it is deliberately not done here.

### Status of the programme

| step | state |
|---|---|
| Z1-Z3 derivative test, dyadic assembly, line `Re s = 1` | done |
| Z4 `zeta(1+it)` itself | done |
| Z5-Z6 rectangle `Re s = sigma`, uniform strip, parameters | done |
| Z7 order chosen from `t` | done |
| Z8 Littlewood exponent `O(log t / log log t)` | **done** |
| Z9 the same `K(t)` on the strip; hand-off to `PNTPlus/ZetaBounds` (Landau, 3-4-1) | open |

Z9 is the only remaining step. It needs the sigma-analogues of `DirichletTailDominated` /
`norm_dirichlet_partial_littlewood_balanced` so that `hS2`, `hSR`, `hfac` of
`norm_dirichlet_sigma_littlewood_assembled` can be discharged at `K = littlewoodOrder t`, after
which the strip width `1 - sigma <= 1/(6*2^K)` is `~ 1/log t` and the rectangle bound is exactly the
input the Landau / 3-4-1 pipeline consumes.

## Z9: the rectangle at the order chosen from `t` (2026-08-06)

`RHTower/Sieve/DirichletSigmaCapstone.lean`. The three structural hypotheses of
`norm_dirichlet_sigma_littlewood_theta` are discharged from the *same* largeness condition the line
case uses, because `splitExponent` and `topExponent` are the same functions of `t` off the line:

- `two_le_splitExponent` — off the line the split point must be at least `2`, not `1`. For `K >= 3`
  the largeness condition gives it: `(K-1) log(K-1) > log 2` (since `K-1 >= 2` and
  `log(K-1) >= log 2`), so `(K-1)(K-4/3)log(K-1) > (K-4/3) log 2`, which is exactly `1 < x` for the
  balance point `x`, hence `ceil x >= 2`.
- `splitExponent_le_topExponent` — `omega` from the line case's `S - 1 < T` together with `1 <= S`.
- the factorial bound — `factorial_le_two_pow_splitExponent`, unchanged.

Hence

```
norm_dirichlet_sigma_littlewood_capstone :
  0 < sigma < 1,  16 pi <= t,  3 <= K,  1 - sigma <= 1/(6*2^K),
  (K-1)(K-4/3) log(K-1) + K log 2  <  log (t/2pi)
  ==>  ||sum_{n < 2^(T+1)} n^(-sigma-it)||
         <= 2 + 2^theta * S * log 2 + R * 2560 * 2^(-theta)
```

and, at `K = littlewoodOrder t` (`orderThreshold_littlewoodOrder_le_of` generalises the Z7 lemma to
any admissible witness order, here `3`):

```
norm_dirichlet_sigma_littlewood_order :
  0 < sigma < 1,  16 pi <= t,  orderThreshold 3 <= log (t/2pi),
  1 - sigma <= 1/(6 * 2^(littlewoodOrder t))
  ==>  the same bound with K = littlewoodOrder t.
```

Since `2^(littlewoodOrder t) <= log(t/2pi)` (Z7) and `log(t/2pi) < 69122 * 2^(3 littlewoodOrder t)`
(Z8), the strip width `1/(6*2^(littlewoodOrder t))` is between `1/(6 log(t/2pi))` and
`(69122/log(t/2pi))^(1/3)/6` — i.e. **`≍ 1/log t` from above**: the width of the classical zero-free
region.

Size of the right-hand side on the strip: `theta = S/(6*2^K) -> 0`, so `2^(±theta) -> 1`; the head is
`~ S log 2 ~ L/K` and the tail is `R * stripTargetEps`, whose exponent is *half* the line's, giving
`O(L/sqrt K)`. Both are `o(log t)`; in particular the estimate is `O(log t)` uniformly on the
rectangle, which is precisely what the Landau / 3-4-1 argument consumes.

All declarations `[propext, Classical.choice, Quot.sound]`.

**Remaining:** the hand-off itself — feed `norm_dirichlet_sigma_littlewood_order` (plus the tail of
`riemannZeta` from `ZetaPartialSumTruncation`, exactly as Z4 did on the line) into
`PNTPlus/ZetaBounds`' Landau / 3-4-1 pipeline. No new analysis; only interface matching against
read-only vendored code.
