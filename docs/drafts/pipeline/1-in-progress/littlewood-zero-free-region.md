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
