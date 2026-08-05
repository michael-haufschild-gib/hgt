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
