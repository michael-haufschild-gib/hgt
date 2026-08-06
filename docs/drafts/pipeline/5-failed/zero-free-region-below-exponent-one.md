# RETIRED: the van der Corput family cannot reach exponent below one

**Outcome.** The goal — a zero-free region `σ ≥ 1 − c/(log t)^κ` with `κ < 1` — is **not reachable**
from the corpus's toolkit.  The obstruction is proved, not merely suspected:

- the per-block saving of the `k`-th derivative test is `N^{−1/(3·2^k)}`, doubly exponentially weak
  in the order, while the height window forces `k ≥ log t/log N`.  Both hold together only for
  `log N ≳ log t/loglog t`, so every smaller block saves nothing at any order.  The `≍ log t/loglog t`
  blocks below that contribute `O(1)` each — exactly the Littlewood bound, as a **ceiling**;
- the Landau/DLVP frame turns any bound `|ζ| ≪ t^{θ(1−σ)}` into width `≍ 1/(θ log t)`, independent
  of the radius, so κ = 1 exactly — even under Lindelöf.

Only a growth bound with exponent **sub-linear in `(1−σ)`** breaks it, and that is
Vinogradov–Korobov, i.e. Vinogradov's mean value theorem — in neither the corpus nor mathlib.

Kept for the inventory table below and the reusable lemmas; read before re-attempting.
See `mem:route_e/van_der_corput_capped_at_loglog_2026_08_06` and
`mem:route_e/landau_route_is_pinned_at_kappa_one_2026_08_06`.

---

# Breaking κ = 1: a zero-free region of exponent below one

**Status:** in progress.  Goal `σ ≥ 1 − c/(log t)^κ` with **κ < 1**, which is what
`zero-free-region-exponent-is-the-mr-wall` says unlocks the Matomäki–Radziwiłł corridor and hence
`MRBilinear → 0` for the Route E sign-class consumers.

## Two corrections to the standing record

The memories were badly out of date.  Before planning anything here, note:

1. **Van der Corput's `k`-th derivative test is already formalised**, for every `k ≥ 2`:
   - `RHTower.Sieve.kth_derivative_test` (`RHTower/Sieve/KthDerivativeTest.lean`)
   - `RHTower.Sieve.dirichlet_block_bound` (`RHTower/Sieve/LogPhaseBlock.lean`), the same applied
     to `n^{-it} = e(g_t(n))` on a dyadic block, with `λ = (t/2π)(k−1)!/(2N)^k`.

   Neighbours: `SecondDerivativeTest`, `WeylDifferencing`, `KuzminLandau`, `KuzminLandauInterval`,
   `ExpSumBernstein`, `LargeSieveExpSum`, `DirichletBlockAbel`.  **Do not rebuild any of it, and do
   not import van der Corput from mathlib or from the literature.**

2. **The Landau/DLVP frame is already the right one.**  `landau_logDeriv`
   (`RHTower/Sieve/LandauLemma.lean`) takes the radius `R` as a parameter, and `dlvp_inequality`
   turns it into a region.

## The obstruction, and the exact escape

Landau at radius `R` about `1+it` gives error `O(log M(R)/R)`, `M(R) = max_{|z−(1+it)|≤R}|ζ(z)|`,
and the region width is `≍ 1/(log M(R)/R)`.

- **Polynomial growth is useless.**  For any `|ζ(σ+it)| ≪ t^{θ(1−σ)}` — convexity `θ=1/2`,
  subconvexity `θ=1/3`, **Lindelöf** `θ=ε` — one gets `log M(R) ≍ θR log t`, so
  `log M(R)/R ≍ θ log t` **independent of `R`**, and width `≍ 1/(θ log t)`: κ = 1 exactly.
  For `R ≲ 1/log t` it is `≳ log t·loglog t`, worse.  Even Lindelöf improves only the constant.
  The corpus's own line bound `norm_riemannZeta_line_rate_clean : ‖ζ(1+it)‖ ≪ log t/loglog t` is
  likewise useless here — it lives on the line, the width depends on a disc.
- **A sub-linear exponent breaks it.**  With `|ζ(σ+it)| ≪ t^{A(1−σ)^{3/2}}·log^{2/3}t`,

  ```text
  log M(R)/R ≍ A·R^{1/2}·log t + loglog t/R,
  minimised at R ≍ (loglog t/log t)^{2/3},
  giving  log M(R)/R ≍ log^{2/3}t·loglog^{1/3}t,
  width  ≍ 1/(log^{2/3}t·loglog^{1/3}t)  —  κ = 2/3.
  ```

  Even the weaker van der Corput/Chudakov outcome κ = 3/4 clears κ < 1.

## What is actually left

Only the passage from the block bound to a growth bound with a **sub-linear exponent in `(1−σ)`**:

1. **Choose `k` per dyadic block**, growing with `N`, instead of the fixed order the Z1–Z9 chain
   uses.  `dirichlet_block_bound` already quantifies over all `k ≥ 2`; the admissibility
   hypothesis is `λ = (t/2π)(k−1)!/(2N)^k ≤ 1`.
2. **Sum the blocks** into `|ζ(σ+it)| ≪ t^{A(1−σ)^{3/2}}·log^{2/3}t` (or any sub-linear exponent).
3. Feed it into the existing `landau_logDeriv` + `dlvp_inequality` at `R ≍ (loglog t/log t)^{2/3}`.

Step 3's arithmetic is settled (above).  **Steps 1–2 are an optimisation over `k`, not a new
analytic theory.**

## First bricks

- **Admissibility.**  `(k−1)! ≤ k^k`, so `λ ≤ (t/2π)·(k/(2N))^k`, and `λ ≤ 1` holds as soon as
  `k·(t/2π)^{1/k} ≤ 2N`.  This is the usable form of `dirichlet_block_bound`'s hypothesis.
- **Block bound in exponent form.**  Rewrite the two terms of `dirichlet_block_bound` as powers of
  `N` and `T = t/2π` with `K = 2^k`, so that the optimisation over `k` is visible.
- Then the per-block choice and the dyadic sum.

## Bricks 1–3 built

`RHTower/Sieve/DirichletBlockAdmissible.lean` (all unconditional):

| theorem | content |
|---|---|
| `factorial_pred_le_pow_self` | `(k−1)! ≤ k^k` |
| `dirichlet_block_lam_le_one` | `T·k^k ≤ (2N)^k ⟹ λ ≤ 1` — the factorial-free admissibility |
| `dirichlet_block_bound_of_pow` | `dirichlet_block_bound` with that hypothesis |
| `block_terms_mono` | the bound is ↑ in `λ` in term 1, ↓ in term 2 |
| `dirichlet_block_bound_powers` | factorial eliminated via `1 ≤ (k−1)! ≤ k^k` |
| `block_first_base_eq`, `block_second_base_eq` | the two base identities |
| `dirichlet_block_bound_clean` | **the usable form** |

```text
‖∑_{j<L} (N+j)^{-it}‖
  ≤ 256·( L·( T·(2k/N)^k )^{1/(2^k−2)} + L^{1−4/2^k}·( (2N)^k/T )^{2/2^k} ),   T = t/2π,
```
for every `k ≥ 2` with `T·k^k ≤ (2N)^k`.

## The optimisation, worked out — execute this, do not re-derive it

Write `M = 2N` (so `L ≤ M`), `K = 2^k`.  Both terms are `≤ M^{1−ρ}` exactly when

```text
term 1:  L·(T·(4k/M)^k)^{1/(K−2)} ≤ M^{1−ρ}   ⟸   T·(4k)^k ≤ M^{k − ρ(K−2)}
term 2:  L^{1−4/K}·(M^k/T)^{2/K}  ≤ M^{1−ρ}   ⟸   M^{k − 2 + ρK/2} ≤ T
```

so the block is `≤ 512·M^{1−ρ}` whenever

```text
M^{k − 2 + ρK/2}  ≤  T  ≤  M^{k − ρ(K−2)} / (4k)^k .
```

The window is non-empty when `ρ ≍ 1/K = 2^{−k}`, and it pins `k ≍ log T/log M`.  The saving `ρ` is
exponentially small in `k` but the range of `N` it covers grows — that is the whole trade, and it
is what produces an exponent **sub-linear in `(1−σ)`** after the dyadic sum.

### Next bricks, in order

1. **The window lemma.**  `k ≥ 2`, `ρ > 0`, `M^{k−2+ρK/2} ≤ T ≤ M^{k−ρ(K−2)}/(4k)^k`
   ⟹ `‖block‖ ≤ 512·M^{1−ρ}`.  Pure rpow arithmetic on `dirichlet_block_bound_clean`; the two
   displayed implications above are the two halves.
2. **The per-block choice.**  Given `N` and `t`, pick `k = k(N,t)` inside the window and read off
   `ρ(N,t) ≍ 2^{−k}`.
3. **The dyadic sum.**  Sum `∑_{n∼N} n^{−σ−it}` over dyadic `N` with the per-block `ρ`, giving
   `|ζ(σ+it)| ≪ t^{A(1−σ)^{3/2}}·log^{2/3}t` (or any sub-linear exponent).
4. **Feed into** `landau_logDeriv` + `dlvp_inequality` at `R ≍ (loglog t/log t)^{2/3}`.

---

# CORRECTION (audit of the existing corpus)

**Most of what is above was already built.**  The plan was written without auditing the
`Dirichlet*` family, and bricks 1–3 duplicate existing theorems.  What follows replaces the
"next bricks" list.

## Canonical, already in the corpus

| module | theorem | content |
|---|---|---|
| `DirichletBlockSchedule` | `blockLambda` | `λ = (t/2π)(k−1)!/(2N)^k`, as a definition |
| | **`exists_blockLambda_in_window`** | **the per-block order choice** — returns `k ∈ [2, k₀]` with `λ` in `[N^{−5/3}, N^{−1/3}]` |
| | `blockLambda_two_ge`, `blockLambda_le_of_small_factorial` | discharge its two hypotheses |
| `DirichletBlockSaving` | `block_saving`, `block_saving_wide` | **the window and the saving**: `4^k λ ≤ N⁻¹`, `N^{−3/2} ≤ λ` ⟹ `≤ 1024·N^{−1/2^k}` |
| | `dirichlet_block_saving_of_range`, `…_of_factorial_range`, `…_of_small_factorial` | with the height window stated in `t` |
| `DirichletBlockSigma` | `dirichlet_block_sigma_saving`, `…_of_small_factorial` | **the same at general σ**: `≤ 2560·N^{1−σ}·N^{−1/(3·2^k)}` |
| `DirichletDyadicTailAssembly` | **`dirichlet_tail_dyadic_le`** | **the dyadic sum, already taking a per-block order `k : ℕ → ℕ`** |
| `DirichletHeadTailSplit`, `DirichletEndpointReduction`, `DirichletConstantOrder`, `DirichletExponentShape`, `DirichletAssembledBound`, `DirichletExplicitRHS`, `DirichletOrderChoice`, `DirichletOrderRate` | | the assembly through to `norm_riemannZeta_line_rate_clean` |

## What this session added, and what of it is redundant

| module | status |
|---|---|
| `DirichletBlockAdmissible` | `block_terms_mono` is general and reusable; `dirichlet_block_lam_le_one` gives a factorial-**free** admissibility condition `T·k^k ≤ (2N)^k`, which the corpus states instead as `(k−1)! ≤ N`.  The `_powers` / `_clean` restatements are a coordinate change of `dirichlet_block_bound`. |
| `DirichletBlockWindow` | **duplicates** `block_saving`, in `T`-coordinates instead of `λ`. |
| `DirichletBlockStandardOrder` | **duplicates** `block_saving` / `block_saving_wide` specialisations. |
| `DirichletOrderExists` | `rpow_le_of_le_log_div`, `le_rpow_of_log_div_le`, `mul_le_rpow_of_log_div_le` are generic and reusable.  `exists_order_in_window` duplicates the combinatorial core of `exists_blockLambda_in_window`. |
| `DirichletBlockOrderChoice` | **duplicates** `exists_blockLambda_in_window`. |

Nothing outside this session's own chain imports any of them.

## THE ACTUAL GAP

`dirichlet_tail_dyadic_le` already accepts a **varying** order `k : ℕ → ℕ`.  Every consumer of it
in the corpus (`DirichletConstantOrder`, `norm_dirichlet_partial_littlewood_const`) instantiates a
**constant** order across all blocks, and `DirichletOrderChoice` / `DirichletOrderRate` then
optimise that one order globally.  **A constant order is exactly what caps the result at
`log t/loglog t`.**

The sub-linear `(1−σ)^{3/2}` exponent needs `k(r)` to grow with the dyadic index `r`.  The plumbing
already permits it; no existing theorem exercises it.

### Remaining work, correctly scoped

1. Choose a growing `k(r)` and verify the four hypotheses of `dirichlet_tail_dyadic_le`:
   `2 ≤ k r`, `(k r − 1)! ≤ A·2^r`, `8π(A2^r)^{1/3} ≤ t`, and the upper height bound.
   The second is the binding one and is what forces `k(r) ≍ log(A2^r)/log log(A2^r)`.
2. Sum `∑_r 2560·(A2^r)^{−1/(3·2^{k r})}` with that growing order — the sum no longer collapses to
   a single power, which is the whole point.
3. Repeat at general σ with `dirichlet_block_sigma_saving`, giving the growth bound with exponent
   sub-linear in `(1−σ)`.
4. Feed into `landau_logDeriv` + `dlvp_inequality` at `R ≍ (loglog t/log t)^{2/3}`.

**Before writing anything: grep the `Dirichlet*` family.**  It is large, and its module names
describe their contents accurately.
