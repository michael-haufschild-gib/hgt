# The marker-scale lifting device: an `o(1)` mean square suffices for the reciprocal-marker Hall law

- **ID:** `ROUTE-E-MARKER-SCALE-LIFT-001`
- **Stage:** 1-in-progress
- **Type:** MECHANISM / UNBLOCKS THREE STAGE-2 CARDS
- **RH used:** no
- **Computation used:** no

## Why this card exists

`1-in-progress/moebius-halasz-log-saving-programme.md` was opened to supply the three route-E marker
cards with a Möbius short-interval mean square of rate `o(1/log x)`. That programme is now **closed
negatively**: §"the exact-Ramaré chain is CLOSED in Lean — and its rate has a hard ceiling" proves
the route caps at `(log x)^{−2(β−κ)}`, and the audit below upgrades that to a statement about *every*
window. This card shows the rate was never needed: a change in the **scale of the marker primes**
makes the three cards follow from the `o(1)` the corpus already owns.

## The negative half, sharpened (2026-08-19)

Matomäki–Radziwiłł's own short note (*A note on the Liouville function in short intervals*,
Lemmas 2 and 5) fixes every constant of the route:

- Lemma 2 needs `exp((log X)^θ) ≤ P` with `θ > 2/3` — **Vinogradov–Korobov's exponent** — for
  `|𝒫(1+it)| ≪ log X/(1+|t|) + (log X)^{−A}` to hold uniformly in `|t| ≤ X`.
- Lemma 5 takes `Q = X^{δ/3}` at window `h = X^δ`, i.e. `Q ≤ h`: the last display needs
  `QT/X ≤ 1` with `T = X/h`.
- The discarded integers are those with no prime factor in `[P,Q]`; MR bound their contribution by
  the mean value theorem, which costs `log P/log Q` **linearly**, giving their `(log X)^{−1/3+ε}`.

The corpus's fibre route replaces the mean value theorem by a *count* of rough integers in the
window, so the same quantity enters **squared**, giving `(log P/log Q)²`. That is the corpus's
improvement, and it is the best the route allows. Since `log P ≥ (log X)^{2/3}` and `log Q ≤ log h ≤
log X`, the rate obeys

```
      rate ≥ ( (log X)^{2/3} / log h )²  ≥  (log X)^{−2/3}   for every h ≤ X.
```

`o(1/log X)` would need `log h ≥ (log X)^{7/6} > log X`. **So no window length whatsoever makes the
Ramaré/zero-free-region route reach `o(1/log X)`**, and with the corpus's Route-T exponent `9/10`
in place of `2/3` the ceiling is `(log X)^{−1/5}`. The card's cited input `(6)` — a transfer error
`(log log L)/(log L)` — is therefore not a consequence of that method.

## The positive half: lift the marker scale

Fix the cofactor scale `x`, put `N = √x`, `h = cardLength β x = exp((log x)^β)` with `99/100 < β < 1`,
`c = √(log x)`, and define the **physical** scale and cell by

```
      Xc = x · log x  (so √Xc = c·N),        Hc = D · N · h · log x  =  D · c² N h,
```

`D` an absolute constant fixed below. Markers are the primes

```
      p ∈ ( c²N , D c²N ] ,        c²N = Xc/N ,
```

i.e. at scale `N log x`, **not** at scale `N`. Cofactors are `a` in the fibre
`(⌈Xc/p⌉−1, ⌊(Xc+Hc)/p⌋]`, whose start is `t_p = ⌈Xc/p⌉−1 ∈ [N/D, N]` and whose length is
`Hc/p ∈ [h, D h]`.

### Why this is the right scale

For a start `t ≍ N`, the primes with that start are the primes of

```
      J_t = ( Xc/(t+1) , Xc/t ] ,      |J_t| = Xc/(t(t+1)) ≍ Xc/N² = log x .
```

At the card's scale (`markers ≍ N`) one has `|J_t| = O(1)`, so only a `1/log x` fraction of starts
carries a marker at all, and an exceptional set of starts of density `ρ` destroys a `ρ·log x`
fraction of the markers — the `o(1/log x)` requirement. At scale `N log x` one has `|J_t| ≍ log x`,
so `π(t) := #{p prime : p ∈ J_t} ≍ 1` on average, **every** start carries markers, and the loss is
only `√ρ`:

```
      #{bad markers}  =  ∑_{t bad} π(t)  ≤  ( #{t bad} )^{1/2} ( ∑_t π(t)² )^{1/2} .
```

The second factor is `O(#starts)` by the Selberg sieve for shifted prime pairs, so with
`#{t bad} = ρ·#starts` and `∑_t π(t) ≍ #starts`,

```
      #{bad markers} / #{markers}  ≪  √ρ .
```

**`ρ = o(1)` therefore suffices**, and `ρ = o(1)` is exactly
`Sieve/MoebiusMeanSquare.averagedMeanSquare_moebius`, unconditional in the corpus.

### The count is unchanged

Every good marker contributes `≥ (3/16)ϱ·(Hc/p)` targets, so the total is

```
      ≥ (3/16) ϱ Hc ∑_{p ∈ (c²N, Dc²N]} 1/p  ≈  (3/16) ϱ Hc (log D)/log(c²N)
                                              =  (3/8) ϱ Hc (log D)/log Xc ,
```

independent of `c`. Brun–Titchmarsh gives `π(Xc+Hc) − π(Xc) ≤ (4+o(1))Hc/log Xc`, so `log D > 18`
— `D = e^{18}` — already makes every cell contain more positive-Möbius targets than source primes.

### Decoding is unchanged

`a ≍ N` and `p ≍ N log x`, so `p > a`, `p ∤ a`, `μ(ap) = μ(a)μ(p)`, and `ap = a'p'` forces `p = p'`
exactly as in the card's `(24)`. No divisor-multiplicity normalisation appears.

### The displacement is unchanged

`Hc/√Xc = D N h log x/(cN) = D h √(log x)`, so `log(Hc/√Xc) = (log x)^β + O(log log x) = o(log Xc)`:
the cell is still `Xc^{1/2+o(1)}` and the Gibbs cost is still `Xc^{1/2+o(1)}`.

## Numbered chain, ready for Lean

Corpus theorems are flagged `[C]`.

1. `[C]` `Sieve/MoebiusMeanSquare.averagedMeanSquare_moebius` : `AveragedMeanSquare μ (cardLength (99/100))`.
2. `[C]` `Sieve/FibreStepOneClosed.eventually_fibre_step_one_closed` and
   `Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing` : outside a set of `a ∈ outerBlock x h`
   of size `1024ε√x/ϱ² + √x/(log x)²`, the fibre carries `≥ (3/16)ϱ·fibreLen` integers of each Möbius sign.
3. **Start realisation.** For `t` with `N/D ≤ t ≤ N − 1` the interval `[x/(t+1), x/t)` has length
   `≥ 1`, hence contains an integer `a` with `⌈x/a⌉ − 1 = t`; and `a ∈ [√x, D√x]`.
   *(Elementary; needs `t(t+1) ≤ x`.)*
4. **Window match.** For that `a`, `⌊(x + h√x)/a⌋ − t` and `⌊(Xc+Hc)/p⌋ − t` differ by `O(D)`
   whenever `⌈Xc/p⌉ − 1 = t`. *(Both equal `h·t/N + O(D)`.)*
5. **Prime-pair second moment.** `∑_{t} π(t)² ≪ D³ · #starts`, from
   `#{p ≤ Y : p + k prime} ≪ 𝔖(k) Y/(log Y)²` and `∑_{k ≤ K} 𝔖(k) ≪ K`.
   *(Corpus: the 2-D Selberg sieve of `Sieve/PrimePair*`, used by `Sieve/DyadicPrimeMeanSquare`.)*
6. **Cauchy–Schwarz transfer.** `∑_{t ∈ B} π(t) ≤ |B|^{1/2}(∑_t π(t)²)^{1/2}`; with `|B| = o(#starts)`
   and 5, the bad markers are `o(#markers)`.
7. `[C]` PNT on the dyadic marker range and `[C]` Brun–Titchmarsh on the cell.
8. **Assembly.** Distinct targets `≥ (3/16)ϱ Hc ∑_{p good} 1/p ≥ (3/8)ϱ (log D − o(1)) Hc/log Xc`,
   all with `μ = σ`, all in `(Xc, Xc+Hc]`, pairwise distinct by decoding.

## What each card needs re-tuned

- `route-e-reciprocal-marker-mobius-hall-law`: replace `(15)` (`2^kN < p ≤ 2^{k+1}N`, `K` fixed) by
  the single range `(c²N, D c²N]`; replace `(18)` (`O_K(1)` fibres) by 5–6; the analytic input drops
  from Menon `(6)` to `[C]` 1. Statement `(1)` becomes `H(X) = √X·exp((log X)^β)` for fixed
  `β ∈ (99/100, 1)`, which contains the constructed `Hc` for large `X`.
- `route-e-growing-reciprocal-marker-low-breadth-transport`: same substitution in its growing-block
  capacity proof; the low-breadth transport half is untouched.
- `route-e-coprime-square-root-mobius-product-sign-law`: its window range `(log log x)^{1+η}` is a
  separate question and is **not** addressed here.

## The device is Lean, unconditionally (2026-08-19)

Three modules, all built, all `[propext, Classical.choice, Quot.sound]`, wired into
`GaloisForLFunctions.RHTower`.

### `Sieve/MarkerScaleTransfer`

```
sq_sum_subset_le_card_mul_sumSq (B ⊆ S) (π) :
  (∑_{i ∈ B} π i)² ≤ #B · ∑_{i ∈ S} (π i)²

exists_start_preimage (1 ≤ t) ((t+1)·t ≤ x) :
  ∃ a, 1 ≤ a ∧ x/(t+1) ≤ a ∧ a < x/t

fibreStartIdx_eq_of_start_interval (1 ≤ t) (1 ≤ a) (x/(t+1) ≤ a) (a < x/t) :
  fibreStartIdx x a = t
```

The last two are chain item 3: above the lifted scale **every** start is realised by an integer
outer factor, so the corpus's fibre statements — which are indexed by the outer factor — apply to
every start a marker can produce.

### `Sieve/FibreMultiplicitySecondMoment`

```
sum_card_lower_eq_sum_card_upper (f) :
  ∑_{p ∈ S} #{q ∈ S | f q = f p ∧ p < q} = ∑_{p ∈ S} #{q ∈ S | f q = f p ∧ q < p}

card_upper_le_card_shifts (f) (K) (separation) (p ∈ S) :
  #{q ∈ S | f q = f p ∧ p < q} ≤ #{d ∈ [1,K] | p + d ∈ S}

sum_sq_fibreCard_le (f) (K) (∀ p q ∈ S, p < q → f q = f p → q ≤ p + K) :
  ∑_{t ∈ image f S} (#{p ∈ S | f p = t})²  ≤  #S + 2 ∑_{d ∈ [1,K]} #{p ∈ S | p + d ∈ S}
```

Chain item 5's combinatorial half, coefficient-free and sieve-free: the second moment of the
per-start multiplicity is the first moment plus twice a shifted-pair count.

### `Sieve/MarkerBadCount` — the device

```
sq_card_marker_bad_le (f) (K) (B ⊆ image f S) (separation)
    (∑_{d ∈ [1,K]} #{p ∈ S | p+d ∈ S} ≤ Pi) :
  ( #{p ∈ S | f p ∈ B} )²  ≤  #B · ( #S + 2·Pi )
```

**This is the whole mechanism.** Take `S` = the marker primes, `f = fibreStartIdx X`, `B` = the
exceptional starts. The trivial estimate would be
`#{bad markers} ≤ #B · (maximal multiplicity)`; the device replaces the maximal multiplicity by the
mean square, giving `#{bad markers} ≤ √(#B · (#S + 2Pi))`. With `#S ≍ #starts` (the lifted scale)
and `Pi ≪ #starts` (the two-dimensional sieve), this is `#S·√(#B/#starts)` — a `√ρ` loss instead of
a `ρ·log x` loss.

Remaining to assemble: instantiate `S` at the marker primes and `Pi` from
`Sieve/PrimePairAverage.sum_card_primePair_le`, then the target count.

### `Sieve/MarkerPrimeSeparation` — the separation hypothesis (2026-08-19)

```
start_interval_of_fibreStartIdx (0 < x) (1 ≤ p) (1 ≤ t) (fibreStartIdx x p = t) :
  x/(t+1) ≤ p  ∧  p < x/t

sub_lt_of_fibreStartIdx_eq … : (q : ℝ) − p < x/(t(t+1))

marker_separation_nat (0 < x) (1 ≤ T₁) (x/(T₁(T₁+1)) ≤ K) (1 ≤ p) (1 ≤ q)
    (T₁ ≤ fibreStartIdx x p) (fibreStartIdx x q = fibreStartIdx x p) :
  q ≤ p + K
```

This is the `hsep` hypothesis of `sum_sq_fibreCard_le` and `sq_card_marker_bad_le`, verified for the
actual fibre start map. Together with `exists_start_preimage` and
`fibreStartIdx_eq_of_start_interval` the combinatorial layer of the device is complete: what remains
is arithmetic — the pair budget from `Sieve/PrimePairAverage.sum_card_primePair_le`, the marker
count from the PNT, and the assembly.

## The Hall layer was already built — only the supply was missing (2026-08-19)

Audit of the card's own Lean programme. **The combinatorial and matching layers are complete:**

| corpus theorem | what it gives |
|---|---|
| `RHTower.markerBlockTargets`, `card_markerBlockTargets` | the target set and `#T = ∑_p #(C p)` — no target produced twice |
| `RHTower.markerBlockTargets_mem_window`, `markerBlockTargets_sign` | every target in `(X, X+H]` and carrying the reversed sign |
| `Sieve/MarkerBlockLower.card_markerBlockTargets_ge` | `#P · c ≤ #T` |
| `Sieve/WindowMatching.exists_hall_injection_primes_of_cells` | **the Hall injection from the source primes of `(X,X+H]` into `markerBlockTargets P C`, for an arbitrary marker set `P` and cofactor family `C`**, given `c ≤ #(C p)` for every `p ∈ P` and the numeric criterion `2H/log Y + Y²·… ≤ #P · c` |
| `Sieve/MarkerCountUpper.exists_hall_injection_full` | the same with Mertens and the marker count substituted, for `C = windowCell` |

So the card's `(19)`–`(26)` are Lean. The single missing input is `hc : ∀ p ∈ P, c ≤ #(C p)` for the
**sign-restricted** cells `C p = {a ∈ windowCell X H p | μ a = σ}` — which needs *every* marker in
`P` to be good, i.e. exactly the supply the device provides.

`RHTower.card_markers_start_mem_le` is the corpus's own supply estimate and is the lossy one: it
discards `#S · (X/(A(A+1)) + 1)` markers, the bad-start count times the *largest* fibre.

### Landed this session

| module | statement |
|---|---|
| `Sieve/MarkerLossDevice` | `reciprocal_separation` (two integers with the same reciprocal start above `A` differ by `≤ X/A²`); **`sq_card_markers_start_mem_le`**: `#{p ∈ M : X/p ∈ S}² ≤ #S·(#M + 2·Pi)` |
| `Sieve/MarkerGoodSupply` | `half_card_le_card_markers_start_notMem` — if `#S·(#M+2Pi) ≤ (#M)²/4` then at least half the markers are good |
| `Sieve/MarkerCellSign` | `Ioc_subset_windowCell`, `card_sign_windowCell_ge` — a good window at the marker's start transfers its sign count to `windowCell X H p` |
| `Sieve/MarkerPairBudget` | `sum_card_shift_bigPrimeSet_le_sieve` — the shifted-pair budget of a marker block from `Sieve/PrimePairAverage.sum_card_primePair_le` |

All built, all `[propext, Classical.choice, Quot.sound]`, all wired, no name collisions.

**Remaining:** the asymptotic fitting — choose `M₀, Q, X, H, x, h` as functions of the scale, take
the bad-start set from `Sieve/FibreStepOneClosed.eventually_fibre_step_one_closed`, check
`#S·(#M+2Pi) ≤ (#M)²/4` and the `hnum` criterion of `exists_hall_injection_primes_of_cells`.

## The last gap, isolated exactly: the window family (2026-08-19)

Full accounting of the card's §2–§4 against the corpus.

**The card's block structure.** Block `k` uses markers `p ∈ (2^kN, 2^{k+1}N]`, whose cells
`windowCell X H p` have length `H/p ≍ h/2^k`, and needs a good cofactor window of that length at the
start `t = ⌊X/p⌋ ≍ N/2^k`. Each block then contributes `#markers · (3ϱ/16)·(h/2^k) ≍ (3ϱ/64)Nh/log N
= (3ϱ/32)H/log X`, the **same for every `k`**, with `H = Nh` fixed. So `K` blocks give
`K·(3ϱ/32)H/log X`, and `K ≥ 70` beats Brun–Titchmarsh's `(4+o(1))H/log X`. That is why the card's
statement `(3)` holds for every constant `C`.

**What the corpus supplies.** `AveragedMeanSquare μ (cardLength β)` is a statement about the *single*
window function `hh = cardLength β`. Its fibres are `innerFibre x (hh x) a` for `a ∈ [√x, 2√x]`, so

```text
      start ≍ √x ,      window = hh(x)·√x/a ∈ [hh(x)/2, hh(x)] .
```

Applying it at the scale `x/4^k` moves the start to `N/2^k` but leaves the window at
`cardLength β (x/4^k) ≍ h` — because `cardLength β` is nearly scale-invariant over these ranges. So
the available (start, window) pairs lie on the one-parameter curve `(√y, cardLength β y)`, on which
`window/start` is strictly decreasing, while the card needs the *line* `window/start = h/N`. **The
curve meets the line in exactly one point.**

**Consequence, computed.** Restricted to that single scale — equivalently, summing over the dyadic
blocks with `start ≥ T₀ := Xh/H` and using only a window of length `h` inside each cell — the total
is `≍ 2·(3ϱ/16)H/log M₀`, and with `log M₀ ≥ (1/2)log X` forced by the decoding constraint `p > a`,
the ratio to the source count `8H/log X` is at most

```text
      2·(3ϱ/16)·(log X/log M₀)/8  ≤  (3ϱ/16)/2  ≈  0.057 .
```

Improving every constant that can be improved — the sign constant `3/16 → 1/2`, Brun–Titchmarsh
`2 → 1`, the device's `1/2 → 1` — reaches at most `≈ 0.6 < 1`. **No arrangement of the corpus's
single-window mean square closes the card.**

**The gap, as a statement.** What is needed, and all that is needed, is

```text
      AveragedMeanSquare μ (fun x => cardLength β x / 2^k)      for k = 0, 1, …, K,   K ≈ 70 .
```

This is **not new mathematics** — it is the corpus's own chain at a window shrunk by a fixed
constant. `Sieve/OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget` is already fully
general in `hh`, and `Sieve/OmegaBudgetMaster.exists_omegaBudget_master` is general in `(x, h, z₀,
z, L, B₀, Q, η, D, w₀, T₀, G, …)`. What must be re-run with `h/2^k` in place of `cardLength β x` is
the parameter substitution and the four quotient limits:

`Sieve/SpectralParameters`, `Sieve/BudgetSubstitution`, `Sieve/RhoLimit`,
`Sieve/SlopeQuotientLimit`, `Sieve/ConstQuotientLimit`, `Sieve/EnergyQuotientLimit`,
`Sieve/NonSpectralBudget`, `Sieve/BudgetLimit` — about 2200 lines, every estimate of which is
insensitive to a bounded factor in the window. Two reparameterisations that would avoid the work do
**not**: `cardLength β x/2^k = cardLength β (ψ_k x)` moves the start by
`exp(−0.35k(log x)^{1−β})`, not by `2^k`; and blocks of ratio `r` shrink the window by
`exp(2β log r·(log x)^{β−1})`, which is below `r` for every `x` past a fixed bound.

## The scaled-window chain, started (2026-08-19)

### `Sieve/ScaledCardLength`

```
scaledLength c β x = c * cardLength β x
scaledLength_one, scaledLength_pos, log_scaledLength, tendsto_scaledLength,
scaledLength_le_sqrt (c ≤ 1), tendsto_rpow_log_div_scaledLength,
tendsto_rpow_log_mul_scaledLength_div_sqrt
```

Every asymptotic property of the window that the spectral chain consumes, transferred to a constant
multiple.

### `Sieve/ScaledBudgetGeometry`

```
budgetBS c β x = ⌊√x + scaledLength c β x⌋₊      gallagherCutS c β x = budgetBS/scaledLength
budgetTS c β x = budgetBS                        budgetNminS c β x = ⌊gallagherCutS⌋₊

exp_quarter_le_sqrt_div_cardLength      : ∀ᶠ x, exp(log x/4) ≤ √x/cardLength β x
sqrt_div_cardLength_le_gallagherCutS    : ∀ᶠ x, √x/cardLength β x ≤ gallagherCutS c β x
one_le_gallagherCutS, gallagherCutS_le_budgetTS, annulusStart_le_gallagherCutS,
tendsto_gallagherCutS, tendsto_budgetNminS, eventually_contourParam_budgetNminS
```

Six of the fifteen side conditions of `Sieve/BudgetSubstitution.exists_eventually_omegaBudget_le`
are now available at the scaled window. The comparison `√x/cardLength β x ≤ gallagherCutS c β x`
does the work: shrinking the window only *raises* the Gallagher cut, so every lower bound the cut
must satisfy is inherited from the unscaled one.

### What the audit of the master theorem shows must also be scaled

`Sieve/OmegaBudgetMaster.exists_omegaBudget_master` is free in `(x, h, z₀, z, L, B₀, Q, η, D, w₀,
T₀, G, Lx, q, μ, xmin, Hmaj, Nmin)`, so most parameters may keep their corpus values. Checking each
hypothesis against `h = scaledLength c β x`:

- **may stay unscaled:** `siftStart`, `ladderEta`, `annulusStart`, `ladderWidth` (only `1 ≤ D` is
  asked of it), `Lx = (log x)^β`, `q`, `μ`, `xmin`, `Hmaj`;
- **must be scaled:** `B₀`, `G`, `T₀`, `Nmin` — done above — **and the ladder top**. The condition
  `∀ j ∈ range L, Nmin ≤ ⌊B₀/(Q(1+η)^j)⌋₊` is the binding one: `Nmin' ≍ √x/(ch)` while
  `B₀'/z ≍ √x/h` if the ladder keeps its unscaled top `z ≍ h`. So `ladderSteps` and `ladderTop`
  must use `scaledLength c β x` in place of `cardLength β x`, after which
  `B₀'/z' ≍ √x/(ch) = G'` and the condition is again borderline-satisfied exactly as in the
  unscaled chain.

Remaining: the scaled `ladderSteps`/`ladderTop` and their `Sieve/SpectralParameters` lemmas, the
scaled `exists_eventually_omegaBudget_le`, and the four quotient limits.

## `Sieve/ScaledBudgetSubstitution` — the budget bound at the scaled window (2026-08-19)

```
budgetMuS, budgetHmajS, budgetRhoS                       (the annulus data at the scaled window)

eventually_cardLength_add_two_le_sqrt_mul_eta (0<β) (β<1) :
  ∀ᶠ x, cardLength β x + 2 ≤ √x · ladderEta β γ x

budgetNmin_le_floor_cofactorS (0<c) (1<x) (ladderEta ≤ 1) (the slack) (0<Q) (ladderPow_le) (j<L) :
  budgetNmin β x ≤ ⌊budgetBS c β x / (Q(1+η)^j)⌋₊

exists_eventually_omegaBudgetS_le (0<c) (c ≤ 1) (0<β) (β<1) (0<γ) (γ<1) (γβ<1) :
  ∃ A delta Ctot, 0 < delta ∧ 0 < Ctot ∧ ∀ᶠ x,
    omegaBudget x (scaledLength c β x) (siftStart (γβ) x) (ladderTop β γ x) ≤ (the explicit bound)
```

**All fifteen side conditions of `Sieve/OmegaBudgetMaster.exists_omegaBudget_master` are now
verified at `h = scaledLength c β x`.** The design that made it short:

- the ladder keeps its corpus value — sifting bottom, step ratio, number of steps, ladder top,
  smoothing width, annulus threshold are all window-free;
- only `B₀`, `G`, `T₀` move, and `Sieve/ScaledBudgetGeometry` supplies their facts from the single
  comparison `√x/cardLength β x ≤ gallagherCutS c β x`;
- **`Nmin` and the disc constant `budgetS` stay unscaled.** The block condition
  `Nmin ≤ ⌊B₀'/(Q(1+η)^j)⌋` then needs `B₀'(1+η) ≥ B₀`, i.e. `cardLength β x + 1 + η ≤ √x·η` — which
  is the new slack lemma, and holds with room because `√x·(log x)^{γβ−β−5/4}` dwarfs
  `exp((log x)^β)`. Keeping `budgetS` unscaled is what will let the four quotient limits transfer
  by monotonicity instead of re-derivation.

### The remaining four limits, and why they are now comparisons

`Sieve/BudgetLimit.tendsto_normalised_omegaBudget` squeezes the normalised budget by
`136·slope + 140·energy + 131·const + nonSpectral`. At the scaled window:

- `B₀' ≤ B₀` and `scaledLength = c·cardLength`, so each denominator loses at most the constant `c`;
- `budgetRhoS ≤ budgetRho`, because `budgetTS = B₀' ≤ B₀ = budgetT` makes
  `routeTWidthPolylogLower` larger, hence `budgetMuS ≥ budgetMu` and `budgetHmajS ≤ budgetHmaj`, and
  `ladderRho` is increasing in `Hmaj` and decreasing in `μ`;
- `ladderAffineSlope`, `ladderAffineConst` and `ladderDefectSum` are increasing in `B₀` and in `ρ`,
  and the disc constant is unchanged.

So each scaled quotient is at most `1/c²` times the corresponding unscaled one, and
`squeeze_zero'` finishes. What is left to write is the three monotonicity lemmas, the four
comparisons, `tendsto_normalised_omegaBudgetS`, and
`AveragedMeanSquare μ (scaledLength c β)` — after which the Hall capstone
`Sieve/HallInjectionLiftedMarkers.exists_hall_injection_lifted_markers` is instantiated.

## The full parameter table, derived (2026-08-19)

The audit below fixes every exponent and constant; nothing is left to tuning.

Write `N = √x`, `h = cardLength β x`, `β ∈ (99/100, 1)`, `Q` a fixed integer `≥ 2`,
`K = ⌈log₂ Q⌉`.

```
      M₀ = N · log x                    (the LIFTED marker scale)
      X  = N · M₀ = x · log x           (the physical scale)
      H  = 2 · h · M₀ = 2 h N log x     (the physical window),   H/√X = 2h√(log x)
      markers        p ∈ ( M₀ , Q·M₀ ]
      marker block k: p ∈ ( 2^k M₀ , 2^{k+1} M₀ ],   k = 0 … K−1
      block-k starts t = X/p ∈ [ N/2^{k+1} , N/2^k ]
      block-k cofactor scale   y_k = x / 4^k        (so √y_k = N/2^k)
      block-k window           h_k = h / 2^k        ( = scaledLength (2^{-k}) β,  up to 1+o(1) )
```

### Why every entry is forced

- `a < p` (the Möbius sign flip) forces `p > a ≍ N`, hence `M₀ ≳ N` and `log X ≥ log x`.
- `t = X/p` must land in the corpus's start range `[√y/2, √y]` of the outer block, forcing
  `√y_k = N/2^k`, i.e. `y_k = x/4^k`.
- `fibreLen ≍ h_k √y_k / a` and `H/p = H t/X` are **both** proportional to `t`, so their ratio is
  `h_k X /(√y_k H)`, constant across a block.  Requiring it to be constant across blocks forces
  `h_k ∝ 2^{-k}`, i.e. `h_k = h/2^k` — the shrunk-window family.
- `|dp/dt| = X/t² = M₀/N`.  At the card's unlifted scale `M₀ = N` this is `1`: a start carries a
  marker only with probability `1/log N`, and the Cauchy–Schwarz device returns
  `#bad markers ≤ √(o(N)·O(N/log N)) = o(N/√log N)` against `#markers ≍ N/log N` — a ratio
  `o(√log N)`, **useless**.  At `M₀ = N log x` one has `|dp/dt| = log x`, so `π(t) ≍ 2`,
  `#markers ≍ N`, and the device returns `√(o(N)·O(N)) = o(N)` — ratio `o(1)`.  **This is the
  whole reason the scale must be lifted, and it fixes `c² = log x` up to a constant.**
- `∑_{M₀ < p ≤ Q M₀} 1/p ≍ log Q / log M₀ = 2 log Q/log x`, so the target count is
  `(3/16)ϱ · H · S ≍ (3/8)ϱ log Q · H/log X`, i.e. `C = (3/8)ϱ log Q`: **unbounded in `Q`**, which
  is what statement (3) of the Hall card demands ("for every fixed `C`").  A *single* dyadic marker
  block gives only `C = (3/8)ϱ log 2 = 0.158 < 2`, below Brun–Titchmarsh; `Q = e^{18}` clears it.

### The remaining Lean chain

`[C]` = already in the tree.

1. `[C]` `Sieve/ScaledBudgetLimit.averagedMeanSquare_moebius_scaledLength` : for every
   `0 < c ≤ 1` and `9/10 < β < 1`, `AveragedMeanSquare μ (scaledLength c β)`.  *(built 2026-08-19)*
2. **Step 1 at a shrunk window.**  Generalize `Sieve/FibreStepOne{Closed,Positive}` from
   `cardLength (99/100)` to `scaledLength c β`: outside `o(√y)` outer factors, the fibre carries
   `(3/16)ϱ·fibreLen` integers of each sign.
3. `[C]` `Sieve/MarkerScaleTransfer.{exists_start_preimage, fibreStartIdx_eq_of_start_interval}` —
   every start in `[√y/2, √y]` is realised by an outer factor of `outerBlock y h`.
4. `[C]` `Sieve/MarkerBadCount.sq_card_marker_bad_le` and
   `Sieve/MarkerGoodSupply.half_card_le_card_markers_start_notMem` — the device.
5. `[C]` `Sieve/MarkerPairBudget.sum_card_shift_bigPrimeSet_le_sieve` — `Pi ≪ #markers`.
6. `[C]` `Sieve/MarkerCellFromGoodOuter.card_windowCell_sign_ge_of_goodOuter` — the fibre count
   becomes the cell count.
7. `[C]` `Sieve/MarkerSignWindowCount.card_sign_window_ge` — the cells, summed harmonically, become
   the sign count of the physical window.  *(built 2026-08-19)*
8. **Assembly**: the block-`k` instantiation, then the sum over `k = 0 … K−1`.

Items 2 and 8 are what remains.

## The whole programme reduces to ONE classical sieve estimate (2026-08-19)

Every hypothesis of the block assembly `Sieve/LiftedMarkerBlock.card_sign_window_ge_block` is
either elementary or already in the tree, **except** the shifted-prime-pair budget `Pi`.  The audit
below shows the reduction is exact: the marker programme closes if and only if

```
   (PP)     ∑_{d ≤ K} #{ n ≤ Y : n and n+d both prime }  ≤  C · K · Y / (log Y)²
```

holds with an absolute `C` for `K ≥ 1` and `Y` large — and it does **not** close with any weaker
saving.

### The device inequality, in invariant form

Write `ρ = #badStart/#starts`, `μ = #markers/#starts`, `ν = (#M + 2Pi)/#M`.  The device
`Sieve/MarkerGoodSupply.half_card_le_card_markers_start_notMem` needs exactly

```
                              ρ · ν  ≤  μ/4 .
```

`ρ` is what step 1 supplies: `ρ ≤ 2(1024ε/ϱ² + (log y)^{-2})`, an arbitrarily small **fixed**
constant.  So the programme closes iff `ν = O(μ)`, and `μ ≍ W/log m` where `W = M₀/m` is the lift.

- With the **true** pair bound (PP), `Pi/#M ≍ K/log M₀ = 4W/log m ≍ μ`, hence `ν ≍ μ` and the
  condition is `ρ ≤ const`. ✔ closes at `W ≍ log m`, window `H/√X = 2L√W = X^{o(1)}·√X`. ✔
- With **Brun–Titchmarsh** for the maximal multiplicity (`r ≤ 2K/log K`), `ν ≍ W/(log K)`, and the
  condition becomes `ρ ≤ (log K)/(32 log m) ≍ (log W)/(32 log m)`.  A *fixed* `ρ` then forces
  `log W ≍ log m`, i.e. a **polynomial** lift `W = m^θ` — and then `H/√X = 2L√W = X^{θ/(2(2+θ))}`,
  so the window is `X^{2/3}` at `θ = 1`.  ✘ the card's window is destroyed.
- With the corpus's present `Sieve/PrimePairAverage.sum_card_primePair_le`, the saving is
  `E² = (log h/log P₁)²` under `h^{2k} ≤ z`, `k ≥ e·∑_{P₁≤p≤h} 2/(p−2) + log 2 ≈ 2e·log log h`.
  Since the remainder forces `log z ≤ (1/2) log Y`, this gives `log h ≤ log Y/(8e log log Y)` and
  hence `Pi ≪ K Y (log log Y)²/(log Y)²`.  The condition becomes `ρ ≲ (log log m)^{-2}`. ✘ by
  exactly `(log log)²`.

Four independent escapes were checked and all fail for the same invariant reason:
increasing `Q` (then `b ∝ log Q` but `#M ∝ Q`), increasing or decreasing the lift `W` (the
`(log log)²` is `W`-independent), restricting markers to a residue class `mod q ≈ K/r` (then
`#M ≍ M₀/(φ(q) log M₀)` and the gain cancels exactly), and taking one marker per start (then the
harmonic mass drops from `log Q/log M₀` to `1/(2W)`, and the two agree only at `W ≍ log M₀`).

### Where the `(log log)²` comes from, and how to remove it

The loss is a **Rankin exponent chosen too small**.  For the Selberg `G(z) = ∑_{d ≤ z, d | P(h)} g(d)`
with `g(p) = 2/(p−2)`, the corpus bounds the tail by `z^{-1/k} ∏_p (1 + p^{1/k} g(p))` with
`k ≥ e·∑ g(p)`, forcing `k ≳ log log h`.  The correct choice is `α = λ/log z`:

```
   ∑_{d > D, d | P(z)} g(d)  ≤  D^{-α} ∏_{p ≤ z}(1 + p^α g(p))
                             ≤  ∏_{p ≤ z}(1 + g(p)) · exp( 2(e^λ − 1)/λ − λ s ) ,
        s = log D / log z ,        α = λ / log z .
```

At `λ = log s` the exponent is `2(s−1)/log s − s log s`, which is `≤ −5` already at `s = 6`.  So a
**bounded** level ratio `s` suffices, `log h ≍ log z ≍ log Y`, and the saving is the full
`(log Y)²`.  The two ingredients to formalize are

1. `∑_{p ≤ z} (p^α − 1)/p ≤ C (z^α − 1)/(α log z)` — a Mertens-type estimate with a rising weight;
2. the Rankin inequality itself, plus `1 + p^α g(p) ≤ (1 + g(p))·exp((p^α − 1) g(p))`.

That is the single open item of the whole marker programme.

### What is already Lean (this session)

- `Sieve/GenericFibreStepOne` — step 1 at an *arbitrary* window (four hypotheses on the window).
- `Sieve/ScaledFibreStepOne` — step 1 at `c·exp((log x)^β)`, unconditional.
- `Sieve/ScaledBadStart` — `goodFibre`, `badOuter`, `badStart`; `#badStart = o(√y)`; and
  every start in `[√y/2, √y−1]` outside `badStart` is realised by a good outer factor.
- `Sieve/StartFibreLength` — `hy·t/√y − 1 ≤ fibreLen ≤ hy(t+1)/√y + 1`.
- `Sieve/GoodMarkerData` — the fibre fits the marker's cell and fills a definite proportion of it.
- `Sieve/MarkerSignWindowCount` — the harmonic sum of the cells is the sign count of the window.
- `Sieve/MarkerBlockSignCount`, `Sieve/LiftedMarkerBlock` — the block assembly, with `Pi` abstract.

## The sieve gap is CLOSED (2026-08-19)

The `(log log)²` loss is gone.  Four new modules replace the prime-factor-count truncation of the
Selberg bounding sum by Rankin's size truncation at the exponent `α = 1/log h`.

### `Sieve/RankinTruncation`

```
sum_powerset_prod_le_ge (∀ p ∈ s, 0 ≤ a p) (∀ p ∈ s, 1 ≤ p) (0 < α) (0 < D)
    (∑_{p ∈ s} (p^α − 1)·a_p + log 2 ≤ α·log D) :
  (1/2)·∏_{p ∈ s}(a_p + 1)  ≤  ∑_{t ⊆ s, ∏_{p ∈ t} p ≤ D} ∏_{p ∈ t} a_p
```

Generic, coefficient-free, and strictly stronger than the corpus's
`Sieve/PowersetTailBound.sum_powerset_card_le_ge`: the level condition is on `log D` rather than on
the number of factors.

### `Sieve/RankinPairCondition`

```
rankin_pairSum_le : ∑_{p ∈ (P₁,h]} (p^{1/log h} − 1)·(pairClassCount d p)/(p − pairClassCount d p)
                      ≤ 6e·(1/log h)·(log h + mertensFirstConst)
rankin_pairSieve_condition (2 ≤ P₁) (2 ≤ h) (20·mertensFirstConst ≤ log h) (d) :
   … + log 2  ≤  (1/log h)·log(h^18)          [ = 18 ]
```

The whole content is `p^{1/log h} ≤ e` across the range, `e^u − 1 ≤ u·e` on `[0,1]`,
`c/(p−c) ≤ 6/p` for `p ≥ 3`, and Mertens' first theorem.  Numerically `6e·1.05 + log 2 = 17.82 < 18`.

### `Sieve/RoughPairSieveSharp`, `Sieve/PrimePairAverageSharp`

```
selbergBoundingSum_roughPairSieve_ge_sharp  (level  h^18 ≤ √z)
selbergBoundingSum_ge_mertens_sharp
card_roughPair_le_sharp
card_primePair_le_sharp
sum_card_primePair_le_sharp
sum_card_shift_bigPrimeSet_le_sieve_sharp
```

all with hypotheses `2 ≤ h`, `P₁ ≤ h`, `h ≤ M₀`, `h^18 ≤ √z`, `20·mertensFirstConst ≤ log h` — and
**no** `k`.  So `h` may be taken as a fixed root of the level: with `z = Y^{1/2}` one may take
`h = Y^{1/72}`, giving

```
      ∑_{d ≤ K} #{p ≤ Y : p, p+d prime}  ≤  2e·K·Y/E²  +  K·R ,
      E = exp(mertensS h − mertensS P₁) ≍ log h ≍ log Y ,      R ≪ √z·(log z)^5 .
```

That is exactly (PP), the estimate the device inequality `ρ·ν ≤ μ/4` needs.  The lift may therefore
stay at `W ≍ log m`, and the physical window stays at `√X·X^{o(1)}`.

### What is left

Only bookkeeping: instantiate `Sieve/LiftedMarkerBlock.card_sign_window_ge_block` at
`M₀ = m·W`, `X = m·M₀`, `H = 2·L·M₀`, `W = ⌊log(m²)⌋`, `L = ⌈cardLength β (m²)⌉ + 1`,
`Q = 2`, `K = 4W`, feeding `Pi` from `sum_card_shift_bigPrimeSet_le_sieve_sharp`; then sum over
the `K₀ = ⌈log₂ Q⌉` dyadic marker blocks with the shrunk windows `scaledLength (2^{-k}) β`.
