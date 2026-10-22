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

## The multi-block frame is Lean (2026-08-19)

`Sieve/MultiBlockFrame` carries the whole `K₀`-block construction with explicit parameters
(`v` the free integer, `m = 2^{K₀+1}v`):

```
multiHalf K₀ v k = 2^{K₀-k}·v          multiBlockLen K₀ v k = 2·multiHalf   (= m/2^k)
multiScale K₀ v  = multiBlockLen K₀ v 0                              (= m)
multiFactor K₀ v = ⌊log(m²)⌋                                          (= W)
multiBase K₀ v   = m·W                                                (= M₀)
multiPhys K₀ v   = m·M₀                                               (= X)
multiCell β K₀ v = ⌈cardLength β (m²)⌉ + 2^{K₀}                        (= L)
multiWindow β K₀ v = 2·L·M₀                                            (= H)
multiBlockScale K₀ v k  = (m/2^k)²                                     (= y_k)
multiBlockWindow β K₀ v k = scaledLength (2^{-k}) β y_k                 (= h_k)
```

Proved:

- `block_start_ge`, `block_start_lt`, `multiPhys_block`, `exists_block` — every marker of
  `(M₀, 2^{K₀+1}M₀]` lies in exactly one dyadic block, and its reciprocal start lands in
  `[m/2^{k+1}, m/2^k)`, which is exactly the realisable range of the block's outer factors.
- `multi_fit` — the block's fibre fits inside the marker's cell.  The `+2^{K₀}` in `multiCell` is
  what pays for the floor's `+1` at the top block.
- `multi_supply` — the fibre fills at least `ϱ/256` of the cell, under
  `L ≤ 12·cardLength β y_k − 24·2^k`.
- `multi_cell_bound` — the two combined, through `cell_bound_of_good_start`.
- `card_sign_window_ge_multi` — the whole family, via `card_sign_window_ge`, with `Pi`, `S`, `B`
  abstract.
- `multi_separation` (`q ≤ p + 4^{K₀+1}·W`) and `sum_inv_goodMarkers_ge` — the device on the family.
- `card_badStartUnion_le` — the exceptional starts of the family are the sum of the blocks'.
- `multiBlockScale_div` (`y_k = y_0/4^k`), `CardLengthDilation.eventually_half_cardLength_le_dilated`
  and `eventually_multiCell_le` — the supply condition holds at every block, eventually in `v`.
- `two_le_multiScale`, `two_le_multiFactor`, `multiPhys_add_le`, `eventually_multi_basics` —
  `0 < M₀` and `X + H ≤ M₀²`, eventually in `v`.

Left: the shifted-pair budget `Pi` at concrete `(P₁, h, z)` from
`Sieve/PrimePairAverageSharp.sum_card_shift_bigPrimeSet_le_sieve_sharp`, the device threshold
`#badStartUnion·(#M+2Pi) ≤ b²`, the harmonic mass `S` (sharp Mertens) and the count `B`
(Brun–Titchmarsh), then the count theorem and the transfer from `X = multiPhys` to all large `X`.

## The pair budget is instantiated (2026-08-19)

`Sieve/SieveRemainderBound.sieve_remainder_le` : for `P₁ ≥ 2` and `z ≥ 1`,

```
      ∑_{e | P(P₁,h), e ≤ z} 2·6^{ω(e)}  ≤  2 z³ .
```

Every such `e` is squarefree with all prime factors `≥ 3`, so `3^{ω(e)} ≤ e` and hence
`6^{ω(e)} ≤ 9^{ω(e)} ≤ e²`; and the `e` are distinct positive integers below `z`.

`Sieve/MultiPairBudget` fixes the sieve parameters of the family:

```
      multiLevel K₀ v = M₀^{1/4}      multiSift K₀ v = ⌊M₀^{1/144}⌋      multiPairK K₀ v = 4^{K₀+1}·W
```

`multiSift_pow_le` verifies the level condition `h^{18} ≤ √z` exactly (`18/144 = 1/8 = (1/4)/2`),
and `multi_pair_le` gives

```
      ∑_{d ≤ K} #{p ∈ M : p+d ∈ M}
        ≤ 2e·K·(2^{K₀+1}M₀)/exp(mertensS h − mertensS 3)²  +  K·2·M₀^{3/4} .
```

The saving is `exp(mertensS h − mertensS 3) ≍ log h/log 3 ≍ log M₀/158`, so the first term is
`≍ M₀/log M₀ ≍ m` and the second is `M₀^{3/4} log M₀ = o(m)`.  That is `Pi = O(m)` — the shape the
device inequality `ρ·ν ≤ μ/4` needs.

Still to do: `∃ C, ∀ᶠ v, Pi ≤ C·m` (Mertens-second lower bound on the saving), the device threshold
`#badStartUnion·(#M+2Pi) ≤ b²` with `#badStartUnion = o(m)` from `Sieve/ScaledBadStart`, the
harmonic mass `S` and count `B` of the marker range, the count theorem, and the transfer from
`X = multiPhys K₀ v` to all large `X`.

## The budget and the exceptional set are both `O(m)` in Lean (2026-08-19)

- `Sieve/MultiPiBound.multiPi_le` : with `multiPi K₀ v` the explicit budget of `multi_pair_le`,

  ```
        multiPi K₀ v  ≤  multiPiConst K₀ · m ,
        multiPiConst K₀ = 8e·8^{K₀+1}·(288 log 3)²·e^{2(L+U)} + 1 ,
  ```

  under `2 ≤ M₀`, `1 ≤ W`, `288 log 2 ≤ log M₀`, `3 ≤ h`, `8·4^{K₀+1}(log M₀)² ≤ M₀^{1/4}`.
  The two ingredients are `sieve_saving_ge` (`exp(mertensS h − mertensS 3) ≥ (log h/log 3)e^{-(L+U)}`
  from Mertens' second theorem) and `log_multiSift_ge` (`log h ≥ log M₀/288`).
- `Sieve/MultiEventual` : all five side conditions hold eventually in `v`, from `multiBase → ∞`;
  the remainder condition uses `isLittleO_log_rpow_rpow_atTop 2 (1/4)`.
  Capstone: `eventually_multiPi_le`.
- `Sieve/MultiBadStart.eventually_card_badStartUnion_le` : **for every `ε > 0`**,
  eventually `#badStartUnion β K₀ v ≤ ε·m`.  Each block contributes
  `1024ε'√y_k/ϱ² + √y_k/(log y_k)²` with `√y_k = m/2^k ≤ m`; choosing the mean-square tolerance
  `ε' = δϱ²/2048` with `δ = ε/(2(K₀+1))` and summing the `K₀+1` blocks gives `ε·m`.

That is exactly `ρ = o(1)` and `ν = O(1)` in the invariant device inequality `ρ·ν ≤ μ/4`.

### The final arithmetic, checked

With `B ≍ 16·2^{K₀+1}M₀/log M₀` (Brun–Titchmarsh at `Y = M₀^{1/8}`) and
`S ≥ A(K₀)/log M₀`, `A(K₀) = (K₀+1)(log 2)/2 − 2(2·mertensFirstConst + 1/2)` (sharp Mertens at
`z = M₀`, `b = 2^{K₀+1}M₀`):

```
      ϱ/256 · (H·S − B)  ≥  (ϱ/256)·A(K₀)·L·M₀/log M₀ ,        C·H/log X = C·L·M₀/log M₀ ,
```

so the constant in `#T_σ ≥ C·H/log X` is `C = (ϱ/256)·A(K₀)`, **unbounded in `K₀`**; and the device
threshold reads `ε·(32·2^{K₀+1} + 2·multiPiConst K₀) ≤ A(K₀)²`, a fixed positive `ε`.

Left: `hB` (Brun–Titchmarsh at the family's range), `hS` (sharp Mertens), the device threshold, the
count theorem, and the transfer from `X = multiPhys K₀ v` to all large `X`.

## Statement (3) of the Hall card is Lean, at the constructed scales (2026-08-19)

`Sieve/MultiDevice.exists_eventually_card_sign_window_ge` — unconditional, axioms
`[propext, Classical.choice, Quot.sound]`:

```
   for  9/10 < β < 1,  every  C : ℝ,  and either sign σ = ±1 :
     ∃ K₀, ∀ᶠ v : ℕ in atTop,
        C · H/log X  ≤  #{ n ∈ (X, X+H] : μ(n) = σ } ,
     X = multiPhys K₀ v ,   H = multiWindow β K₀ v .
```

The chain of the last stretch:

- `Sieve/MultiHarmonic` — `eventually_multiHarm_ge` (sharp Mertens over `K₀+1` dyadic blocks, net
  constant `multiHarmConst K₀ = (K₀+1)(log 2)/2 − 2(2·mertensFirstConst + 1/2)`, via
  `log(1+u) ≥ u/(1+u) ≥ u/2`) and `eventually_multiCount_le` (Brun–Titchmarsh at `Y = ⌊M₀^{1/8}⌋`,
  `#M ≤ 64·2^{K₀+1}M₀/log M₀`).
- `Sieve/MultiDevice` — `eventually_multiFactor_bounds` (`log M₀/2 ≤ W ≤ 2 log M₀`),
  `multiEps K₀ = multiHarmConst²/(16(128·2^{K₀+1} + 2·multiPiConst))` — the Möbius tolerance the
  Cauchy–Schwarz device can afford — then `eventually_card_sign_window_ge`,
  `eventually_card_sign_window_ge_const` (constant `ϱ·multiHarmConst K₀/1024`), and finally
  `tendsto_multiHarmConst` giving the `for every C` form.

**Remaining for the card:** (i) recognise the window as `H = √X·exp((log X)^{β'})` — currently
`H/√X = 2·multiCell·√W`, which is `X^{o(1)}` but has to be matched to the card's `h(X)`; (ii) the
transfer from `X = multiPhys K₀ v` to *all* large `X` (the gap between consecutive `multiPhys` is
`≍ √X·√W ≪ H`, so a covering argument suffices); (iii) the unique-decoding/injection corollary (5),
which is already Lean in `Sieve/WindowMatching` and `Sieve/MarkerSignWindowCount`.

## The arbitrary-scale obstruction is removed (2026-08-19)

`Sieve/MultiBlockFrame` ties the physical scale to `X = m·M₀` because a *dyadic range of primes*
`(2^k M₀, 2^{k+1} M₀]` only has its reciprocal starts inside the realisable range `[√y/2, √y − 1]`
when `X` is exactly that product.  `Sieve/FreeScaleMarkerBlock` indexes the block by its **start
range** instead, and the constraint disappears:

```
      freeStart m k = m / 2^k ,
      freeBlock X m k = bigPrimeSet (X / freeStart m k) (X / freeStart m (k+1)) .
```

- `start_mem_of_mem_bigPrimeSet` — `p ∈ (X/b, X/a]` **iff** `X/p ∈ [a, b−1]`.  Both directions are
  the same Nat fact `X/p < b ↔ X < p·b`, so there is no rounding loss at all.
- `start_mem_freeBlock` — hence every marker of block `k` has `X/p ∈ [m_{k+1}, m_k − 1]`.
- `freeStart_two_mul` — with `2^{K₀+1} ∣ m` each start scale halves **exactly**, so
  `m_{k+1} = m_k/2` on the nose.
- `freeBlock_start_bounds` — therefore `m_k/2 ≤ X/p` and `X/p + 1 ≤ m_k` in `ℝ`, which are exactly
  the two hypotheses `htlow`, `hthigh` of `Sieve/MarkerBlockSignCount.cell_bound_of_good_start`.
- `freeBlock_subset_range`, `exists_freeBlock` — the blocks all sit in the single prime range
  `(X/m, X/(m/2^{K₀+1})]`, and every prime of that range lies in exactly one block.  Consecutive
  halvings give **consecutive, disjoint** prime ranges, so the harmonic mass and the device apply
  to the union exactly as before.

`X` is now a free parameter.  The fit and supply conditions are unchanged: with `H = 2·L·(X/m)`,
`p ≤ 2X/m_k` gives `H/p ≥ (hy_k+1)` from `L ≥ C_k + 2^k`, and `p > X/m_k` gives `H/p < 2L/2^k`, so
the supply condition is again `L ≤ 12·C_k − 24·2^k`.  What remains for the card is to re-run
`Sieve/MultiDevice` over `freeBlock` in place of the dyadic blocks, and then to note that the
resulting window `H = 2L·(X/m)` at `m ≍ √(X/W)` is `√X·exp((log X)^β)·Θ(√log X)`, so the card's
`H(X)` is covered by tiling `(X, X+H(X)]` with consecutive free-scale windows — which is now
possible precisely because the construction runs at every `X`.

## The whole per-marker argument now runs at a free scale (2026-08-19)

Three more modules, all unconditional, all built and wired:

- `Sieve/FreeScaleCellBound` — `freeScale m k = (m/2^k)²`,
  `freeWindow β m k = scaledLength (2^{-k}) β (freeScale m k)`, and

  ```
     free_cell_bound :   (freeWindow + 1)·p ≤ H                                        (fit)
                         rho·(H/p − 1) ≤ (3/16)ϱ·(freeWindow/2 − 1)                    (supply)
                         X/p ∉ badStart (freeScale m k) (freeWindow β m k)
                      ⟹  rho·(H/p − 1) ≤ #{ a ∈ windowCell X H p : μ(a) = −σ } .
  ```

  Both hypotheses are inequalities in the **block data alone** — the physical scale `X` has
  disappeared from them, which is what the start-range indexing bought.
- `Sieve/MarkerSignWindowCount.card_sign_window_ge'` — the harmonic sign count from
  `∀ p ∈ P, p.Prime` and `∀ p ∈ P, M₀ < p` instead of `P ⊆ bigPrimeSet M₀ (Q·M₀)`, so the marker
  set need not be a dyadic prime range.
- `Sieve/FreeScaleWindowCount.free_card_sign_window_ge` — the assembly:

  ```
     rho·(H·S − B)  ≤  #{ n ∈ (X, X+H] : μ(n) = σ }
  ```

  for **any** `X`, with `S` the harmonic mass and `B` the count of
  `freeGoodMarkers β X m K₀ = { p ∈ (X/m, X/(m/2^{K₀+1})] : X/p ∉ freeBadStartUnion β m K₀ }`.

So the construction is no longer tied to `X = multiPhys K₀ v`.  What remains for the card is the
analytic instantiation at a free scale — the free-scale copies of `eventually_multiPi_le`,
`eventually_card_badStartUnion_le`, `eventually_multiHarm_ge`, `eventually_multiCount_le` and the
device threshold, which are the same estimates with `multiBase K₀ v` replaced by `X / m` — and then
the tiling of the card's `H(X)` by consecutive free-scale windows.

### The device at a free scale

`Sieve/FreeScaleWindowCount`, unconditional:

- `freeRange X m K₀ = bigPrimeSet (X/m) (X/(m/2^{K₀+1}))` — the whole marker range;
  `freeGoodMarkers_eq` identifies the good markers as its subset avoiding `freeBadStartUnion`.
- `free_separation` — two markers of the range with the same reciprocal start differ by at most
  `X/(m/2^{K₀+1})²`, from `Sieve/MarkerLossDevice.reciprocal_separation` at the range's minimal
  start.
- `free_sum_inv_goodMarkers_ge` — the Cauchy–Schwarz device at a free scale: under a shifted-pair
  budget `Pi` and the threshold `#freeBadStartUnion·(#freeRange + 2Pi) ≤ b²`,

  ```
        ∑_{p ∈ freeRange} 1/p − b/(X/m)  ≤  ∑_{p ∈ freeGoodMarkers} 1/p .
  ```

- `card_freeBadStartUnion_le` — the family's exceptional starts are the sum of the blocks'.

**Every structural step of the marker programme now holds at an arbitrary physical scale.**  What
is left is arithmetic: the free-scale copies of `eventually_multiPi_le`,
`eventually_card_badStartUnion_le`, `eventually_multiHarm_ge`, `eventually_multiCount_le` — the
same estimates with `multiBase K₀ v` replaced by `X/m` — the device threshold, and the tiling.

### One of the four free-scale estimates is done

`Sieve/FreeScaleBadStart`, unconditional:

- `freeStart_pow_mul`, `freeStart_pow_mul_pos`, `dvd_pow_mul` (in `FreeScaleMarkerBlock`) — with the
  base written `m = 2^{K₀+1}·u`, every start scale is `freeStart m k = 2^{K₀+1−k}·u`, exactly.
- `tendsto_freeScale`, `tendsto_freeStart_zero` — each block's cofactor scale and the base start
  scale grow with `u`.
- `eventually_card_freeBadStartUnion_le` — **for every `ε > 0`**,

  ```
        ∀ᶠ u,   #freeBadStartUnion β (2^{K₀+1}u) K₀  ≤  ε · freeStart (2^{K₀+1}u) 0 .
  ```

  Same mechanism as the fixed-scale version: block `k` contributes
  `1024ε'·√y_k/ϱ² + √y_k/(log y_k)²` with `√y_k = m/2^k ≤ m`, and the mean-square tolerance
  `ε' = δϱ²/2048`, `δ = ε/(2(K₀+1))`, is free.  Note this estimate depends only on the *start*
  scale `m`, not on the physical scale `X` — which is why it transferred without change.

Remaining for the card: the free-scale pair budget, harmonic mass and marker count (all three are
`Sieve/PrimePairAverageSharp`, `Sieve/MertensWindowSharp` and `Sieve/MarkerCountUpper` applied at
`M₀ = X/m`, `b = X/(m/2^{K₀+1})`), the device threshold, and the tiling.

### The free-scale structural capstone

`Sieve/GenericPairBudget` lifts the sieve parameters off the particular marker base:
`sieveLevel M₀ = M₀^{1/4}`, `sieveSift M₀ = ⌊M₀^{1/144}⌋`, `sieveSift_pow_le` (the level condition
`h^18 ≤ √z`, exact because `18/144 = 1/8`), and

```
   generic_pair_le :  ∑_{d ≤ K} #{p ∈ (M₀,b] : p+d ∈ (M₀,b]}
                        ≤ 2e·K·b/exp(mertensS h − mertensS 3)²  +  K·2·(M₀^{1/4})³
```

for **any** base `M₀`, under `1 ≤ M₀`, `3 ≤ sieveSift M₀`, `20·mertensFirstConst ≤ log(sieveSift M₀)`.

`Sieve/FreeScaleWindowCount.free_card_sign_window_ge_device` then closes the structure at a free
physical scale:

```
   rho·(H·S − B)  ≤  #{ n ∈ (X, X+H] : μ(n) = σ }
```

from: the per-block fit and supply; the shifted-pair budget `Pi` of the marker range; the device
threshold `#freeBadStartUnion·(#freeRange + 2Pi) ≤ b²`; the harmonic mass
`S ≤ ∑_{p ∈ freeRange} 1/p − b/(X/m)`; and the count `B ≥ #freeRange`.  Every hypothesis is now an
inequality between quantities the corpus already estimates:

| hypothesis | supplied by |
|---|---|
| `Pi` | `Sieve/GenericPairBudget.generic_pair_le` at `M₀ = X/m`, `b = X/(m/2^{K₀+1})` |
| `#freeBadStartUnion ≤ ε·m` | `Sieve/FreeScaleBadStart.eventually_card_freeBadStartUnion_le` |
| `S` | `Sieve/MertensWindowSharp.sum_inv_bigPrimeSet_ge_sharp` |
| `B` | `Sieve/MarkerCountUpper.card_bigPrimeSet_le_explicit` |

**The marker programme is now structurally complete at every physical scale.**  What is left is the
arithmetic: choose `m ≍ √(X/log X)`, check the fit/supply/threshold inequalities at those values
(the same computations as `Sieve/MultiPiBound` and `Sieve/MultiDevice`, with `multiBase K₀ v`
replaced by `X/m`), and tile the card's `H(X)` by consecutive free-scale windows.

### The fit and supply conditions, discharged at every scale

`Sieve/FreeScaleFitSupply`, unconditional.  Writing `C₀ = cardLength β (freeScale m 0)` and taking
the cell parameter

```
        H  ≍  (2·C₀ + 2^{K₀+1}) · X / m ,
```

- `free_fit_of_le` — if `(2C₀ + 2^{K₀+1})·X/m ≤ H` then every marker of every block satisfies the
  fit `(freeWindow β m k + 1)·p ≤ H`.  The proof is exact: a marker of block `k` obeys
  `p ≤ 2^{k+1}X/m`, the block window obeys `freeWindow β m k ≤ 2^{-k}C₀`, and
  `2^{-k}·2^{k+1} = 2`, so the product is `(2C₀ + 2^{k+1})X/m`.
- `free_supply_of_le` — if `H ≤ (2C₀ + 2^{K₀+1})·X/m` and

  ```
        2·C₀ + 2^{K₀+1}  ≤  24·(freeWindow β m k · 2^k) − 48·2^k
  ```

  then every marker satisfies the supply
  `(ϱ/256)(H/p − 1) ≤ (3/16)ϱ(freeWindow β m k/2 − 1)`.  A marker of block `k` obeys
  `p > X/freeStart m k`, so its cell is at most `(2C₀ + 2^{K₀+1})/2^k`.
- `freeWindow_le`, `freeScale_le_zero`, `one_le_freeScale` — the block window against the base one.

**Both conditions are inequalities in `m` alone** — `X` cancels between the marker's size and the
window.  Since `freeWindow β m k · 2^k = cardLength β (freeScale m k)` and
`cardLength β (freeScale m k) ≥ C₀/2` eventually (`CardLengthDilation`), the gap hypothesis reads
`2C₀ + 2^{K₀+1} ≤ 12C₀ − 48·2^{K₀}`, i.e. `49·2^{K₀+1} ≤ 10·C₀`, which holds for all large `m`.

So a single choice of `m` serves **every** physical scale `X` simultaneously — which is exactly what
the tiling of the card's `H(X)` needs.

### The harmonic mass and the count, at a free scale

`Sieve/FreeScaleHarmonic`, unconditional:

- `freeRange_top_ge` — the marker range spans a factor `2^{K₀+1}` exactly:
  `2^{K₀+1}·(X/m) ≤ X/(m/2^{K₀+1})`, from `Nat.div_div_eq_div_mul` and `Nat.div_mul_le_self`.
- `log_freeRange_top_ge` — hence `log(top) ≥ (K₀+1)·log 2 + log(X/m)`, the input the sharp Mertens
  comparison `logLog(top) − logLog(X/m) ≈ (K₀+1)log 2/log(X/m)` needs.
- `free_harm_ge` — `Sieve/MertensWindowSharp.sum_inv_bigPrimeSet_ge_sharp` applied to `freeRange`.
- `free_count_le` — `Sieve/MarkerCountUpper.card_bigPrimeSet_le_explicit` applied to `freeRange`.

All four ingredients of `free_card_sign_window_ge_device` are now available at a free scale:
the pair budget (`GenericPairBudget.generic_pair_le`), the exceptional starts
(`FreeScaleBadStart.eventually_card_freeBadStartUnion_le`), the harmonic mass (`free_harm_ge`) and
the count (`free_count_le`); the fit and supply are `FreeScaleFitSupply`.

What is left is to choose `m` from `X`, check the device threshold
`#freeBadStartUnion·(#freeRange + 2Pi) ≤ b²` at those values — the same computation as
`Sieve/MultiDevice` — and sum the tiles.

### The cell parameter, and both conditions at once

`Sieve/FreeScaleFitSupply` now closes the two-sided band.  Writing
`C₀ = cardLength β (freeScale m 0)`:

```
        freeCell β X m K₀ = ⌈ (2C₀ + 2^{K₀+1}) · X / m ⌉
```

- `free_supply_of_le` is now parametric in the upper bound `A₂` (`H ≤ A₂·X/m`, gap
  `A₂ ≤ 24(freeWindow·2^k) − 48·2^k`), so the fit's lower bound and the supply's upper bound need
  not coincide.
- `free_fit_supply_ceil` — **both conditions hold simultaneously at `H = freeCell β X m K₀`**,
  for every block and every marker, provided `m ≤ X` and

  ```
        2C₀ + 2^{K₀+1} + 1  ≤  24·(freeWindow β m k · 2^k) − 48·2^k      for all k ≤ K₀.
  ```

  The ceiling lands in the band because `⌈A⌉ < A + 1 ≤ A + X/m`.  Since
  `freeWindow β m k · 2^k = cardLength β (freeScale m k) ≥ C₀/2` eventually, the displayed gap is
  `2C₀ + 2^{K₀+1} + 1 ≤ 12C₀ − 48·2^{K₀}`, i.e. `49·2^{K₀+1} + 1 ≤ 10C₀` — a condition on `m` alone.

So for a single `m`, the fit and supply hold at **every** `X ≥ m` with the cell parameter
`freeCell β X m K₀`.  Together with `Sieve/WindowTiling.card_filter_Ioc_tile` this is the last
structural ingredient; what remains is the device threshold at `M₀ = X/m` and the choice of `m`.

## The tile family, and the count on one tile

The construction is now indexed by the start modulus rather than by the physical scale.  With
`K₀` blocks and index `u`:

```
        m = tileM K₀ u = 2^{K₀+1}·u          the start modulus
        T = tileLog K₀ u = ⌊log m⌋
        P = tileBase K₀ u = m²·T             the bottom of the physical range
        C = tileC β K₀ u = cardLength β (m²)
        h = tileLen β K₀ u = ⌈(2C + 2^{K₀+1})·2P/m⌉
```

`Sieve/FreeScaleTileCount.exists_tile_count` proves, for every `9/10 < β < 1`, every sign `σ`, and
every `K₀` with positive net harmonic mass:

> for all large `u` and **every** `X` with `P ≤ X ≤ 2P`,
> `(ϱ/256)·(h·multiHarmConst K₀/(2 log M) − 64·2^{K₀+2}·M/log M) ≤ #{n ∈ (X, X+h] : μ(n) = σ}`,
> where `M = X/m`.

`tile_count_clean` absorbs the marker count into the main term (it costs a factor 4, and needs only
`C ≥ 128·2^{K₀+2}/multiHarmConst K₀`) and replaces `log M` by `log X`:

> `tileConst K₀ · h/log X ≤ #{n ∈ (X, X+h] : μ(n) = σ}`,   `tileConst K₀ = ϱ·multiHarmConst K₀/1024`.

**One modulus serves a whole dyadic range**, which is what makes the tiling possible.  The three
numerical inputs of `free_count_master` become, at these parameters:

| input | what it says | how it is met |
|---|---|---|
| `T₁` | markers vs squared harmonic mass | `u·log M ≤ 4M/2^{K₀+1}`, i.e. the choice `X ≍ m² log m`; then `768·ε·2^{K₀+3} ≤ A²` |
| `T₂` | shifted-pair budget | `6·ε·pairMainConst·2^{3K₀+6} ≤ A²` — **scale-free**: the `(log M)²` of the sharp pair sieve cancels the `(log M)²` of the squared harmonic mass |
| `T₃` | sieve remainder | `12·ε·2^{2K₀+4}(log M)² ≤ A²·M^{1/4}` — eventual in `M` |

with `A = multiHarmConst K₀/2` and `ε` chosen from `K₀` alone.  That `T₂` is scale-free is exactly
the payoff of the Rankin exponent `α = 1/log h`: with the corpus's old exponent `1/k` the level was
`h^{k}` with `k ≍ log log h`, and `T₂` would have carried a `(log log)²` that no choice of `ε`
could absorb.

Still open on this card: the covering (for each large `Z` a modulus `u` with `P ≤ Z` and
`2Z < 3P`) and the tiling of `(Z, Z+H]` by `h`-blocks.
