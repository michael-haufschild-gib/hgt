# Route E two-sided off-normal Wold-breadth transport

- **ID:** ROUTE-E-OFF-NORMAL-WOLD-BREADTH-003
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / Lean finite-rate certificate
- **Parent:** `route-e-growing-reciprocal-marker-low-breadth-transport.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no

## Result `[PROVED HERE]`

Use
\[
h(X)=\exp\!\left(\frac{\log X}{\log\log X}\right),
\qquad H(X)=\sqrt X\,h(X).
\tag{1}
\]
Fix \(0<c_-<1<c_+\), and let
\[
\mathcal E_{c_-,c_+}(X,H)=
\left\{X<n\le X+H:\mu(n)\ne0,\
\omega(n)\le c_-\log\log X\ \text{or}\
\omega(n)\ge c_+\log\log X\right\}.
\tag{2}
\]
Every sufficiently large \(H\)-cell admits disjoint opposite-Möbius-sign edges of displacement at
most \(H\) covering all vertices of \(\mathcal E_{c_-,c_+}(X,H)\).  Targets can be chosen outside
\(\mathcal E_{c_-,c_+}(X,H)\).  Across a dyadic shell, aggregate first-order Gibbs cost is
\(X^{1/2+o(1)}\).

Consequently all fixed lower and upper deviations from normal Wold breadth are closed.  Any
unresolved sequence in the physical-capacity branch must satisfy
\[
\frac{\omega(n)}{\log\log n}\longrightarrow1.
\tag{3}
\]
This does not close the central normal-order sector or co-moving seam flux.

## Proof

Define the two-sided Chernoff rate
\[
I(c)=1-c+c\log c.
\tag{4}
\]
For every \(c>0\), \(c\ne1\),
\[
c-1<c\log c,
\tag{5}
\]
so \(I(c)>0\).  This strict inequality is valid on both sides of one; no separate upper-tail
entropy function is needed.

Shiu's short-interval upper bound for the nonnegative multiplicative function
\(z^{\omega(n)}\), uniformly on an \(H\)-cell with \(H\ge\sqrt X\), gives for each fixed \(z>0\)
\[
\sum_{X<n\le X+H}z^{\omega(n)}
\ll_z H(\log X)^{z-1}.
\tag{6}
\]

For the lower tail take \(z=c_-<1\).  If
\(\omega(n)\le c_-\log\log X\), then
\[
1\le z^{\omega(n)-c_-\log\log X}.
\]
Equation `(6)` yields
\[
\#\{\omega(n)\le c_-\log\log X\}
\ll_{c_-}H(\log X)^{-I(c_-)}.
\tag{7}
\]

For the upper tail take \(z=c_+>1\).  If
\(\omega(n)\ge c_+\log\log X\), the same inequality
\[
1\le z^{\omega(n)-c_+\log\log X}
\]
has the opposite monotonic regime but identical algebra.  Hence
\[
\#\{\omega(n)\ge c_+\log\log X\}
\ll_{c_+}H(\log X)^{-I(c_+)}.
\tag{8}
\]

Put \(\delta=\min\{I(c_-),I(c_+)\}>0\).  Equations `(7)`--`(8)` give
\[
\#\mathcal E_{c_-,c_+}(X,H)
\ll H(\log X)^{-\delta}
=o\!\left(\frac H{\log\log X}\right).
\tag{9}
\]

The growing reciprocal-marker theorem supplies \(\gg H/\log\log X\) distinct physical targets
of each nonzero Möbius sign in every cell.  Delete all vertices of
\(\mathcal E_{c_-,c_+}\) from both target reservoirs.  Equation `(9)` leaves enough positive and
negative targets to inject the two source signs separately into unused opposite-sign targets.
The matchings are disjoint because target signs differ.

For \(x\asymp X^{-1}\), one edge costs
\[
|e^{-xm}-e^{-xn}|\le x|m-n|e^{-x\min(m,n)}\ll xH.
\]
There are \(O(X)\) source vertices across a dyadic shell, so total first-order cost is
\[
O(xXH)=O(H)=X^{1/2+o(1)}.
\tag{10}
\]

Finally, if an unresolved sequence had
\(\omega(n)/\log\log n\not\to1\), some fixed \(\eta>0\) and subsequence would lie in `(2)` with
\(c_-=1-\eta\) or \(c_+=1+\eta\), contradicting its transport.  This proves `(3)` as a frontier
localization, not as a uniform shrinking-window estimate.

## Hostile audit

1. **No uniform moving tilt is claimed.**  \(c_-\) and \(c_+\) are fixed before \(X\to\infty\).
   Statement `(3)` is the logical exclusion of every fixed deviation, not a quantitative
   Erdős--Kac window.
2. **No parity cancellation is imported.**  Shiu is applied only to positive
   \(z^{\omega(n)}\).  Möbius signs enter through already-proved reciprocal-marker target
   reservoirs.
3. **Physical capacity remains physical.**  Marker products are uniquely decoded; the proof does
   not amplify representation labels.
4. **Central band remains positive density.**  The theorem does not imply `OPEN-SOURCE-001`, a
   Mertens bound, or RH.

## Lean status

`MobiusWoldBreadthTwoSidedDeviationRate.lean` proves unconditionally:

- exact exponent identity
  `c - 1 - c log c = -I(c)`;
- `I(1)=0`;
- `I(c)>0` for every nonnegative `c != 1`;
- separate strict lower- and upper-tail specializations.

Existing `MobiusReciprocalMarkerPrimeCapacity.lean` proves finite physical-window, sign,
unique-decoding, and distinct-target skeleton.  Shiu's analytic short-interval estimate remains
paper-level.

## Novelty audit

Upper-tail Chernoff algebra is classical.  Candidate project-new content is its composition with
growing reciprocal-marker physical reservoirs, which removes both fixed Wold-breadth deviations
and localizes surviving Route E capacity to exact normal order.  No independent priority claim is
made for `(4)`--`(8)`.

## Log

- 2026-08-01 — symmetric hostile audit found upper-tail omission in prior low-breadth theorem;
  proved two-sided transport and formalized exact rate positivity.

## Lean completion programme (opened 2026-08-03)

The only paper-level step left in this card is the Shiu-type short-interval upper bound `(6)`.
It is being built unconditionally in the corpus rather than cited.  Corpus/mathlib audit done
before starting:

- mathlib `Mathlib/NumberTheory/SelbergSieve.lean` stops at the diagonalized Λ² quadratic form
  (`mainSum_lambdaSquared_eq_sum_mul_sum_sq`).  No optimized level, no fundamental lemma, no
  Brun–Titchmarsh.
- mathlib has `Nat.Ioc_filter_dvd_card_eq_div` (multiples of `d` in `Ioc 0 n`) and the Möbius
  arithmetic function, but **no** Bonferroni / truncated-Möbius inequality
  (`rg -il bonferroni` over mathlib: no hit).
- corpus `rg -il "selbergsieve|BoundingSieve|brun.?titchmarsh|shiu"` hits only
  `PrimeWindowBinomialBound.lean` (an elementary `log`-window bound, not a sieve) and this card's
  own `MobiusWoldBreadthTwoSidedDeviationRate.lean`.  No sieve exists in the corpus.

Chosen route: **Brun's pure sieve** (truncated inclusion–exclusion), not Selberg.  It is
combinatorial, needs no optimization step, and its output — the fundamental lemma — is exactly the
input Shiu's argument consumes.  It also supplies Brun–Titchmarsh, which
`route-e-reciprocal-marker-mobius-hall-law.md` `(26)` needs.

Stages (each unconditional, each wired into the umbrella when it lands):

1. `Sieve/IntervalMultiples.lean` — exact count of multiples of `d` in `Ioc X (X+H)`, and the
   `|#− H/d| ≤ 1` form.
2. `Sieve/TruncatedMoebius.lean` — the partial alternating binomial identity
   `∑_{j≤r} (-1)^j C(k,j) = (-1)^r C(k-1,r)` and the resulting Bonferroni inequalities for
   `∑_{d ∣ m, ω d ≤ r} μ d` against `[m = 1]`.
3. `Sieve/BrunPure.lean` — `S(A,z) ≤ H ∏_{p<z}(1−1/p) + (tail) + O(z^r)` for even truncation
   level `r`, with the explicit tail bound `∑_{j>r} (∑_{p<z} 1/p)^j / j!`.
4. `Sieve/FundamentalLemma.lean` — the usual `S(A,z) = H ∏_{p<z}(1−1/p)(1+O(e^{−u}))` form.
5. `Sieve/Shiu.lean` — `(6)` for `z^{ω(n)}` on `Ioc X (X+H)` with `H ≥ √X`.
6. `MobiusWoldBreadthTwoSidedTail.lean` — `(7)`, `(8)`, `(9)` from `(6)` and the already-proved
   `woldBreadthDeviationRate_pos`.

Stage 1 and 2 are elementary and start now.

### Stage 1–4 landed (2026-08-03) — sieve core is built and unconditional

Five new modules under `formal/GaloisForLFunctions/RHTower/Sieve/`, all wired into
`GaloisForLFunctions/RHTower.lean`, all building, all with
`#print axioms = [propext, Classical.choice, Quot.sound]`:

| module | content |
|-|-|
| `IntervalMultiples.lean` | `card_filter_dvd_Ioc` (exact count of multiples of `d` in `Ioc a b`), `abs_card_filter_dvd_Ioc_sub_lt` (`\|count − (b−a)/d\| < 1`) |
| `TruncatedMoebius.lean` | `alternating_choose_partialSum`, `sum_divisors_moebius_filter_card_le` (exact truncated value `(−1)^r C(ω m − 1, r)`), and both Bonferroni inequalities |
| `BrunPure.lean` | `card_coprime_Ioc_le` / `le_card_coprime_Ioc` — Brun's pure sieve on `Ioc a b` with main term `(b−a) ∑_{d ∣ m, ω d ≤ r} μ d/d` and error `#truncDivisors m r`; plus `coprime_prod_primes_iff` |
| `MainTerm.lean` | `sum_divisors_moebius_div_eq_prod` (`∑_{d ∣ m} μ d/d = ∏_{p ∣ m}(1−1/p)`), `card_truncDivisors` (`= ∑_{j ≤ r} C(ω m, j)`), and the graded description of the discarded divisors |
| `TruncationDefect.lean` | `abs_sum_truncDivisors_moebius_div_sub_prod_le`, and the capstones `card_coprime_Ioc_le_prod` / `prod_sub_le_card_coprime_Ioc` |

The capstone, for squarefree `m`, `a ≤ b`, even `r`, any tilt `λ ≥ 1`:

```text
#{n ∈ (a,b] : gcd(n,m)=1}
  ≤ (b−a) ∏_{p ∣ m}(1−1/p)
    + (b−a) λ^{−r} ∏_{p ∣ m}(1+λ/p)
    + #{d ∣ m : ω d ≤ r},
```
with the mirror lower bound at odd `r`.

**Method note.**  The classical treatment bounds the truncation tail by the elementary symmetric
functions and Maclaurin's inequality `j! e_j ≤ S^j`.  That is replaced here by an exponential
tilt: every discarded divisor has `ω d > r`, so `λ^r/d ≤ λ^{ω d}/d`, and
`∑_{d ∣ m} λ^{ω d}/d = ∏_{p ∣ m}(1+λ/p)` is a one-line `Finset.prod_add`.  Choosing
`λ ≍ r / ∑_{p ∣ m} 1/p` recovers the same geometric decay with no factorial and no symmetric
function theory.  This is why stage 4 landed in one pass.

Remaining: stage 5 (`Shiu.lean`, the `z^{ω(n)}` short-interval bound `(6)`) and stage 6
(`(7)`–`(9)`).

### Stage 5 plan — Shiu's bound `(6)` from the new sieve

Route (formalization-friendly, uses the sieve just built):

Fix `z₀ > 0` and a smoothness cut `z`.  Factor each `n` as `n = d·m` with `d` the `z`-smooth part
and `m` the `z`-rough part.  Then `z₀^{ω n} = z₀^{ω d} z₀^{ω m}`, and for `z = X^{1/L}` every
`z`-rough `m ≤ 2X` has `ω m ≤ L`, so `z₀^{ω m} ≤ max(1, z₀)^L = O_L(1)`.  Hence

```text
∑_{X<n≤X+H} z₀^{ω n} ≪_L ∑_{d z-smooth} z₀^{ω d} · #{m : dm ∈ (X, X+H], P⁻(m) > z}.
```

The inner count is exactly what `Sieve.card_coprime_Ioc_le_prod` bounds, with modulus the
primorial `∏_{p ≤ z} p`; it gives `≪ (H/d)/log z` once `∏_{p≤z}(1−1/p) ≪ 1/log z`.  The outer sum
is `∑_{d z-smooth} z₀^{ω d}/d ≤ ∏_{p≤z}(1 + z₀/p + z₀/p² + …) ≪ (log z)^{z₀}`.  Multiplying gives
`≪ H (log z)^{z₀−1}`, and `log z ≍ log X` up to a `log log X` factor, which is harmless for
`(7)`–`(9)` since only `o(H / log log X)` is used downstream.

**The missing analytic input is Mertens' second theorem**, and it is missing everywhere:

- mathlib has no Mertens theorem at all (`rg -il mertens` over mathlib hits only
  `RingTheory/Polynomial/ContentIdeal.lean`, an unrelated name);
- the corpus's many `Mertens`-named modules are all about the Mertens function `M(x)=∑μ(n)`, not
  about `∑_{p≤x} 1/p`.

Sharpness matters: with `∑_{p≤x} 1/p ≤ A log log x + O(1)` the Chernoff optimum in `(7)` becomes
`−I(c) + c log A`, so any `A > 1` destroys the theorem.  The constant must be exactly `1`.

Stage 5 therefore splits:

* **5a** `∏_{p≤z}(1−1/p) ≤ exp(−∑_{p≤z} 1/p)` and `∏_{p≤z}(1+λ/p) ≤ exp(λ ∑_{p≤z} 1/p)`
  (elementary, no arithmetic input).
* **5b** Chebyshev `θ(x) = ∑_{p≤x} log p ≪ x`, from mathlib's `Nat.primorial_le_4_pow`.
* **5c** Mertens' first theorem `∑_{p≤x} (log p)/p = log x + O(1)`, from Legendre's formula for
  `v_p(n!)`, mathlib's Stirling, and 5b.
* **5d** Mertens' second theorem `∑_{p≤x} 1/p = log log x + O(1)`, by **discrete** Abel summation
  from 5c against `f(n) = 1/log n` — no integral is needed for the `R(t)` part, which telescopes;
  the main part reduces to `∑_{n≤N} log(1+1/n)/log(n+1) = log log N + O(1)`, handled by mathlib's
  `AntitoneOn.sum_le_integral_Ico`.
* **5e** smooth/rough factorization and the assembly above.

### Stage 5a–5b landed (2026-08-03)

`formal/GaloisForLFunctions/RHTower/Sieve/Mertens.lean`, wired into the umbrella, built,
axiom-clean:

- `one_sub_le_exp_neg`,
- `prod_one_sub_inv_le_exp_neg_sum` : `∏_{p ∈ P}(1−1/p) ≤ exp(−∑_{p ∈ P} 1/p)`,
- `prod_one_add_le_exp_sum` : `∏_{p ∈ P}(1+λ/p) ≤ exp(λ ∑_{p ∈ P} 1/p)`,
- `sum_log_primesLE_le` : Chebyshev `∑_{p ≤ n} log p ≤ n log 4`, from mathlib's
  `primorial_le_four_pow`,
- `primeFactors_primorial_eq` : the sieve modulus `n#` has prime support exactly `primesLE n`,
  so `Sieve.card_coprime_Ioc_le_prod` applied at `m = n#` counts `z`-rough integers.

Both Euler products in the sieve capstone are now controlled by the single quantity
`∑_{p ≤ z} 1/p`.  Next: 5c (Mertens I) and 5d (Mertens II).

### Stage 5c–5d landed (2026-08-03) — Mertens I and II are proved

Three new modules, wired into the umbrella, built, axiom-clean
(`[propext, Classical.choice, Quot.sound]` on all 17 theorems):

**`Sieve/MertensFirst.lean`** — `∑_{p ≤ n} (log p)/p = log n + O(1)`.

- `div_le_factorization_factorial` : `⌊n/p⌋ ≤ v_p(n!)` (first Legendre term);
- `log_factorial_eq_sum_primesLE` : `log n! = ∑_{p ≤ n} v_p(n!) log p`;
- `log_factorial_le` : `log n! ≤ n log n` (from `n! ≤ n^n`);
- `le_log_factorial` : `n log n − n ≤ log n!` — **no Stirling**: one term of the exponential
  series gives `n^n/n! ≤ e^n`;
- `summable_log_div_sq`, `logSqTailConst` : the convergent correction from the higher prime
  powers, via `log k ≤ 2√k` and the `3/2` p-series;
- `sum_log_div_prime_mul_pred_le` : `∑_{p ≤ n} (log p)/(p(p−1)) ≤ 2·logSqTailConst`;
- **`mertensFirst_upper`** : `∑_{p ≤ n} (log p)/p ≤ log n + log 4`;
- **`mertensFirst_lower`** : `log n − 1 − 2·logSqTailConst ≤ ∑_{p ≤ n} (log p)/p`.

**`Sieve/LogLogTelescope.lean`** — the discrete model of `∫ dt/(t log t)`.

- `log_sub_log_le` / `le_log_sub_log` : `(b−a)/b ≤ log b − log a ≤ (b−a)/a`;
- `logLogIncrementSum N := ∑_{2 ≤ i < N} (log(i+1) − log i)/log(i+1)`;
- `logLogIncrementSum_le` / `le_logLogIncrementSum` :
  `logLog(N+1) − logLog 3 ≤ logLogIncrementSum N ≤ logLog N − logLog 2`.

  **No integral comparison.**  Concavity of `log` sandwiches each term between two consecutive
  increments of `log ∘ log`, and the sum telescopes.  For the lower bound the shift
  `log(i+2) − log(i+1) ≤ log(i+1) − log i` moves the increment one step forward.

**`Sieve/MertensSecond.lean`** — `∑_{p ≤ N} 1/p = log log N + O(1)`.

- `mertensS_eq_abel` : discrete summation by parts (`Finset.sum_range_by_parts`) against
  `1/log`, giving `S N = A N/log N + ∑_{2 ≤ i < N} (1/log i − 1/log(i+1))·A i`;
- `sum_Ico_inv_log_variation` : the total variation is `1/log 2 − 1/log N`, so the `R i` part is
  bounded by `mertensFirstConst/log 2`;
- **`mertensSecond_upper`** : `S N ≤ logLog N + (1 + 2·C/log 2 − logLog 2)`;
- **`mertensSecond_lower`** : `logLog N − (2·C/log 2 + logLog 3 − 1) ≤ S N`,
  with `C = mertensFirstConst = max (log 4) (1 + 2·logSqTailConst)`.

The leading constant is exactly `1`, as required: an `A·log log N` bound with `A > 1` would turn
the Chernoff exponent of `(7)` into `−I(c) + c log A` and destroy the theorem.

Remaining: **5e** — smooth/rough factorization, the sieve applied at the primorial modulus, and
the assembly into Shiu's `(6)`; then `(7)`–`(9)`.

### Fundamental lemma landed (2026-08-03) — `Sieve/RoughCount.lean`

Mertens II feeds Brun's pure sieve at the primorial modulus and both Euler products become explicit
powers of `log z`:

- `prod_one_sub_inv_primesLE_le` : `∏_{p ≤ z}(1−1/p) ≤ exp(c₀)/log z`
  (`c₀ = mertensSecondLowerConst`);
- `prod_one_add_primesLE_le` : `∏_{p ≤ z}(1+λ/p) ≤ exp(λ c₁)·(log z)^λ`
  (`c₁ = mertensSecondUpperConst`, `(log z)^λ` an `rpow`);
- `coprime_primorial_iff` : coprime to `z#` ⟺ no prime factor `≤ z`;
- **`card_rough_Ioc_le`** — the fundamental lemma:

```text
#{n ∈ (a,b] : P⁻(n) > z}
  ≤ (b−a)·exp(c₀)/log z
    + (b−a)·exp(λ c₁)(log z)^λ / λ^r
    + #{d ∣ z# : ω d ≤ r},          any even r, any λ ≥ 1.
```

Built, wired, axiom-clean.  This is the exact input Shiu's argument consumes, and it is also the
Brun–Titchmarsh source `route-e-reciprocal-marker-mobius-hall-law.md` `(26)` needs.

Remaining for `(6)`: the smooth/rough factorization `n = d·m`, the observation that a `z`-rough
`m ≤ 2X` with `z = X^{1/L}` has `ω m ≤ L`, the smooth-part sum
`∑_{d z-smooth} z₀^{ω d}/d ≤ ∏_{p ≤ z}(1 + z₀/p + z₀/p² + …)`, and the parameter choice
`log z ≍ log X / log log X` with `r ≍ log log z`.

### Smooth–rough splitting landed (2026-08-03) — `Sieve/SmoothRough.lean`

- `smoothPart z n`, `roughPart z n` (prime powers with `p ≤ z`, resp. `p > z`);
- `smoothPart_mul_roughPart` : `smoothPart z n * roughPart z n = n` for `n ≠ 0`;
- `primeFactors_roughPart` : `(roughPart z n).primeFactors = {p ∈ n.primeFactors | ¬ p ≤ z}`;
- `not_dvd_roughPart` : no prime `≤ z` divides the rough part — this is exactly the hypothesis
  `card_rough_Ioc_le` sieves for;
- `card_primeFactors_roughPart_add` : `ω(smooth) + ω(rough) = ω n`;
- **`pow_card_primeFactors_roughPart_le`** : `z ^ ω(roughPart z n) ≤ n`.  With `z = X^{1/L}` this
  caps the rough prime count by `L`, so `z₀^{ω(rough)} ≤ max(1,z₀)^L` is a constant.

Built, wired, axiom-clean.  Every structural ingredient of `(6)` is now in the corpus; what remains
is the smooth-part sum `∑_{d z-smooth} z₀^{ω d}/d ≤ ∏_{p ≤ z}(1 + z₀/p + z₀/p² + …)` and the
parameter bookkeeping (`log z ≍ log X/log log X`, `r ≍ log log z`, `λ` fixed).

### Smooth Euler bound landed (2026-08-03) — `Sieve/SmoothSum.lean`

- `smoothUpTo P Y` : the integers in `[1,Y]` with all prime factors in `P`;
- **`sum_smoothUpTo_le`** : for any nonnegative coprimality-multiplicative `g` with `g 1 = 1`,
  `∑_{s ∈ smoothUpTo P Y} g s ≤ ∏_{p ∈ P} ∑_{i ≤ Y} g(p^i)`.
  Proved by induction on `P`: splitting off `p` sends `s ↦ (v_p(s), ordCompl[p] s)` injectively
  into `range (Y+1) × smoothUpTo (P \ {p}) Y`, and `g` splits by coprimality.  Only the injection
  is used, so no exact counting is needed;
- `smoothWeight t s = t^{ω s}/s`, with `smoothWeight_one`, `smoothWeight_mul`;
- `sum_smoothWeight_prime_pow_le` : `∑_{i ≤ Y} smoothWeight t (p^i) ≤ 1 + t/(p−1)` (geometric);
- **`sum_smoothWeight_le`** : `∑_{s z-smooth, s ≤ Y} t^{ω s}/s ≤ ∏_{p ≤ z}(1 + t/(p−1))`.

Built, wired, axiom-clean.

### Sharpness note recorded before assembly

The route now in place gives, for `0 < c < 1`,

```text
#{n ∈ (a,b] : ω n ≤ c·log log z}  ≪  (b−a)·(log z)^{−I(c)}  +  errors,
```

by combining the smooth/rough bijection, `card_rough_Ioc_le`, and the **tilt**
`∑_{ω s ≤ k} 1/s ≤ t^{−k} ∏_{p ≤ z}(1 + t/(p−1))` at `t = k/∑_{p≤z} 1/p` — the same
exponential-tilt device used for the truncation defect, again avoiding `j! e_j ≤ S^j`.
Optimising reproduces the Chernoff rate `I(c) = 1 − c + c log c` exactly.

The constraint is `log z`, not `log X`.  The sieve error forces `z^r ≤ b−a` and the smooth-part
cutoff forces `log z ≲ log X / log log X`, so this route proves `(7)`–`(8)` with `(log z)^{−I(c)}`,
i.e. with an extra `(log log X)^{I(c)}` factor compared with the literal statement.  **This does
not weaken the card's theorem**: `(9)` only needs `#E = o(H / log log X)`, and
`(log X)^{−δ}(log log X)^{O(1)} = o(1/log log X)` for every fixed `δ > 0`.  Getting the literal
`(log X)^{−I(c)}` requires Shiu's own argument (largest-prime-factor induction plus
Brun–Titchmarsh in progressions), which is recorded here as the remaining sharpening, not as a gap
in the card's theorem.

### Lower tail assembled (2026-08-03) — `Sieve/SmoothTilt.lean`, `SmoothCount.lean`, `OmegaTail.lean`

**`SmoothTilt.lean`**
- `prod_one_add_mul_le_exp` : `∏(1 + t·w p) ≤ exp(t ∑ w p)`;
- `sum_inv_pred_primesLE_le` : `∑_{p ≤ z} 1/(p−1) ≤ mertensS z + 1` — the correction telescopes
  through `1/(k(k−1)) = 1/(k−1) − 1/k`;
- **`sum_smoothUpTo_card_le_inv_le`** : `∑_{s z-smooth ≤ Y, ω s ≤ k} 1/s ≤ t^{−k} ∏_{p≤z}(1+t/(p−1))`
  for `0 < t ≤ 1` — the same exponential tilt again, now truncating from above;
- **`sum_smoothUpTo_card_le_inv_le_exp`** : the Chernoff shape
  `t^{−k}·exp(t(log log z + C))` after Mertens II.

**`SmoothCount.lean`** — `primePowerSet z Y` (prime powers `p^e ≤ Y`, `p ≤ z`, so `e ≤ log₂ Y`),
`card_primePowerSet_le`, and **`card_smoothUpTo_card_primeFactors_le`** :
`#{s ≤ Y : z-smooth, ω s ≤ k} ≤ ∑_{j≤k} C(π(z)·log₂ Y, j)`, by mapping `s` to its set of maximal
prime powers (injective, since their product is `s`).

**`OmegaTail.lean`**
- **`card_omega_le_le_sum`** : fibring `Ioc a b` over the smooth part,
  `#{n ∈ (a,b] : ω n ≤ k} ≤ ∑_{s z-smooth ≤ b, ω s ≤ k} #{m ∈ (a/s, b/s] : P⁻(m) > z}`;
- `roughDensityBound`, `smoothTiltBound`, `smoothIndexBound`;
- **`card_omega_le_le`** — the assembled lower-tail bound:

```text
#{n ∈ (a,b] : ω n ≤ k}
  ≤ (b−a)·roughDensityBound z r λ·smoothTiltBound z k t
    + (roughDensityBound z r λ + #{d ∣ z# : ω d ≤ r})·smoothIndexBound z b k
```
for every `a ≤ b`, `2 ≤ z`, even `r`, `λ ≥ 1`, `0 < t ≤ 1`.

All built, wired, axiom-clean.  This is `(7)` in structural form: the first term carries the
Chernoff rate (choose `t = k/∑_{p≤z}1/p` to make `roughDensityBound·smoothTiltBound` equal
`(log z)^{−I(c)}` up to constants), the second is the sieve error, controlled because
`smoothIndexBound` is `X^{o(1)}` when `log z ≍ log X/log log X` and `k ≍ log log X`.

Remaining: the parameter instantiation turning `card_omega_le_le` into `(7)`, the mirror argument
for the upper tail `(8)`, and `(9)`.

### Upper tail `(8)` — route found (2026-08-03)

The smooth/rough fibring that proved `(7)` **cannot** prove `(8)`: its error term is
`(sieve error) × #{index set}`, and for the upper tail the index set
`{σ z-smooth ≤ b : ω σ ≥ k'}` has no useful cardinality bound (unlike `ω σ ≤ k`, which
`card_smoothUpTo_card_primeFactors_le` bounds).  Several natural repairs were checked and all fail
on the same `+1`-per-divisor error:

- plain divisor choice (`∑_{ω d = k'} #{n : d ∣ n}`) has no `1/log z` saving and is worse than
  trivial already at `c₊ = 1.5`;
- the untruncated MGF `∑_n u^{ω_{≤z} n}` has error `u^{π(z)}`;
- truncating the MGF from above is the wrong direction for `u > 1` (all terms are nonnegative);
- second/higher moments give only `(log X)^{-(c-1)²/e}`, and the `2m`-th moment needs the same
  divisor sums anyway;
- transferring `ω → ω_{≤z}` with the worst-case bound `ω_{>z}(n) ≤ log b / log z` loses
  `≍ log log X`, i.e. everything.

**The route that works** splits at a threshold `J` and uses two different devices.

**(8a) Small primes — truncated factorial-moment (Bonferroni) MGF.**  For `u ≥ 1` and any `w`,

```text
[w ≥ k'] ≤ u^{-k'} ∑_{i ≤ k'} C(w, i) (u-1)^i,
```
because `C(w,i) ≥ C(k',i)` for `w ≥ k'` makes the truncated sum at least `u^{k'}`, and every term
is nonnegative.  Summing over `n ∈ (a,b]` and using
`∑_{n ∈ (a,b]} C(ω_{≤z} n, i) = ∑_{d ∣ z#, ω d = i} #{n ∈ (a,b] : d ∣ n}` gives

```text
#{n ∈ (a,b] : ω_{≤z} n ≥ k'}
  ≤ u^{-k'} (b-a) ∏_{p ≤ z}(1 + (u-1)/p) + u^{-k'} ∑_{i ≤ k'} (u-1)^i C(π z, i),
```
whose main term is the **sharp** Chernoff factor `exp(-S·I(c))` at `u = k'/S`, and whose error is
`#truncDivisors (z#) k'`-shaped, hence `X^{o(1)}` for `log z ≍ log X / log log X`.
The same device reproves `(7)` directly (with `t ≤ 1`, using the *even* Bonferroni inequality
already in `TruncatedMoebius.lean`), with no fibring and no sieve.

**(8b) Large primes — geometric-mean divisor trick.**  If `ω_{>z} n ≥ 4J` then the product `d` of
the `J` smallest prime factors of `n` exceeding `z` satisfies `d ≤ n^{J/ω_{>z} n} ≤ b^{1/4}`,
because the geometric mean of the `J` smallest is at most the geometric mean of all.  Hence

```text
#{n ∈ (a,b] : ω_{>z} n ≥ 4J} ≤ (b-a) · L^J / J! + b^{1/4},
    L = ∑_{z < p ≤ b} 1/p ≍ log log log X.
```
Choosing `J ≍ log log X / log log log X` makes `L^J/J! ≤ (log X)^{-I(c)}` while
`4J = o(log log X)`, so the transfer `ω n ≥ k ⟹ ω_{≤z} n ≥ k - 4J` costs nothing in the
exponent.  The `b^{1/4}` error is far below `H = X^{1/2+o(1)}`.

This is the plan for the next stages; `(9)` then follows from `(7)` and `(8)`.

### Factorial-moment layer landed (2026-08-03) — `Sieve/OmegaMGF.lean`

Built, wired, axiom-clean:

- **`card_divisors_filter_card_primeFactors_eq`** : for squarefree `m`,
  `#{d ∣ m : ω d = i} = C(ω m, i)` — via the bijection `d ↦ d.primeFactors` onto
  `m.primeFactors.powersetCard i`;
- `omegaSmall z n = ω (gcd n z#)` — the number of primes `≤ z` dividing `n`;
- `levelDivisors z i = {d ∣ z# : ω d = i}`, `levelDivisors_gcd`;
- **`sum_choose_omegaSmall_eq`** — the factorial moment identity:
  `∑_{n ∈ (a,b]} C(ω_{≤z} n, i) = ∑_{d ∣ z#, ω d = i} #{n ∈ (a,b] : d ∣ n}`;
- `binomialPartial x w r = ∑_{i ≤ r} C(w,i)(−x)^i`, with `binomialPartial_zero`,
  `binomialPartial_succ` (the Pascal recursion
  `B(w+1, r+1) = B(w, r+1) − x·B(w, r)`), and
- **`binomialPartial_sign`** : `0 ≤ (−1)^r (binomialPartial x w r − (1−x)^w)` for `x ∈ [0,1]` —
  the Bonferroni inequalities for the binomial expansion, both parities at once, by induction on
  `w` with `r` quantified inside (the even and odd cases feed each other through the Pascal
  recursion).

These are the two halves of `(8a)`: the moment identity turns `∑_n C(ω_{≤z} n, i)` into a divisor
sum whose error is one unit per divisor of `z#` at level `i`, and `binomialPartial_sign` supplies
the one-sided truncation needed to assemble the moments into an indicator bound.

Remaining: the indicator lemmas (`[w ≥ k'] ≤ u^{−k'} ∑_{i≤k'} C(w,i)(u−1)^i` for `u ≥ 1`, and its
`t ≤ 1` mirror from `binomialPartial_sign`), their combination with the moment identity into the
two `ω_{≤z}` tail bounds, then `(8b)` (the geometric-mean divisor trick for `ω_{>z}`) and `(9)`.

### `(8a)` complete and `(8b)`'s core landed (2026-08-03)

**`Sieve/OmegaMGF.lean` (extended)** — both tails of the small-prime count, sharp:

- `indicator_mul_pow_le_sum_choose` : for `u ≥ 1`,
  `[k ≤ w]·u^k ≤ ∑_{i≤k} C(w,i)(u−1)^i` — from `C(k,i) ≤ C(w,i)` and the binomial theorem
  `u^k = ∑_{i≤k} C(k,i)(u−1)^i`;
- `indicator_mul_pow_le_binomialPartial` : for `0 < t ≤ 1` and even `r`,
  `[w ≤ k]·t^k ≤ binomialPartial (1−t) w r` — from `binomialPartial_sign` and `t^k ≤ t^w`;
- `abs_sum_choose_omegaSmall_sub_le` : `|∑_n C(ω_{≤z}n, i) − (b−a)∑_{d ∈ levelDivisors} 1/d|
  ≤ #levelDivisors z i`;
- **`card_omegaSmall_ge_mul_pow_le`** :
  `#{n ∈ (a,b] : k ≤ ω_{≤z} n}·u^k ≤ (b−a)·∑_{i≤k}(u−1)^i e_i + ∑_{i≤k}(u−1)^i·#levelDivisors z i`;
- **`card_omegaSmall_le_mul_pow_le`** :
  `#{n ∈ (a,b] : ω_{≤z} n ≤ k}·t^k ≤ (b−a)·∑_{i≤r}(t−1)^i e_i + ∑_{i≤r} #levelDivisors z i`
  for even `r`.

Both carry the **sharp** Chernoff shape: optimising `u` (resp. `t`) at `k/∑_{p≤z}1/p` makes the
main term `exp(−S·I(c))`, and the error is one unit per level divisor — bounded by
`#truncDivisors (z#) k`, hence `X^{o(1)}` at `log z ≍ log X / log log X`.

**`Sieve/GeometricMeanDivisor.lean`** — the core of `(8b)`:

- **`prod_pow_card_le_prod_pow_card`** : if every element of `T` is at most every element of
  `S \ T` then `(∏_T p)^{#S} ≤ (∏_S p)^{#T}` — the integral geometric-mean inequality, proved by
  the two-sided product comparison `(∏_T p)^{#(S\T)} ≤ (∏_{S\T} q)^{#T}`;
- **`pow_prod_le_of_card_mul_le`** : if additionally `c·#T ≤ #S` and `∏_S p ≤ n`, then
  `(∏_T p)^c ≤ n`.

So once `n` has at least `c·J` prime factors above the cut, the product of the `J` smallest of them
is at most `n^{1/c}` — which is exactly what keeps the `(8b)` divisor range below `b^{1/4}`.

All built, wired, axiom-clean.  Remaining: instantiate `S = {p ∈ n.primeFactors | z < p}` with `T`
its `J` smallest elements, count `#{n : ω_{>z} n ≥ 4J}` by the resulting small divisors, combine
with `(8a)` for `(8)`, and conclude `(9)`.

### `(8b)` landed (2026-08-03) — `Sieve/SmallestPart.lean`

- `smallestPart S J` — the `J` smallest elements of a finite set of naturals, defined by truncating
  `Finset.sort`; `smallestPart_subset`, `card_smallestPart` (`= min J #S`), and
  **`smallestPart_le`** (`∀ p ∈ T, ∀ q ∈ S \ T, p ≤ q`, from `List.pairwise_append` applied to
  `take ++ drop`);
- **`exists_small_divisor`** : if `c·J ≤ #{p ∣ n : z < p}` and `n ≠ 0`, there is a squarefree
  `d ∣ n` with `ω d = J`, every prime factor above `z`, and **`d^c ≤ n`** — the product of the `J`
  smallest large prime factors, with the size bound coming from
  `pow_prod_le_of_card_mul_le`;
- `bigDivisors z b J c` and `bigDivisors_subset_Icc` : such divisors are confined to
  `Icc 1 D` whenever `b < (D+1)^c`, i.e. to a `c`-th root range;
- **`card_omegaBig_ge_le_sum`** : the covering
  `#{n ∈ (a,b] : c·J ≤ ω_{>z} n} ≤ ∑_{d ∈ bigDivisors} #{n ∈ (a,b] : d ∣ n}`;
- **`card_omegaBig_ge_le`** : its quantitative form
  `≤ (b−a)·∑_{d ∈ bigDivisors} 1/d + D`.

Built, wired, axiom-clean.  Both halves of `(8)` now exist as unconditional Lean theorems: `(8a)`
(`card_omegaSmall_ge_mul_pow_le`) with the sharp Chernoff main term, and `(8b)`
(`card_omegaBig_ge_le`) with the divisor range confined to `b^{1/c}` so that the `D` error is
negligible.

Remaining: bound `∑_{d ∈ bigDivisors} 1/d` by the tilted Euler product over the primes in `(z,b]`
(the same `prod_one_add_mul_le_exp` device), then instantiate parameters to combine `(8a)` and
`(8b)` into `(8)`, and conclude `(9)`.
