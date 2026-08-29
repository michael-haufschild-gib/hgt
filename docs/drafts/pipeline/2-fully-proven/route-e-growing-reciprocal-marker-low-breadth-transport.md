# Route E growing reciprocal-marker capacity and low-breadth transport

- **ID:** `ROUTE-E-GROWING-RECIPROCAL-MARKER-002`
- **Stage:** 2-fully-proven
- **Type:** NEW SYNTHESIS / GROWING-BLOCK DISTINCT-TARGET THEOREM
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** finite window, sign reversal, marker decoding and finite-family distinctness in
  `MobiusReciprocalMarkerPrimeCapacity.lean`; the window prime count `(11)`/`(28)`, the reciprocal
  fibre bound `(25)`-`(26)`, the *truncated* short-interval squarefree count `(19)`/`(21)` with the
  density `6/pi^2`, and the averaged truncation tail `(22)`-`(23)` are formalized unconditionally in
  `Sieve/PrimeWindow.lean`, `Sieve/ReciprocalFibre.lean`, `Sieve/InverseSquareTail.lean`,
  `Sieve/SquarefreeCount.lean`, `Sieve/AveragedSquarefreeTail.lean`; the squarefree identity `(20)`
  is formalized in `Sieve/SquarefreeIndicatorZero.lean` and the truncated-to-true bridge in
  `Sieve/SquarefreeTruncationDefect.lean`; the sign-count identity and
  its conclusion are in `Sieve/MoebiusSignCount.lean`, `Sieve/MoebiusSignLower.lean`; the
  short-interval variance layer (`Sieve/Window*.lean`, `Sieve/RealWindow*.lean`,
  `Sieve/CorrelationToVariance.lean`) proves `(15)` *equivalent* to cancellation in the shifted
  Moebius correlations at the `L-1` shifts `h < L`, and rules out both non-arithmetic routes to it; the two-variable squarefree sieve
  (`Sieve/ShiftedCongruenceCount.lean`, `Sieve/JointCongruence*.lean`,
  `Sieve/TruncatedPair*.lean`) evaluates the shifted `mu^2` correlation unconditionally;
  step 1 is the single theorem `Sieve.card_le_good_add_correlation`, whose only non-elementary
  hypothesis is a bound on the `L-1` shifted Moebius correlations `sum_n mu(n)mu(n+h)`; the
  mean-square input `(15)` is *derived* from it, not assumed, and the prime number theorem is not
  used at all (the marker supply comes from Mertens via `Sieve/PrimeWindow.lean`); **update (2026-08-18):** the Moebius short-interval mean square is now an
  unconditional theorem of this corpus (`Sieve/MoebiusMeanSquare.averagedMeanSquare_moebius`,
  window `exp((log X)^{99/100})`) in the *fibre* normalization; this card, like
  `ROUTE-E-RECIPROCAL-MARKER-HALL-001`, needs the *integer-start* form
  `DyadicTranslates.dyadicMeanSquare`, and the one missing input for that is the low-frequency
  contour bound for the Ramare-weighted cofactor polynomial --- see the Hall-law card for the
  exact reduction

## Result

Let \(h=h(X)\), \(H=\sqrt Xh\), and suppose
\[
 \log h=o(\log X).
\tag{1}
\]
Suppose there is an auxiliary \(w=w(X)\) such that
\[
 \sqrt{\log X}(\log\log X)^2=o(w),\qquad
 w=o(\log h).
\tag{2}
\]
For either sign \(\sigma\in\{-1,+1\}\), define
\[
 T_\sigma(X,H)=
 \{n\in\mathbb N:X<n\le X+H,\ \mu(n)=\sigma\}.
\tag{3}
\]
Then an absolute \(c>0\) satisfies
\[
 \#T_\sigma(X,H)
 \ge
 c\,{H\log h\over\log X}
\tag{4}
\]
for both signs and all sufficiently large \(X\).

Every target counted in `(4)` has a uniquely decoded representation
\[
 n=ap,\qquad p>\sqrt X>a,\qquad \mu(a)=-\sigma,
\tag{5}
\]
where \(p\) is prime.  Thus `(4)` counts distinct physical integers, not
factorizations.

The useful near-maximal subpower schedule is
\[
 h(X)=\exp\!\left({\log X\over\log\log X}\right),
 \qquad
 w(X)=(\log X)^{2/3}.
\tag{6}
\]
It gives
\[
 H=X^{1/2+o(1)},\qquad
 \#T_\sigma(X,H)\gg {H\over\log\log X}.
\tag{7}
\]
This improves the fixed-block law \(C H/\log X\) by the growing factor
\(\asymp\log h\).

As a second consequence, fix \(0<c_0<1\) and put
\[
 {\cal L}_{c_0}(X,H)=
 \{n:X<n\le X+H,\ \mu(n)\ne0,\
       \omega(n)\le c_0\log\log X\}.
\tag{8}
\]
For the schedule `(6)`, every sufficiently large \(H\)-cell admits disjoint
opposite-Möbius-sign edges, of displacement at most \(H\), covering every
vertex in \({\cal L}_{c_0}(X,H)\).  The other endpoint of every edge can be
chosen outside \({\cal L}_{c_0}(X,H)\).  Across a dyadic shell, the aggregate
first-order Gibbs cost is \(X^{1/2+o(1)}\).

Therefore every fixed lower deviation from normal Wold breadth is closed
unconditionally.  Route E's composite capacity problem is no longer the
whole positive-density composite sector: it is confined to
\[
 \omega(n)\ge c_0\log\log n
\quad\text{for every fixed }c_0<1,
\tag{9}
\]
together with its co-moving seam flux.

## Proof of growing-block capacity

Put \(N=\sqrt X\), and define
\[
 K=
 \left\lfloor{\log h-w\over\log2}\right\rfloor-4.
\tag{10}
\]
For \(1\le k\le K\), use marker primes
\[
 2^kN<p\le2^{k+1}N,
\tag{11}
\]
reciprocal starts and cofactor lengths
\[
 t_p=\left\lfloor{X\over p}\right\rfloor,\qquad
 L_k=\left\lfloor{h\over2^{k+2}}\right\rfloor.
\tag{12}
\]
The start scale is
\[
 A_k\asymp {N\over2^k}.
\tag{13}
\]
Uniformly for \(k\le K\),
\[
 \log L_k\ge w+O(1),\qquad
 \log A_k
 \ge \tfrac12\log X-\log h+w+O(1)
 =(\tfrac12+o(1))\log X.
\tag{14}
\]

Menon's Theorem 1.1, with the Möbius analogue explicitly noted after its
statement, gives
\[
 {1\over A_k}\int_{A_k}^{2A_k}
 \left|
 {1\over L_k}\sum_{x<n\le x+L_k}\mu(n)
 \right|^2dx
 \ll R_k,
\tag{15}
\]
where
\[
 R_k=
 {(\log\log L_k)^2\over(\log L_k)^2}
 +{(\log\log A_k)^4\over(\log A_k)^2}.
\tag{16}
\]
Equations `(2)` and `(14)` imply, uniformly in every retained block,
\[
 R_k\log X=o(1).
\tag{17}
\]
Since the short sum is constant between consecutive integral starts up to
two endpoint terms, Markov's inequality shows that only
\[
 o(A_k/\log X)
\tag{18}
\]
integer starts have a fixed positive-proportion Möbius imbalance.

The squarefree count is controlled independently.  Write
\[
 Q(t,L)=\sum_{t<n\le t+L}\mu^2(n)
\tag{19}
\]
and truncate
\[
 \mu^2(n)=\sum_{d^2\mid n}\mu(d)
\tag{20}
\]
at \(R=\lfloor\sqrt L\rfloor\).  Uniformly in \(t\),
\[
 \sum_{t<n\le t+L}\sum_{\substack{d^2\mid n\\d\le R}}\mu(d)
 ={6\over\pi^2}L+O(\sqrt L).
\tag{21}
\]
Summing the omitted absolute tail over \(t\asymp A\) gives
\[
 \sum_{t\asymp A}
 \sum_{t<n\le t+L}
 \sum_{\substack{d>\sqrt L\\d^2\mid n}}1
 \ll {AL\over\sqrt L}+L\sqrt A.
\tag{22}
\]
Consequently only
\[
 O(A/\sqrt L+\sqrt A)
\tag{23}
\]
starts fail a fixed positive squarefree-density lower bound.  From `(14)`,
`(23)` is \(o(A_k/\log X)\), uniformly for \(k\le K\).

Combining `(18)` and `(23)`, all but \(o(A_k/\log X)\) starts contain
\[
 \gg L_k
\tag{24}
\]
cofactors of each nonzero Möbius sign.

The reciprocal map is not bounded-to-one uniformly in \(k\), and this is
where the growing-block audit differs from the fixed-\(K\) proof.  If
\(\lfloor X/p\rfloor=t\), then
\[
 {X\over t+1}<p\le {X\over t}.
\tag{25}
\]
For \(t\asymp A_k\), its integral fibre has size
\[
 {X\over t(t+1)}+1\ll4^k.
\tag{26}
\]
Thus the bad starts discard at most
\[
 4^k\,o(A_k/\log X)
 =o(2^kN/\log X)
\tag{27}
\]
markers.  Chebyshev's dyadic prime lower bound, uniformly over the growing
range `(11)`, leaves
\[
 \gg {2^kN\over\log X}
\tag{28}
\]
good markers.

For each good \(p\), choose every \(a\) of the required sign in
\((t_p,t_p+L_k]\).  The product satisfies
\[
 X<ap\le X+pL_k\le X+\tfrac12Nh<X+H.
\tag{29}
\]
Moreover \(a<N<p\) for all retained blocks and large \(X\).  Hence
\((a,p)=1\) and \(\mu(ap)=-\mu(a)\).

If \(ap=a'p'\) are two constructed products, the prime \(p>N>a'\) divides
\(a'p'\).  It cannot divide \(a'\), so \(p=p'\), and then \(a=a'\).
This also separates different marker blocks.  Combining `(24)` and `(28)`,
block \(k\) contributes
\[
 \gg {2^kN\over\log X}\,{h\over2^k}
 \gg {H\over\log X}
\tag{30}
\]
distinct targets of each sign.  Finally \(K\asymp\log h\), so summing `(30)`
proves `(4)`.

## Proof of low-breadth transport

Let
\[
 I(c)=1-c+c\log c>0\qquad(0<c<1).
\tag{31}
\]
Apply Shiu's short-interval upper bound to the nonnegative multiplicative
function \(z^{\omega(n)}\), where \(0<z<1\).  Since
\(H\ge X^{1/2}\), uniformly in an \(H\)-cell,
\[
 \sum_{X<n\le X+H}z^{\omega(n)}
 \ll_z H(\log X)^{z-1}.
\tag{32}
\]
For \(\omega(n)\le c_0\log\log X\),
\[
 1\le z^{\omega(n)-c_0\log\log X}.
\tag{33}
\]
Taking \(z=c_0\) in `(32)` therefore gives the Chernoff lower-tail bound
\[
 \#{\cal L}_{c_0}(X,H)
 \ll_{c_0}
 H(\log X)^{-I(c_0)}.
\tag{34}
\]
The right side is \(o(H/\log\log X)\).  By `(7)`, each sign-specific
reciprocal-marker target set is therefore larger than
\({\cal L}_{c_0}(X,H)\) by an unbounded factor.

Delete all low-breadth vertices from both target-sign sets.  The remaining
positive and negative target sets still each have cardinality
\(\gg H/\log\log X\).  Match every positive low-breadth source to a distinct
remaining negative target, and every negative low-breadth source to a
distinct remaining positive target.  The two matchings are disjoint because
their target signs differ, and no target is a source because of the deletion.
Every edge stays inside the same \(H\)-cell.

For \(x\asymp X^{-1}\), one opposite-sign edge \(\{m,n\}\) costs
\[
 |e^{-xm}-e^{-xn}|
 \le x|m-n|e^{-x\min(m,n)}
 \ll xH.
\tag{35}
\]
There are \(O(X)\) edges across a dyadic shell, so their total is
\[
 O(xXH)=O(H)=X^{1/2+o(1)}.
\tag{36}
\]
The terminal partial cell has \(O(H)\) absolute mass and obeys the same
bound.  This proves the transport claim.

## Hostile audit

1. **This does not prove RH.**  The matching proved on this card covers the strict
   lower-tail breadth sector `(9)`.  The later two-sided extension
   `route-e-two-sided-off-normal-wold-breadth-transport.md` also removes fixed upper deviations,
   but the central normal-order sector still has positive density.
2. **Growing fibres were charged.**  The map
   \(p\mapsto\lfloor X/p\rfloor\) has size \(O(4^k)\), not \(O(1)\), in a
   growing block.  Equation `(27)` is the required cancellation with the
   cofactor scale \(A_k\asymp2^{-k}N\).
3. **The shortest cofactor interval remains long.**  The subtraction of
   \(w\) in `(10)` is essential.  Taking every block through
   \(L_k\asymp1\) would invalidate Menon's estimate and recreate the
   unresolved dual prime-interval regime.
4. **The count is physical.**  The marker prime is larger than every
   cofactor, so unique factorization gives literal injectivity.  No
   representation weights or Boolean divisor normalization occur.
5. **Targets do not double-use low-breadth sources.**  All low-breadth
   vertices are removed from target reservoirs before the two sign
   matchings.
6. **The transport cost is first order but admissible.**  Its displacement
   is \(H=X^{1/2+o(1)}\); no rectangle cancellation is being claimed for
   this sector.
7. **No fixed-\(K\) asymptotic was silently made uniform.**  Menon's bound
   is uniform in \(10\le L\le A\); the prime input is the uniform Chebyshev
   lower bound; all \(k\)-dependence is explicit in `(14)`, `(26)`, and
   `(27)`.

## Novelty audit

Searches covered Menon's 2026 mean-square theorem, Matomäki--Radziwiłł
short-interval sign work, Matomäki--Teräväinen all-interval Möbius work,
reciprocal-prime sampling, and Möbius-sign product counts.  No located source
states the growing reciprocal-block physical target law `(4)`, the exact
fibre compensation `(26)`--`(27)`, or its Shiu lower-breadth transport
consequence `(34)`--`(36)`.

Inputs are classical or published; their combination and Route E extraction
appear new.  External priority is unverified.  The result is recorded as new
scientific synthesis, not as a closure of `OPEN-SOURCE-001`.

## Lean completion programme (opened 2026-08-03)

Corpus audit before starting.  `MobiusReciprocalMarkerPrimeCapacity.lean` already owns the finite
skeleton: `reciprocalMarker_product_mem_window` is `(29)`, `reciprocalMarker_target_sign_flip` is the
sign law of `(5)`, and `largePrimeMarker_pairProduct_injective` / `card_markerProducts_eq` are the
injectivity of `(30)`.  The `Sieve/` layer built for the two-sided card owns Mertens I and II,
Brun's pure sieve, the Selberg sieve and the Chernoff tails.  Missing were the three arithmetic
inputs of this card's own proof: the window prime count `(11)`/`(28)`, the reciprocal fibre bound
`(25)`–`(26)`, and the squarefree count `(19)`–`(23)`.

### `(11)`, `(28)` landed — `Sieve/PrimeWindow.lean`

- `sum_logDiv_bigPrimeSet` : `∑_{M<p≤N} (log p)/p = mertensA N − mertensA M`;
- `logDiv_le_of_lt` : beyond `e` the weight `(log p)/p` is maximised at the left endpoint;
- **`card_bigPrimeSet_ge`** :
  `#{p : M < p ≤ N} ≥ (log(N/M) − 2c₁)·M/log M`, with `c₁ = mertensFirstConst`;
- **`card_bigPrimeSet_ratio_ge`** : the same for a ratio window `N = QM`.

This is a Chebyshev-type lower bound with *named* constants.  Note the honest constraint it exposes:
Mertens' first theorem carries `c₁ = max(log 4, 1 + 2·logSqTailConst)`, so the bound is vacuous for a
literal dyadic block and becomes positive once the block ratio exceeds `exp(2c₁)`.  The card's
construction is unaffected — replacing base `2` by a larger fixed base changes `K ≍ log h` only by a
constant factor — but the card's `(10)` should be read with that base.

### `(25)`, `(26)` landed — `Sieve/ReciprocalFibre.lean`

- `reciprocalFibre_subset` : `⌊X/p⌋ = t` is exactly `X/(t+1) < p ≤ X/t`;
- **`card_reciprocalFibre_le`** : the fibre has at most `X/(t(t+1)) + 1` members.

Exact arithmetic, no asymptotics; this is the growing-fibre charge of hostile-audit item 2.

### `(19)`–`(21)` landed — `Sieve/InverseSquareTail.lean`, `Sieve/SquarefreeCount.lean`

- `sum_range_inv_sq_shift_le`, `summable_inv_sq_shift`, **`tsum_inv_sq_shift_le`** :
  `∑_{d > R} d^{−2} ≤ 1/R`, by the telescoping invariant `1/R − 1/(N+R)`;
- `summable_moebius_div_sq`, `squarefreeDensity := ∑_{d≥1} μ(d)/d²`;
- `abs_sum_Icc_moebius_div_sq_sub_le` : truncating the density at `R` costs at most `1/R`;
- `sum_truncated_moebius_eq` : the exact exchange
  `∑_{n∈(t,t+L]} ∑_{d≤R, d²∣n} μ(d) = ∑_{d≤R} μ(d)·#{n∈(t,t+L] : d²∣n}`;
- **`abs_truncated_squarefree_sub_le`** :
  `|∑_{n∈(t,t+L]} ∑_{d≤R, d²∣n} μ(d) − L·C| ≤ R + L/R`, **uniformly in `t`** — this is `(21)`, and at
  `R ≍ √L` the error is `O(√L)`;
- `lseries_moebius_two_eq`, **`squarefreeDensity_eq`** : `C = 6/π²`, obtained from the corpus's own
  `LSeries_moebius_eq_inv_riemannZeta` at `s = 2` together with mathlib's `riemannZeta_two`.

### `(22)`, `(23)` landed — `Sieve/AveragedSquarefreeTail.lean`

- `card_start_window_le` : an integer lies in at most `L` of the windows `(t, t+L]`;
- **`sum_card_filter_dvd_le`** : `∑_{A ≤ t < B} #{n∈(t,t+L] : m ∣ n} ≤ L·#{n∈(A,B+L] : m ∣ n}`,
  the double counting that makes the tail affordable on average;
- `sum_Icc_inv_sq_le` : the truncated inverse-square tail;
- **`sum_tail_divisor_count_le`** :
  `∑_{A ≤ t < B} ∑_{R < d ≤ M} #{n∈(t,t+L] : d²∣n} ≤ L·((B+L−A)/R + M)`,
  which at `R ≍ √L`, `M ≍ √(B+L)` is exactly `(22)`, hence `(23)`.

Built, wired into `GaloisForLFunctions/RHTower.lean`, axiom-clean (nineteen theorems, every one
`[propext, Classical.choice, Quot.sound]`).

### What remains

**Partially superseded — see "The mean square, unconditionally", "Step 1 of the Hall-law argument,
unconditionally" and, for the correct scope of that work, "Window range of the derived mean square"
at the end of this card.** A mean square of the shape `(15)` *is* now derived in this corpus from the
zero-free region, through the twisted contour argument and Gallagher's reduction, and step 1 consumes
it with no analytic hypothesis. But the derivation is only nontrivial for **long** windows,
`L ≳ N·exp(−c(log N)^{1/10})`, whereas `(15)` is applied here at `L_k/A_k ≍ h/√X = X^{−1/2+o(1)}`.
So `(15)`–`(18)` at the parameters this card needs still rest on the cited theorem; the paragraph
below remains the accurate description of that dependency.

`(15)`–`(18)` rest on Menon's 2026 mean-square theorem for Möbius in short intervals, a cited
published analytic result; nothing in mathlib or the corpus approaches it, and `(18)` is its Markov
consequence.  `(32)`/`(34)` are Shiu's bound, for which the corpus now owns an unconditional
substitute (`Sieve/RateBridge.card_omega_le_le_rate`) that is weaker by `(log log X)^{Θ(1)}` — still
enough here, since `(34)` is used only as `o(H/log log X)` and `(log X)^{−I(c₀)}(log log X)^{I(c₀)+1}`
tends to zero.  `(35)`/`(36)` are `MobiusWoldBreadthGibbsCost.abs_gibbsEdge_le` and
`sum_abs_gibbsEdge_le`.

### `(10)`–`(14)`, `(18)`, `(27)`, `(30)` landed — `MobiusReciprocalMarkerBlockCount.lean`, `MobiusReciprocalMarkerSchedule.lean`

The assembly steps, stated on the *hypotheses* a distribution theorem would supply rather than on
the theorem itself:

- `markerBlockTargets P C` — the target set of a marker family with prescribed cofactor sets;
- **`card_markerBlockTargets`** : `#targets = ∑_{p ∈ P} #(C p)` — the physical count of `(30)`,
  proved from the corpus's own `largePrimeMarker_product_injective`;
- **`markerBlockTargets_mem_window`** : every target lies in `(X, X+H]`, which is `(29)`;
- **`markerBlockTargets_sign`** : every target carries the reversed nonzero Möbius sign, `(5)`;
- **`card_markers_start_mem_le`** : the markers lost to a set `S` of bad starts number at most
  `#S · (X/(A(A+1)) + 1)` — this is `(27)`, the growing-fibre compensation, obtained by fibring the
  marker set over its reciprocal starts and applying `card_reciprocalFibre_le` to each fibre;
- **`card_large_le_of_sum_sq_le`** : Markov for a mean-square bound — `#{t : |f t| ≥ δ} ≤ R/δ²`
  whenever `∑ (f t)² ≤ R`.  This is exactly the step `(15) → (18)`, now available independently of
  which mean-square theorem supplies `R`.

Schedule bookkeeping:

- **`markerBlock_window_length_ge`** : cutting the block index at `K` with
  `K + 4 ≤ (log h − w)/log 2` forces `h/2^{k+2} ≥ 4 e^w` for every retained `k`.  This is the `(14)`
  lower bound on `log L_k`, and it is exactly where the subtraction of `w` in `(10)` earns its keep
  (hostile-audit item 3);
- **`markerBlock_start_ge`** : with `X = N²` and `p ≤ 2^{k+1}N`, the start `⌊X/p⌋` is at least
  `N/2^{k+1}` — the `(13)`/`(14)` lower bound on `A_k`, exact in natural division.

Built, wired, axiom-clean (seven theorems; `markerBlock_start_ge` needs only
`[propext, Quot.sound]`).

### Status

**Partially superseded.** A `(15)`-shaped mean square is now derived in-corpus from the zero-free
region (see the sections at the end of this card), but only in the long-window range
`L ≳ N·exp(−c(log N)^{1/10})`, which does not contain this card's parameters. The paragraph below
remains accurate for `(15)`–`(17)` as used here.

Everything this card proves is now an unconditional Lean theorem except `(15)`–`(17)`, which are
Menon's 2026 mean-square theorem for Möbius in short intervals — a cited published analytic result.
Its consequence `(18)` is formalized as a general lemma, so the moment that estimate is available in
any form the chain closes with no further work: `card_large_le_of_sum_sq_le` turns it into a
bad-start count, `card_markers_start_mem_le` charges the discard, `card_bigPrimeSet_ratio_ge` supplies
the surviving markers, `abs_truncated_squarefree_sub_le` and `sum_tail_divisor_count_le` supply the
cofactors, and `card_markerBlockTargets` counts the targets.

### `(10)`–`(11)` also landed — `Sieve/SharedPrimeTail.lean`

The large-prime tail of this card has the same shape as the coprime-pair card's, and is now shared:
`card_pair_dvd_le` gives the two-factor bound `(√x/p + 1)(h/p + 1)`, and `sum_pair_tail_le` sums it
over a prime window into `ℓ₁ℓ₂/P + (ℓ₁ + ℓ₂)·mertensS Q + Q` — the inverse-square, Mertens and
Chebyshev pieces separated.

### Toward the external input — `Sieve/RamareWeight.lean` (2026-08-03)

All three Route E cards in this folder bottom out on the same external theorem (Matomäki–Radziwiłł
2016 Theorem 2, or Menon's 2026 refinement).  Rather than restate it as a hypothesis, the corpus is
being built toward it.  The first step of that proof — the device that manufactures a bilinear sum
out of a one-dimensional one — is now unconditional:

- `primeFactorsIn P n` — the designated primes dividing `n`;
- **`sum_inv_card_primeFactorsIn`** : Ramaré's identity `∑_{p ∈ P, p ∣ n} 1/ω_P(n) = 1`;
- **`sum_eq_sum_ramare`** :
  `∑_{n ∈ S} f(n) = ∑_{p ∈ P} ∑_{n ∈ S, p ∣ n} f(n)/ω_P(n)`, exact, for any `S` whose members all
  carry a designated factor;
- `sum_div_image` : reindexing a sum over multiples of `p` by the cofactor;
- **`sum_eq_sum_ramare_bilinear`** : the same identity written over pairs `(p, m)` with `n = pm`;
- **`sum_eq_ramare_add_rough`** : the *complete* decomposition, with no hypothesis at all —
  `∑_{n ∈ S} f = (bilinear part) + ∑_{n ∈ S, no designated factor} f`.
  The second term is the rough remainder, which the corpus sieve already bounds
  (`Sieve/RoughCount.card_rough_Ioc_le`, `Sieve/DivisorSquareSum.card_coprime_Ioc_le_explicit`).

Built, wired, axiom-clean (six theorems).  The weight `1/ω_P` is exactly what stops an integer with
several designated factors being counted several times; the identity carries no error term.

### Turán–Kubilius on an interval — `Sieve/TuranKubilius.lean` (2026-08-03)

The second reusable instrument on the road to the external theorem, and absent from mathlib: the
variance of the small-prime count, uniform over intervals.

- `indDvd`, `centredInd`, `omegaCount` — the divisibility indicator, its centring `1_{p∣n} - 1/p`,
  and `ω_z(n) = #{p ≤ z : p ∣ n}`;
- `sum_centredInd_eq` : `ω_z(n) - ∑_{p ≤ z} 1/p = ∑_{p ≤ z}(1_{p∣n} - 1/p)`;
- `sum_indDvd_Ioc`, `sum_indDvd_mul_Ioc` — interval sums of one and two indicators as multiple
  counts;
- **`abs_sum_centredInd_mul_le`** : *off-diagonal pairs cancel*.  For distinct primes the main terms
  cancel identically — `1_{p∣n}1_{q∣n} = 1_{pq∣n}` and the archimedean prediction for `pq` is the
  product of the two predictions — leaving `|∑_n| ≤ 2`;
- `sum_centredInd_sq_le` : a diagonal pair contributes at most `(b-a)/p + 1`;
- **`sum_omegaCount_variance_le`** :
  `∑_{n ∈ (a,b]} (ω_z(n) - ∑_{p ≤ z} 1/p)² ≤ (b-a)·∑_{p ≤ z} 1/p + π(z) + 2π(z)²`.

Built, wired, axiom-clean (seven theorems).  The only arithmetic input is the interval multiple
count `abs_card_filter_dvd_Ioc_sub_lt`; there is no elementary-symmetric-function bookkeeping and no
distribution theorem.  The identical cancellation of main terms across an off-diagonal pair is the
mechanism a mean-square estimate for a multiplicative function has to reproduce, and having it
unconditional fixes the shape of the constants the external theorem must beat.

### Duality principle — `Sieve/LargeSieveDuality.lean` (2026-08-03)

First piece of the harmonic-analysis half.  A large sieve inequality has two shapes: the *Bessel*
form `∑_r |⟪φ_r, a⟫|² ≤ Δ‖a‖²`, and the *bilinear* form `‖∑_r c_r φ_r‖² ≤ Δ ∑_r |c_r|²`.  The
analytic large sieve is proved in the first shape (for exponential sums at well-spaced points) and
applied in the second (to Dirichlet polynomials).

- **`norm_sum_smul_sq_le_of_bessel`** : the Bessel form implies the bilinear form, in any inner
  product space and for any finite family.

- **`sum_norm_inner_sq_le_of_bilinear`** : the converse, so the two shapes are equivalent;
- `conj_mul_self` : the scalar identity `conj z · z = ‖z‖²` the converse needs.

Built, wired, axiom-clean.  Each direction is one application of Cauchy–Schwarz followed by
dividing by the quantity being bounded; nothing analytic enters, and no hypothesis beyond `0 ≤ Δ`.

### Almost orthogonality — `Sieve/AlmostOrthogonality.lean` (2026-08-03)

The supplier that feeds the duality principle.  A family need not be orthogonal: it behaves like one
as soon as its Gram matrix has small rows.

- `norm_inner_symm` : the Gram matrix is Hermitian, so `|⟪x,y⟫| = |⟪y,x⟫|`;
- `inner_sum_smul_sum_smul` : the energy of a combination expanded over the Gram matrix;
- **`norm_sum_smul_sq_le_of_schur`** :
  `‖∑_r c_r φ_r‖² ≤ (max_r ∑_t |⟪φ_r, φ_t⟫|) ∑_r |c_r|²`.
  The proof splits the Gram double sum by `|c_r||c_t| ≤ (|c_r|² + |c_t|²)/2` into a row piece and a
  column piece; Hermitian symmetry makes both the same bound;
- **`sum_norm_inner_sq_le_of_schur`** : the Bessel form, obtained by composing with
  `LargeSieveDuality.sum_norm_inner_sq_le_of_bilinear`.

Built, wired, axiom-clean (four theorems).  This is why a large sieve inequality is *formal* once
the Gram rows are bounded: the analytic work is confined to estimating `∑_t |⟪φ_r, φ_t⟫|`, and
everything after it — both shapes of the inequality — now exists unconditionally in the corpus.  An
exactly orthogonal family recovers Bessel's inequality with `Δ = max_r ‖φ_r‖²`, the diagonal being
included in the row sum.

### Geometric sum bound — `Sieve/GeometricSumBound.lean` (2026-08-03)

The elementary input behind every Gram-row estimate for exponential families.

- **`norm_geom_sum_le`** : `‖∑_{n < N} ζ^n‖ ≤ 2/‖ζ − 1‖` whenever `‖ζ‖ ≤ 1` and `ζ ≠ 1` —
  *uniform in the length* `N`, from the closed form `(ζ^N − 1)/(ζ − 1)` and `‖ζ^N‖ ≤ 1`;
- `norm_geom_sum_Ico_le` : the same on any interval of indices, since shifting multiplies by a
  factor of modulus at most one;
- `sum_conj_pow_mul_pow` : the correlation of two exponential rows is a geometric sum in their
  quotient, `∑_n conj(ξ^n) η^n = ∑_n (conj(ξ)η)^n`;
- **`norm_sum_conj_pow_mul_pow_le`** : hence two distinct unimodular frequencies correlate at most
  like the reciprocal of their separation.

Built, wired, axiom-clean (four theorems).  Combined with `Sieve/AlmostOrthogonality.lean` this
gives a large sieve inequality directly: the diagonal Gram entry is `N`, each off-diagonal entry is
at most `2/‖ξ_r^{-1}ξ_t − 1‖`, and the row sum over `δ`-separated frequencies is
`N + O(δ^{-1} log δ^{-1})`.  That is the *weak* large sieve — the sharp constant `N + δ^{-1}` needs
Montgomery–Vaughan's refinement of Hilbert's inequality, which is a separate build.

### Gram rows of a separated frequency family — `Sieve/FrequencyGramRow.lean` (2026-08-03)

- `sum_conj_pow_mul_pow_self`, `norm_sum_conj_pow_mul_pow_self` : the diagonal Gram entry of a
  unimodular frequency is exactly the length `N`, since `conj(ξ)ξ = ‖ξ‖² = 1`;
- **`gram_row_le`** :
  `∑_t ‖∑_{n<N} conj(ξ_r)^n ξ_t^n‖ ≤ N + ∑_{t ≠ r} 2/‖conj(ξ_r)ξ_t − 1‖`.

Built, wired, axiom-clean.  This is the *only* analytic input a large sieve inequality needs:
`AlmostOrthogonality.norm_sum_smul_sq_le_of_schur` converts a row bound into the bilinear
inequality, and `LargeSieveDuality.sum_norm_inner_sq_le_of_bilinear` converts that into the Bessel
form.  Both are already unconditional in the corpus, so the chain

  frequency separation ⟶ Gram row bound ⟶ bilinear large sieve ⟶ Bessel large sieve

is now complete except for instantiating the abstract family as the exponential rows in
`EuclideanSpace ℂ (Fin N)`, which is plumbing rather than mathematics.

The residual `log` loss against the sharp constant `N + δ^{-1}` sits entirely in the harmonic sum
`∑_{t ≠ r} ‖conj(ξ_r)ξ_t − 1‖^{-1}` over `δ`-separated frequencies — not in any step above.
Removing it is exactly Montgomery–Vaughan's refinement of Hilbert's inequality, for the *Toeplitz*
kernel `1/(m−n)`; the corpus's `HTGeometry/HilbertMatrixNormBound.lean` proves `‖H‖ ≤ π` for the
*Hankel* kernel `1/(m+n+1)` and does not supply it.

### The large sieve inequality, weak form — `Sieve/LargeSieveWeak.lean` (2026-08-03)

The chain is now a single stated theorem, not a set of pieces.

- `expRow N ξ` — the exponential row `n ↦ ξ^n`, `n < N`, in `EuclideanSpace ℂ (Fin N)`;
- `inner_expRow` : its Gram entry is the truncated geometric correlation;
- `expRow_gram_row_le` : the Gram rows of a separated unimodular family;
- **`largeSieve_bilinear`** : `‖∑_r c_r φ_r‖² ≤ Δ ∑_r |c_r|²`;
- **`largeSieve_bessel`** : `∑_r |⟪φ_r, a⟫|² ≤ Δ ‖a‖²`;

for pairwise-distinct unimodular frequencies and any `Δ` dominating every
`N + ∑_{t ≠ r} 2/‖conj(ξ_r)ξ_t − 1‖`.

Built, wired, axiom-clean (four theorems).  For `δ`-separated frequencies the admissible `Δ` is
`N + O(δ^{-1} log δ^{-1})`.

**This is the weak form, and the qualification is not cosmetic.**  The sharp constant `N + δ^{-1}`
is what the Matomäki–Radziwiłł argument consumes; the logarithm here is the harmonic sum of
reciprocal separations, and removing it is exactly Montgomery–Vaughan's refinement of Hilbert's
inequality for the *Toeplitz* kernel `1/(m−n)`.  The corpus's `HilbertMatrixNormBound.lean` proves
`‖H‖ ≤ π` for the *Hankel* kernel `1/(m+n+1)` and does not supply it.  So this module is a genuine
milestone on the road to the external theorem, not a substitute for it.

### The sharp case — `Sieve/RootsOfUnityFrequencies.lean` (2026-08-03)

At the full set of `Q`-th roots of unity the elementary route already gives the *optimal* constant,
which is a check on the whole chain rather than a new estimate.

- `norm_eq_one_of_isPrimitiveRoot`, `norm_pow_eq_one_of_isPrimitiveRoot` — roots of unity and their
  powers are unimodular;
- `sum_range_pow_eq_zero` : a full geometric sum over a nontrivial root of unity vanishes;
- `ratio_ne_one` : distinct powers of a primitive root give a nontrivial ratio;
- **`inner_expRow_root_eq_zero`**, `inner_expRow_root_self` : the exponential rows of length `Q` at
  the `Q`-th roots of unity are *exactly orthogonal*, with diagonal exactly `Q`;
- `gram_row_root_eq` : hence every Gram row is exactly `Q`;
- **`largeSieve_roots`** : `‖∑_{j<Q} c_j φ_j‖² ≤ Q ∑_j |c_j|²`.

Built, wired, axiom-clean (seven theorems).  This is the sharp constant `N + δ^{-1}` at `N = Q`,
`δ = 1/Q`, with no logarithmic loss — `LargeSieveWeak.lean` specialises here to an equality-sharp
inequality, confirming that the loss in the general case is genuinely the harmonic sum of reciprocal
separations and not an artefact of the Gram-row argument.

### Lint gate

`scripts/formal_tools.py lint` reports **no** error attributable to any module added for these three
cards: every one is reachable from the `GaloisForLFunctions.RHTower` umbrella, with no `sorry`,
`axiom`, `opaque` or `unsafe` declaration and no build warning.  The nine errors the gate does
report are unwired modules owned by concurrent sessions in other areas.

### Arc versus chord — `Sieve/ChordalSeparation.lean` (2026-08-03)

The Gram-row bound is stated in the *chordal* separation `‖conj(ξ_r)ξ_t − 1‖`, whereas a sieve
hypothesis is normally an *arc* separation.  The conversion is now explicit:

- **`norm_exp_I_sub_one`** : `‖exp(iθ) − 1‖ = 2|sin(θ/2)|` — the chord subtended by an arc;
- **`four_mul_le_norm_exp_two_pi_I_sub_one`** : `4α ≤ ‖exp(2πiα) − 1‖` for `0 ≤ α ≤ 1/2`, by
  Jordan's inequality `sin t ≥ (2/π)t` on `[0, π/2]` (mathlib's `Real.mul_le_sin`).

Built, wired, axiom-clean.  So frequencies separated by `δ` in arc are separated by at least `4δ`
in chord, and the reciprocal separations in the Gram row are bounded accordingly.  This is the last
elementary conversion between the two ways of stating a large sieve hypothesis.

### Note on what is *not* being rebuilt

Mathlib already owns character orthogonality for finite abelian groups
(`Analysis/Fourier/FiniteAbelian/Orthogonality.lean`, in the weighted-inner-product `AddChar`
formalism) and a `ZMod` discrete Fourier transform.  `RootsOfUnityFrequencies.lean` is a
*specialisation* of that orthogonality to the corpus's own `expRow`/`EuclideanSpace` objects, which
is what the sieve chain consumes — not new mathematics, and no further Parseval layer will be built
on top of it.

### Bounded Dirichlet partial sums — `Sieve/DirichletKernelBound.lean` (2026-08-03)

First step of the route to the *sharp* large sieve constant.

- `exp_I_pow` : powers of `exp(iθ)` are the exponentials of the multiples of `θ`;
- **`norm_sum_exp_le`** : `‖∑_{d < D} exp(idθ)‖ ≤ 1/|sin(θ/2)|`, uniform in `D`;
- **`abs_sum_sin_le`** : `|∑_{d < D} sin(dθ)| ≤ 1/|sin(θ/2)|`.

Built, wired, axiom-clean.  The proof composes two corpus facts and adds nothing analytic: the
geometric sum bound `‖∑ ζ^d‖ ≤ 2/‖ζ − 1‖` of `GeometricSumBound.lean` with the chord identity
`‖exp(iθ) − 1‖ = 2|sin(θ/2)|` of `ChordalSeparation.lean`; taking imaginary parts loses nothing.

Uniformly bounded partial sums are the Abel-summation input for the classical estimate of
`∑_{d ≤ M} sin(dθ)/d`, which is what converts the Toeplitz kernel `1/(m−n)` into a *bounded* Fourier
multiplier.  That is the route to Hilbert's inequality, hence to replacing the current
`Δ = N + O(δ^{-1} log δ^{-1})` by `Δ = N + O(δ^{-1})` — the shape Matomäki–Radziwiłł consumes.

Recorded honestly: this route yields the sharp *shape* with some explicit constant, not the optimal
constant `π`, which needs the full infinite sawtooth series.  For the sieve application the shape is
what matters.

### Abel's inequality — `Sieve/AbelInequality.lean` (2026-08-03)

- **`abs_sum_mul_le_of_bounded_partial`** : if `|∑_{j<k} g j| ≤ B` for every `k`, and `w` is
  nonnegative and nonincreasing, then `|∑_{i<n} w i · g i| ≤ B · w 0`.

Built, wired, axiom-clean.  This is Dirichlet's test in quantitative form: summation by parts writes
the weighted sum as `w_{n-1}S_n` minus the increments `(w_{i+1} − w_i)S_{i+1}`, the increments are
nonpositive so their absolute values telescope to `w_0 − w_{n-1}`, and every partial sum is capped
by `B`.

Combined with `DirichletKernelBound.abs_sum_sin_le` (`|∑_{d<D} sin(dθ)| ≤ 1/|sin(θ/2)|`) and the
weight `w d = 1/(d+1)`, this is the estimate for `∑_{d ≤ M} sin(dθ)/d` that converts the Toeplitz
kernel `1/(m−n)` into a bounded Fourier multiplier — the remaining step to `Δ = N + O(δ^{-1})`.

### Abel on a tail — `Sieve/AbelTail.lean` (2026-08-03)

- `sum_range_shift` : shifted partial sums are differences of original ones;
- **`abs_sum_Ico_mul_le_of_bounded_partial`** : `|∑_{a ≤ i < n} w i · g i| ≤ 2B · w a`.
  Restricting to a tail costs only a factor two, and the bound carries the *weight at the cut*;
- **`abs_sum_sin_div_le`** : `|∑_{d < M} sin(dθ)/(d+1)| ≤ 1/|sin(θ/2)|`, by composing
  `DirichletKernelBound.abs_sum_sin_le` with `AbelInequality`.

Built, wired, axiom-clean.

**What is still missing, stated precisely.**  `abs_sum_sin_div_le` blows up as `θ → 0`, whereas the
true harmonic-weighted sine sum is bounded by an *absolute* constant.  The uniform bound needs the
range split at `a ≍ 1/|θ|`: below the cut `|sin(dθ)/(d+1)| ≤ |θ|` so that part is `≤ 1`; above it
`abs_sum_Ico_mul_le_of_bounded_partial` gives `2B/(a+1) ≍ 2|θ|/|sin(θ/2)| ≤ 2π`.  Both halves are
now available — the factor `w a` in the tail bound is exactly what makes the second half work — and
assembling them is the remaining step to a uniform constant, hence to `Δ = N + O(δ^{-1})`.

### Uniform harmonic sine bound — `Sieve/HarmonicSineBound.lean` (2026-08-03)

- **`abs_sum_sin_div_le_uniform`** :
  `|∑_{d < M} sin(dθ)/(d+1)| ≤ 1 + 3π`, uniformly in `M` and in `0 < θ ≤ π`.

Built, wired, axiom-clean.  This is the estimate the previous module said was still missing.  The
range is split at `⌈1/θ⌉`: below the cut each term satisfies `|sin(dθ)|/(d+1) ≤ dθ/(d+1) ≤ θ`, so
that half is at most `⌈1/θ⌉θ ≤ 1 + θ`; above it `AbelTail.abs_sum_Ico_mul_le_of_bounded_partial`
gives `2B/(⌈1/θ⌉+1) ≤ 2Bθ`, and Jordan's inequality caps `B = 1/|sin(θ/2)|` by `π/θ`, so that half
is at most `2π`.

The tail lemma's "weight at the cut" factor is exactly what makes the second half work: without it
the bound would degrade as `θ → 0`, which is precisely where the first half is longest.  The two
halves are therefore not interchangeable, and both were needed.

This is the Fourier multiplier bound for the Toeplitz kernel `1/(m−n)`: the kernel's symbol
`∑_{d} sin(dθ)/d` is bounded by an absolute constant, which is what Hilbert's inequality asserts.
Converting it into the bilinear statement `|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²` — and hence into
`Δ = N + O(δ^{-1})` — is the remaining step.

### Next step scoped: exact discrete Parseval (2026-08-03)

`HarmonicSineBound.abs_sum_sin_div_le_uniform` bounds the *symbol* of the Toeplitz kernel.  Turning
that into the bilinear Hilbert inequality `|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²` needs one more
identity, and it is now precisely located:

    (1/Q) ∑_{j<Q} |⟪expRow Q (ζ^j), x⟫|² = ‖x‖²      (exact discrete Parseval)

`RootsOfUnityFrequencies.lean` already gives the two inputs — the family `expRow Q (ζ^j)` is
pairwise orthogonal with every diagonal entry exactly `Q`.  What remains is to promote `Q` pairwise
orthogonal vectors of norm² `Q` in a `Q`-dimensional space to an orthonormal *basis* and read off
Parseval.  API established for this toolchain:

- `finrank_euclideanSpace_fin : finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n`;
- `basisOfOrthonormalOfCardEqFinrank : Orthonormal 𝕜 v → Fintype.card ι = finrank 𝕜 E → Basis ι 𝕜 E`;
- `OrthonormalBasis.mk : Orthonormal 𝕜 v → ⊤ ≤ span 𝕜 (range v) → OrthonormalBasis ι 𝕜 E`;
- Parseval is `OrthonormalBasis.sum_inner_mul_inner` at `y = x`, since
  `⟪x, b i⟫⟪b i, x⟫ = |⟪b i, x⟫|²`.

Names that do **not** exist here (checked, so they are not retried): `OrthonormalBasis.sum_sq_norm_inner`,
`OrthonormalBasis.norm_sq_eq_sum`, `OrthonormalBasis.sum_norm_sq_inner`.

Note the scale: the family has norm² `Q`, not `1`, so the orthonormal family is `Q^{-1/2} • expRow`,
and the `1/Q` in the Parseval statement is that normalisation — not a convention.

### Exact discrete Parseval landed — `Sieve/DiscreteParseval.lean` (2026-08-03)

The identity scoped in the previous entry is now proved.

- `unitRow Q ζ j := Q^{-1/2} • expRow Q (ζ^j)`;
- `orthonormal_unitRow` : the rescaled rows are orthonormal;
- `span_unitRow`, `rootBasis`, `rootBasis_apply` : `Q` orthonormal vectors in a `Q`-dimensional
  space form an orthonormal basis;
- **`sum_norm_inner_expRow_root`** :
  `∑_{j < Q} |⟪expRow Q (ζ^j), x⟫|² = Q ‖x‖²`.

Built, wired, axiom-clean (four theorems).  Parseval is `OrthonormalBasis.sum_inner_mul_inner` at
`y = x`, using `⟪x, b j⟫⟪b j, x⟫ = |⟪b j, x⟫|²`; the factor `Q` is the rescaling, since the
unnormalised rows have squared norm `Q`.

With this and `HarmonicSineBound.abs_sum_sin_div_le_uniform` both unconditional, the two halves of
the Toeplitz argument are in place: the symbol of `1/(m−n)` is bounded by an absolute constant, and
the quadratic form is an exact average of that symbol against `|∑ x_n ζ^{jn}|²` which Parseval
returns to `∑|x_n|²`.  Assembling them into
`|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²` — and hence `Δ = N + O(δ^{-1})` — is the remaining step.

### Bounded symbol gives bounded form — `Sieve/SymbolBound.lean` (2026-08-03)

- **`abs_sum_symbol_mul_norm_inner_le`** :
  `|∑_j c_j |⟪expRow Q (ζ^j), x⟫|²| ≤ C · Q ‖x‖²` whenever `|c_j| ≤ C`.

Built, wired, axiom-clean.  Triangle inequality followed by exact discrete Parseval; no cancellation
is used, so the constant is exactly the sup-norm of the symbol.

This is the abstract half of Hilbert's inequality, and it now sits directly on top of the concrete
half: `HarmonicSineBound.abs_sum_sin_div_le_uniform` bounds the symbol of the Toeplitz kernel
`1/(m−n)` by an absolute constant.

**What remains is one identification, stated precisely.**  To apply the above to that kernel one
must exhibit the quadratic form `∑_{m≠n} x_m x̄_n/(m−n)` as `(1/Q)∑_j c_j |⟪expRow Q (ζ^j), x⟫|²`
with `c_j` the kernel's symbol at `ζ^j`.  That is the finite convolution identity — an exact
computation using the same roots-of-unity orthogonality already in
`RootsOfUnityFrequencies.lean`, valid once `Q` exceeds twice the support length so that no
wraparound occurs.  It is bookkeeping over an established orthogonality relation, not a new
estimate.

### Coefficient expansion — `Sieve/CoefficientExpansion.lean` (2026-08-03)

- **`inner_expRow_apply`** : `⟪expRow Q ξ, x⟫ = ∑_m conj(ξ^m) x_m` — the coefficient is the finite
  Fourier coefficient;
- **`normSq_inner_expRow`** :
  `|⟪expRow Q ξ, x⟫|² = ∑_m ∑_n (conj(ξ^m) x_m) · conj(conj(ξ^n) x_n)`.

Built, wired, axiom-clean.  Both are exact and use *no* orthogonality — the first is the definition
of the inner product on `EuclideanSpace`, the second is `|z|² = z·conj z` with the sum expanded.

**Remaining bookkeeping, stated exactly.**  Summing `normSq_inner_expRow` against a symbol `c_j` and
exchanging the order of summation gives

    ∑_j c_j |⟪expRow Q (ζ^j), x⟫|² = ∑_m ∑_n x_m conj(x_n) · (∑_j c_j conj(ζ^{jm}) ζ^{jn}),

so the multiplier with symbol `c` *is* the kernel `Ǩ(m,n) = ∑_j c_j ζ^{j(n−m)}`.  Identifying that
kernel with `1/(m−n)` — for `Q` past twice the support length, via the roots-of-unity orthogonality
of `RootsOfUnityFrequencies.lean` — then combines with `SymbolBound.lean` and
`HarmonicSineBound.lean` to give `|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²`.

Every ingredient of that chain is now unconditional in the corpus; what is left is index
manipulation over identities already proved, with no further estimate required.

### Multiplier is a kernel — `Sieve/CoefficientExpansion.lean`, second theorem (2026-08-03)

- **`sum_symbol_mul_normSq_eq`** :
  `∑_j c_j |⟪expRow Q (ζ^j), x⟫|² = ∑_m ∑_n x_m conj(x_n) · (∑_j c_j conj(ζ^{jm}) ζ^{jn})`.

Built, wired, axiom-clean.  This is the bookkeeping step flagged in the previous entry, now proved:
summing the coefficient expansion against a symbol and exchanging the order of summation exhibits
the Fourier multiplier with symbol `c` as the kernel `Ǩ(m,n) = ∑_j c_j ζ^{j(n−m)}`.  Exact — no
orthogonality, no estimate.

**Status of the Toeplitz argument.**  Every analytic ingredient is unconditional in the corpus:

| step | module |
|-|-|
| symbol of `1/(m−n)` is bounded by an absolute constant | `HarmonicSineBound.lean` |
| bounded symbol ⟹ bounded quadratic form | `SymbolBound.lean` |
| exact discrete Parseval | `DiscreteParseval.lean` |
| multiplier ⟹ kernel | `CoefficientExpansion.lean` |
| roots-of-unity orthogonality | `RootsOfUnityFrequencies.lean` |

What remains is to run the kernel identification in the one direction not yet written out: choosing
`c_j` as the partial sums of `1/d` against `ζ^{jd}` and checking, via the orthogonality above, that
`Ǩ(m,n) = 1/(m−n)` once `Q` exceeds twice the support length.  That is a choice of `c` plus an
orthogonality computation over identities already proved.

### Orthogonality in divisibility form — `Sieve/RootOrthogonality.lean` (2026-08-03)

- **`sum_pow_mul_eq`** : `∑_{j < Q} (ζ^k)^j = Q` if `Q ∣ k`, else `0`;
- `sum_pow_mul_index_eq` : the same with the exponent written `ζ^{jk}`, the form it takes after
  exchanging summation order.

Built, wired, axiom-clean.  Stating the relation with an `if` on `Q ∣ k` — rather than as two
separate lemmas — is what makes it usable as a *rewrite inside a sum over `k`*, which is exactly what
the inverse discrete Fourier transform needs: summing a symbol against `ζ^{jk}` and exchanging
returns the coefficient at the surviving index.

Note both theorems hold without any positivity hypothesis on `Q`; the `0 < Q` I first assumed turned
out to be unnecessary, so the statements are the general ones.

With `CoefficientExpansion.sum_symbol_mul_normSq_eq` this closes the multiplier/kernel dictionary in
both directions: a symbol determines its kernel, and orthogonality recovers the symbol's
coefficients from it.

### Kernel recovery — `Sieve/InverseDFT.lean` (2026-08-03)

- **`kernel_of_symbol`** :
  `∑_j (∑_d K_d ζ^{jd}) ζ^{jk} = Q · ∑_{d : Q ∣ d + k} K_d`.

Built, wired, axiom-clean.  One exchange of summation followed by the divisibility form of
orthogonality; the `if` in `RootOrthogonality.sum_pow_mul_eq` collapses the inner sum to the
surviving residue class.  When `K` is supported on `range Q` the congruence pins down a single `d`,
so the right-hand side is `Q · K_{(−k) mod Q}` — the inverse discrete Fourier transform.

That is the reason the orthogonality lemma was stated with an `if` rather than as two branches: the
`if` is what survives the exchange and becomes the filter on the right.

The multiplier/kernel dictionary is now complete and unconditional in both directions —
`CoefficientExpansion.sum_symbol_mul_normSq_eq` sends a symbol to its kernel, `kernel_of_symbol`
recovers the coefficients — alongside the bounded-symbol bound (`SymbolBound`), exact Parseval
(`DiscreteParseval`), and the absolute bound on the symbol of `1/(m−n)` (`HarmonicSineBound`).

### Inverse DFT completed — `Sieve/ResidueSingleton.lean` (2026-08-03)

- `filter_dvd_add_eq` : for `k < Q` the surviving residue class `{d < Q : Q ∣ d + k}` is the
  singleton `{(Q − k) % Q}` — since `d + k < 2Q`, the only multiples of `Q` it can equal are `0`
  and `Q`;
- `sum_filter_dvd_add` : hence the filtered sum is a single coefficient;
- **`kernel_of_symbol_singleton`** :
  `∑_j (∑_d K_d ζ^{jd}) ζ^{jk} = Q · K_{(Q−k) % Q}`.

Built, wired, axiom-clean.  The `(Q − k) % Q` form covers both branches uniformly: it is `0` when
`k = 0` and `Q − k` otherwise, so no case split leaks into the statement.

This completes the inverse discrete Fourier transform.  Every component of the Toeplitz argument now
exists unconditionally in the corpus:

| step | module |
|-|-|
| symbol of `1/(m−n)` bounded absolutely | `HarmonicSineBound.lean` |
| bounded symbol ⟹ bounded quadratic form | `SymbolBound.lean` |
| exact discrete Parseval | `DiscreteParseval.lean` |
| symbol ⟹ kernel | `CoefficientExpansion.lean` |
| kernel ⟹ coefficients (inverse DFT) | `RootOrthogonality.lean`, `InverseDFT.lean`, `ResidueSingleton.lean` |

What remains is to choose the coefficient sequence `K_d` matching `1/d` on the relevant range and
read the bilinear inequality off the dictionary — an instantiation, with every supporting identity
and estimate already proved.

### Bilinear bound on the kernel side — `Sieve/BilinearMultiplier.lean` (2026-08-03)

- **`abs_sum_kernel_bilinear_le`** :
  `‖∑_m ∑_n x_m conj(x_n) Ǩ(m,n)‖ ≤ C · Q ‖x‖²` for `Ǩ(m,n) = ∑_j c_j conj(ζ^{jm}) ζ^{jn}`
  and any real symbol with `|c_j| ≤ C`.

Built, wired, axiom-clean.  This is Hilbert's inequality in its structural form: the left side is an
arbitrary sesquilinear form built from a Toeplitz-type kernel, and the bound depends only on the
sup-norm of that kernel's symbol.  No property of the particular kernel enters.

The whole multiplier apparatus is now closed.  Specialising to `1/(m−n)` means choosing the
coefficient sequence and invoking `HarmonicSineBound.abs_sum_sin_div_le_uniform` for its symbol —
the one remaining instantiation, with every identity and estimate it needs already proved.

### Matching the two kernel shapes — `Sieve/KernelReshape.lean` (2026-08-03)

The multiplier side produces the kernel as `∑_j c_j conj(ζ^{jm}) ζ^{jn}`; the inverse transform
consumes it as `∑_j c_j ζ^{jk}`.  The bridge is that conjugation is inversion on the unit circle.

- **`conj_pow_eq`** : `conj(ζ^{jm}) = ζ^{j(Q−m)}` for `m ≤ Q` — both sides are inverses of `ζ^{jm}`,
  the first because `|ζ| = 1`, the second because `ζ^{j(Q−m)}ζ^{jm} = (ζ^Q)^j = 1`;
- **`kernel_pairing_eq`** : substituting turns the conjugate pairing into the single character
  `ζ^{j((Q−m)+n)}`.

Built, wired, axiom-clean.  `(Q−m)+n` is precisely the index at which
`ResidueSingleton.kernel_of_symbol_singleton` reads off a coefficient, so the two halves of the
dictionary now compose without any remaining shape mismatch.

### Kernel of a transform symbol — `Sieve/KernelValue.lean` (2026-08-03)

- **`kernel_value`** : for `n < m < Q`,
  `∑_j (∑_d K_d ζ^{jd}) conj(ζ^{jm}) ζ^{jn} = Q · K_{m−n}`.

Built, wired, axiom-clean.  This is the two halves of the dictionary composed into one statement:
`KernelReshape.conj_pow_eq` turns the conjugate pairing into the character `ζ^{j((Q−m)+n)}`, and
`ResidueSingleton.kernel_of_symbol_singleton` reads off the coefficient at
`(Q − ((Q−m)+n)) % Q`, which for `n < m < Q` is exactly `m − n`.

Restricting to the strict lower triangle `n < m` is not a loss: a Toeplitz kernel is determined off
the diagonal by its lower triangle together with its symmetry type.  The bound `m < Q` excludes only
the degenerate corner `m = Q, n = 0`, where the residue would wrap.

A symbol built from coefficients therefore *has* those coefficients as its kernel, with the factor
`Q` of the transform.  Together with `BilinearMultiplier.abs_sum_kernel_bilinear_le` — which bounds
any such bilinear form by the sup-norm of the symbol — the apparatus is complete: prescribing `K_d`
and bounding the resulting symbol gives a bilinear inequality for that kernel.

### Why the kernel must be antisymmetric — `Sieve/AntisymmetricSymbol.lean` (2026-08-03)

- **`antisym_pow_eq`** : `ζ^{jd} − ζ^{j(Q−d)} = 2i · Im(ζ^{jd})`, since the second term is the
  conjugate of the first;
- **`antisym_symbol_eq`** : hence the antisymmetrised symbol of a real coefficient sequence is `2i`
  times a real sine sum.

Built, wired, axiom-clean.

This records a structural point that the earlier entries left implicit and that would otherwise be
easy to get wrong.  The *full* symbol of a one-sided sequence `K_d = 1/d` is **not** bounded: its
real part is `∑_d cos(dθ)/d`, which diverges like `−log|2 sin(θ/2)|`.  Only the imaginary part is
uniformly bounded.  That is precisely why Hilbert's inequality concerns `1/(m−n)` — an
*antisymmetric* kernel — and not `1/|m−n|`, and it is why `HarmonicSineBound.lean` bounds a **sine**
sum rather than a full exponential sum.

So the coefficient sequence to feed into `KernelValue.kernel_value` is the antisymmetric one, whose
symbol is `2i` times the quantity already bounded by `1 + 3π`.

### Symbol's imaginary part is the sine sum — `Sieve/SymbolImaginaryPart.lean` (2026-08-03)

- `im_exp_pow` : `Im((exp(iθ))^k) = sin(kθ)`;
- **`abs_sum_im_exp_pow_div_le`** :
  `|∑_{d < M} Im((exp(iθ))^d)/(d+1)| ≤ 1 + 3π`, uniformly in `M` and `0 < θ ≤ π`.

Built, wired, axiom-clean.  The multiplier apparatus produces the antisymmetrised symbol as `2i`
times `∑_d K_d Im(ζ^{jd})`, whereas `HarmonicSineBound.lean` bounds a sum of `Real.sin`; this
identifies the two, so the uniform bound now sits directly on the quantity the kernel dictionary
consumes rather than on a paraphrase of it.

Every piece of the Hilbert-inequality argument is now expressed in the *same* vocabulary — powers of
a root of unity, their imaginary parts, and the kernel dictionary — with no remaining translation
step between the analytic estimate and the algebraic apparatus.

### The concrete root and its angles — `Sieve/ConcreteRoot.lean` (2026-08-03)

Everything above was stated for an abstract primitive root.  Instantiating at `ζ = exp(2πi/Q)` makes
the angles explicit.

- `rootOfUnity Q`, `rootOfUnity_pow` : `ζ^j = exp(iθ_j)` with `θ_j = 2πj/Q`;
- `isPrimitiveRoot_rootOfUnity` : it is primitive (mathlib's `Complex.isPrimitiveRoot_exp`, modulo
  moving the cast);
- **`abs_sum_im_rootOfUnity_pow_div_le`** : for `1 ≤ j` and `2j ≤ Q`,
  `|∑_{d < M} Im((ζ^j)^d)/(d+1)| ≤ 1 + 3π`.

Built, wired, axiom-clean.  The hypothesis range `1 ≤ j`, `2j ≤ Q` is exactly `0 < θ_j ≤ π`, which is
where the harmonic sine bound holds; it is the natural half of the frequencies, and no generality is
lost, because the symbol at `j` and at `Q − j` are conjugate.

The symbol bound is now available at a concrete root of unity, so the abstract apparatus
(`KernelValue`, `BilinearMultiplier`) can be instantiated without carrying an abstract `ζ` and a
separate hypothesis that its symbol is bounded.

### Symbol bound at every frequency — `Sieve/SymbolReflection.lean` (2026-08-03)

- `im_pow_reflect` : `Im((ζ^{Q−j})^d) = −Im((ζ^j)^d)`, since `ζ^{Q−j}` is the conjugate of `ζ^j`;
- **`abs_sum_im_rootOfUnity_pow_div_le_all`** : the uniform bound `1 + 3π` holds at *every*
  frequency `j < Q`.

Built, wired, axiom-clean.  The previous entry bounded the symbol only on the half range
`1 ≤ j`, `2j ≤ Q`.  The remaining frequencies need no new estimate: `j = 0` gives the zero symbol
because every power of `1` is real, and `j > Q/2` reflects to `Q − j` in the half range with the
symbol negated.

This matters because `BilinearMultiplier.abs_sum_kernel_bilinear_le` quantifies over *all*
`j : Fin Q` — a bound on half the frequencies would not have satisfied its hypothesis.  The symbol
bound is now in exactly the shape that theorem consumes.

### Hilbert's inequality, bilinear form — `Sieve/HilbertBilinear.lean` (2026-08-03)

- `hilbertSymbol Q M j := ∑_{d < M} Im((ζ^j)^d)/(d+1)` at the standard `Q`-th root of unity;
- `abs_hilbertSymbol_le` : bounded by `1 + 3π` at every frequency;
- **`hilbert_bilinear_bound`** :
  `‖∑_m ∑_n x_m conj(x_n) Ǩ(m,n)‖ ≤ (1 + 3π) · Q ‖x‖²`

  for the kernel `Ǩ` that symbol generates, with an absolute constant, uniformly in `Q`, `M`
  and `x`.

Built, wired, axiom-clean.  This is Hilbert's inequality in the corpus's formulation: an
antisymmetric Toeplitz kernel with harmonic coefficients has bilinear form controlled by the energy,
with no dependence on the length.

The constant is `1 + 3π`, not the optimal `π`; as recorded when the symbol bound was built, the
optimal constant requires the full infinite sawtooth series, and for the sieve application only the
*shape* matters.

Chain, all unconditional and each proved in this corpus:

    GeometricSumBound → DirichletKernelBound → AbelInequality → AbelTail → HarmonicSineBound
      → SymbolImaginaryPart → ConcreteRoot → SymbolReflection ─┐
    RootsOfUnityFrequencies → DiscreteParseval → SymbolBound ──┤
    CoefficientExpansion → KernelReshape ──────────────────────┴→ BilinearMultiplier
                                                                    → HilbertBilinear

### Correction: what the corpus's Hilbert inequality does and does not give (2026-08-03)

The previous entry closed with "next: use this to upgrade `Δ = N + O(δ^{-1} log δ^{-1})` to
`Δ = N + O(δ^{-1})`".  Traced through, **that step is not available from what is proved**, and the
claim is withdrawn.

`HilbertBilinear.hilbert_bilinear_bound` is the inequality for the kernel generated by a symbol *at
the `Q`-th roots of unity* — that is, for frequencies `λ_r = r/Q` which are **equally spaced**.  The
Montgomery–Vaughan route to the sharp large sieve constant needs Hilbert's inequality for
**arbitrary well-spaced** real frequencies `λ_1 < … < λ_R` with `λ_{r+1} − λ_r ≥ δ`:

    |∑_{r ≠ s} x_r conj(x_s) / (λ_r − λ_s)| ≤ π δ^{-1} ∑ |x_r|²

That generalisation is the actual content of Montgomery–Vaughan (1974); its proof is a different and
harder argument, not a corollary of the cyclic case.  In the equally-spaced case the corpus already
had the sharp constant directly, from exact orthogonality
(`RootsOfUnityFrequencies.largeSieve_roots`), so the cyclic Hilbert inequality does not improve the
general bound.

**Accordingly, the status is unchanged from before this sub-programme**: the corpus owns the *weak*
large sieve `Δ = N + O(δ^{-1} log δ^{-1})` (`LargeSieveWeak.lean`), and the sharp `Δ = N + δ^{-1}`
remains open, now with its obstruction identified precisely as the well-spaced generalisation rather
than as "Hilbert's inequality" unqualified.

What the sub-programme did produce, all unconditional and none of it in mathlib: the geometric and
Dirichlet-kernel bounds, Abel's inequality in plain and tail form, the uniform harmonic sine bound,
exact discrete Parseval, the multiplier/kernel dictionary in both directions, and the cyclic Hilbert
inequality.  Those are reusable regardless, and the last of them is the equally-spaced case of the
theorem still needed.

### Separated points spread linearly — `Sieve/SeparatedPoints.lean` (2026-08-03)

- **`le_of_gap`** : if consecutive gaps are at least `δ` then `λ_r + (s−r)δ ≤ λ_s` for `r ≤ s`;
- `inv_dist_le` : hence `|λ_r − λ_s|^{-1} ≤ ((s−r)δ)^{-1}`.

Built, wired, axiom-clean.  This is the telescoping that converts a *separation* hypothesis into the
reciprocal bounds appearing in a Gram row, and it is stated for real frequencies rather than for
unimodular ratios, so it applies to the general (non-cyclic) setting.

It also makes the source of the logarithmic loss explicit and unavoidable for any absolute-values
argument: summing `((s−r)δ)^{-1}` over `s ≠ r` gives `2δ^{-1}H_{R−1} ≍ δ^{-1} log R`.  Montgomery–
Vaughan's sharp constant is obtained by exploiting *cancellation* in `∑_{r≠s} x_r x̄_s/(λ_r−λ_s)`
rather than bounding term by term — which is why, as recorded in the correction above, the cyclic
Hilbert inequality does not supply it.

### Formal layer — the Gram row of a separated family is harmonic

`formal/GaloisForLFunctions/RHTower/Sieve/SeparatedRowSum.lean` completes the separation estimate of
`SeparatedPoints.lean` into a full row bound. For real frequencies with consecutive gaps at least
`δ > 0` and any `r < R`:

- `lt_of_gap` — separated points are strictly increasing.
- `sum_inv_dist_le` — `∑_{r < s < R} (λ_s − λ_r)^{-1} ≤ δ^{-1} ∑_{i < R−r−1} (i+1)^{-1}`.
- `sum_inv_dist_below_le` — the same bound below `r`, obtained by reflecting the range rather than
  by a second estimate.
- `sum_inv_abs_dist_le` — `∑_{s ≠ r, s < R} |λ_s − λ_r|^{-1} ≤ 2 δ^{-1} ∑_{i < R} (i+1)^{-1}`.

All four are unconditional (`[propext, Classical.choice, Quot.sound]`).

Consequence for the route: the harmonic sum on the right is *exactly* the loss incurred by any
argument that bounds `∑_{r ≠ s} x_r conj(x_s)(λ_r − λ_s)^{-1}` term by term — including the Gram-row
route used in `LargeSieveWeak.lean`. So the weak large sieve's `Δ = N + O(δ^{-1} log R)` is not an
artefact of that particular assembly; it is the ceiling of the whole absolute-value method, now a
theorem rather than an observation. Montgomery–Vaughan's sharp `Δ = N + δ^{-1}` must therefore come
from cancellation inside that sum. The cyclic Hilbert inequality already in the corpus
(`HilbertBilinear.lean`) supplies cancellation only for equally spaced frequencies, where
`largeSieve_roots` already gives the sharp constant by orthogonality; it does not extend to the
arbitrary well-spaced case, which remains the open input.

### Formal layer — the chord bound on the circle

The separation estimates above are stated for real frequencies, but a sieve hypothesis separates
frequencies in `ℝ/ℤ`. Two modules supply the missing conversion, both unconditional.

`formal/GaloisForLFunctions/RHTower/Sieve/CircleSeparation.lean`:

- `mul_abs_le_abs_sin` — Jordan's inequality made two-sided: `(2/π)|x| ≤ |sin x|` for `|x| ≤ π/2`.
- `four_mul_abs_le_norm_exp_two_pi` — `4|β| ≤ ‖e(β) − 1‖` for `|β| ≤ 1/2`.
- `exp_two_pi_sub_round` — reducing the argument of `e(·)` modulo one changes nothing.
- `four_mul_round_dist_le` — `4|α − round α| ≤ ‖e(α) − 1‖` at *every* real `α`.

`formal/GaloisForLFunctions/RHTower/Sieve/CircleDistance.lean` names the distance to the nearest
integer `toIntDist x = |x − round x|` and proves what a separation count needs: it is at most `1/2`,
it is invariant under integer shifts (`toIntDist_add_int`), it agrees with `|x|` when `|x| < 1/2`
(`toIntDist_eq_abs_of_abs_lt_half`, via `round_eq_zero_of_abs_lt_half`), and — the form the counting
uses — `toIntDist_sub_lt`: if the reduced representatives of `u` and `v` lie within `δ ≤ 1/2` of each
other then `u` and `v` lie within `δ` on the circle. `four_mul_toIntDist_le` restates the chord bound
in these terms.

`toIntDist_sub_lt` is the lemma that converts "two points in a short arc" into "two points violating
the separation hypothesis", which is the step the circle row-sum needs and the reason the real-line
estimate `sum_inv_abs_dist_le` does not transfer directly: on the circle the ordering of the
frequencies does not bound their distances, only their reduced offsets do.

### Formal layer — the large sieve with an explicit Δ

Two further modules close the gap between the abstract Bessel inequality of `LargeSieveWeak.lean`
and a usable sieve statement. Both unconditional.

`formal/GaloisForLFunctions/RHTower/Sieve/CircleRowSum.lean` proves the Gram row of a family
`δ`-separated in `ℝ/ℤ` is harmonic:

`circle_row_sum_le` — `∑_{t ≠ r} ‖λ_t − λ_r‖^{-1} ≤ 2δ^{-1} ∑_{1 ≤ k ≤ M} k^{-1}` for `M ≥ (2δ)^{-1}`,

together with `one_le_levelOf`, `levelOf_mul_le`, `lt_levelOf_succ_mul`, `levelOf_le`. The index
ordering is *not* available here — on the circle the frequencies may wrap — so the count is by band:
each `λ_t − λ_r` reduces to an offset in `[−1/2, 1/2]` lying in some `[kδ, (k+1)δ)`; two frequencies
in the same band on the same side of zero have offsets differing by less than `δ` and so violate the
separation hypothesis (`toIntDist_sub_lt`). Hence the level–side pair is injective, at most two
frequencies per level, and no level exceeds `(2δ)^{-1}` since offsets never exceed `1/2`.

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveSeparated.lean` assembles this with the chord
bound:

- `circleFreq`, `norm_circleFreq`, `conj_circleFreq_mul` — the correlation of two circle frequencies
  is the frequency of their difference.
- `four_mul_toIntDist_le_norm_sub` — chordal separation from circle separation.
- `largeSieve_separated` — **`∑_r |⟪e(λ_r), a⟫|² ≤ (N + δ^{-1} ∑_{1 ≤ k ≤ M} k^{-1}) ‖a‖²`** for
  `λ` pairwise `δ`-separated in `ℝ/ℤ` and `M ≥ (2δ)^{-1}`.

This is the first statement in the corpus where the large sieve constant is *computed* from a
separation hypothesis rather than assumed: `Δ = N + O(δ^{-1} log δ^{-1})`, everything explicit. The
sharp `Δ = N + δ^{-1}` is a different theorem — `sum_inv_abs_dist_le` shows the harmonic factor is
the provable ceiling of the absolute-value method, so removing it requires cancellation
(Montgomery–Vaughan), not a better assembly of these pieces.

### Formal layer — the large sieve constant in closed form

`formal/GaloisForLFunctions/RHTower/Sieve/HarmonicLogBound.lean` identifies the partial harmonic
sums produced by the Gram-row estimates with mathlib's harmonic numbers and quotes the logarithmic
bound: `sum_Icc_one_div_eq_sum_range`, `sum_Icc_one_div_eq_harmonic`, and
`sum_Icc_one_div_le_one_add_log` (`∑_{1 ≤ k ≤ M} k^{-1} = H_M ≤ 1 + log M`).

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveExplicit.lean` removes the free cut:

- `largeSieve_separated_log` — `Δ = N + δ^{-1}(1 + log M)` for any `M ≥ (2δ)^{-1}`.
- `largeSieve_separated_explicit` — **`∑_r |⟪e(λ_r), a⟫|² ≤ (N + δ^{-1}(1 + log((2δ)^{-1}+1))) ‖a‖²`**
  for any family `δ`-separated in `ℝ/ℤ`, taking `M = ⌈(2δ)^{-1}⌉`.

Both unconditional. This is the weak large sieve in closed form: no free parameter, no hypothesis
beyond the separation, and `Δ = N + O(δ^{-1} log δ^{-1})` now written out rather than described.

Status of the route's sieve layer: the weak large sieve is complete and usable. What is *not* here
is the sharp `Δ = N + δ^{-1}`; `sum_inv_abs_dist_le` proves the logarithm is the ceiling of the
absolute-value method, so it can only be removed by Montgomery–Vaughan's cancellation argument for
arbitrary well-spaced frequencies, which remains the open input alongside Matomäki–Radziwiłł.

### Formal layer — the arithmetic large sieve

`formal/GaloisForLFunctions/RHTower/Sieve/FareySeparation.lean`:

- `one_div_le_toIntDist_of_not_dvd` — a rational with denominator `D` is either an integer or at
  distance at least `D^{-1}` from every integer. Writing `m/D − round(m/D) = (m − D·round(m/D))/D`,
  the numerator is an integer that vanishes exactly when `D ∣ m`.
- `one_div_le_toIntDist_farey` — hence `‖a/q − a'/q'‖ ≥ (qq')^{-1}` whenever the two fractions are
  distinct modulo one.

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveFarey.lean`:

- `largeSieve_farey` — **`∑ |⟪e(a_i/q_i), x⟫|² ≤ (N + Q²(1 + log(Q²/2 + 1))) ‖x‖²`** for rationals
  with denominators at most `Q ≥ 2`, pairwise distinct modulo one.

Both unconditional. This is the arithmetic shape of the large sieve — the form an actual sieve
application consumes — obtained by feeding Farey separation (`δ = Q^{-2}`) into the closed-form
statement. The classical constant is `N + Q²`; the surplus logarithmic factor is exactly the one
`sum_inv_abs_dist_le` proves the absolute-value method cannot avoid, so closing the gap to the
classical constant is Montgomery–Vaughan's theorem and not a rearrangement of these steps.

### Formal layer — the large sieve on the Farey set

`formal/GaloisForLFunctions/RHTower/Sieve/FareyCoprime.lean` discharges the last hypothesis.

- `not_dvd_farey_cross` — distinct reduced fractions in the standard range are automatically
  distinct modulo one. If `qq' ∣ aq' − a'q` with `(a,q) = (a',q') = 1`, then `q ∣ aq'` forces
  `q ∣ q'` and symmetrically `q' ∣ q`, so `q = q'`; cancelling gives `q ∣ a − a'`, and `1 ≤ a,a' ≤ q`
  leaves `a = a'`.
- `largeSieve_farey_reduced` — **`∑_{(a,q)} |⟪e(a/q), x⟫|² ≤ (N + Q²(1 + log(Q²/2+1))) ‖x‖²`** over
  any set of pairs with `0 < q ≤ Q`, `1 ≤ a ≤ q`, `gcd(a,q) = 1`, and `Q ≥ 2`.

Both unconditional. The sieve hypothesis is now membership in the Farey set of order `Q` and nothing
else — the arithmetic input (coprimality) has replaced the analytic one (separation), which is the
form in which the large sieve is actually invoked.

### Formal layer — the large sieve for exponential sums

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveExpSum.lean` puts the chain into the shape the
sieve is actually invoked in. With `S(θ) = ∑_{n<N} c_n e(nθ)` (`expSum`):

- `norm_inner_expRow_conjVec` — the exponential coefficient `⟪expRow N e(θ), ·⟫` *is* `S(θ)` when
  read at the conjugated coefficient vector (`conjVec`).
- `norm_sq_conjVec` — that vector's energy is `∑_n |c_n|²`.
- `largeSieve_expSum_farey` — **`∑_{(a,q)} |S(a/q)|² ≤ (N + Q²(1 + log(Q²/2+1))) ∑_n |c_n|²`** over
  the Farey set of order `Q ≥ 2`.

All unconditional. This is the classical statement of the large sieve up to the logarithmic factor,
now with no inner-product formulation left in the way: coefficients in, exponential-sum bound out.

### Formal layer — the large sieve in textbook form

`formal/GaloisForLFunctions/RHTower/Sieve/FareySet.lean` supplies the canonical instance and the
familiar shape:

- `fareySet Q`, `mem_fareySet` — the Farey set of order `Q` (reduced `a/q` with `1 ≤ a ≤ q ≤ Q`).
- `largeSieve_expSum_fareySet` — the large sieve on it, hypothesis-free.
- `fareySet_eq_biUnion` — the Farey set fibred over its denominators; the fibres are disjoint
  because the second coordinate determines the denominator.
- `largeSieve_expSum_double` — **`∑_{q ≤ Q} ∑_{1 ≤ a ≤ q, (a,q)=1} |S(a/q)|² ≤
  (N + Q²(1 + log(Q²/2+1))) ∑_n |c_n|²`**.

All unconditional. The route's large-sieve input is now available in exactly the form applications
quote it, with `Q ≥ 2` the only hypothesis.

### Formal layer — the dual large sieve

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveDual.lean` supplies the bilinear (dual) half,
which is the shape a Halász–Montgomery argument consumes.

- `circleFreq_corr_ne_one`, `circleFreq_row_le` — the two ingredients (nontrivial correlations, the
  Gram row bound) isolated so both the Bessel and bilinear forms rest on the same statements.
- `largeSieve_separated_bilinear` — `‖∑_r c_r e(λ_r)‖² ≤ (N + δ^{-1}(1 + log((2δ)^{-1}+1))) ∑_r |c_r|²`
  for frequencies `δ`-separated in `ℝ/ℤ`.
- `norm_sq_sum_smul_expRow` — the same quantity in coordinates: a mean square over `n < N`.
- `fareySet_sep` — Farey fractions of order `Q` are `Q^{-2}`-separated (no hypothesis on `Q`; for
  `Q ≤ 1` the statement is vacuous because no two distinct points exist).
- `largeSieve_dual_fareySet` — **`∑_{n<N} |∑_{(a,q)} b_{a,q} e(na/q)|² ≤
  (N + Q²(1 + log(Q²/2+1))) ∑ |b|²`**.

All unconditional. The large sieve is now available in both directions with the same explicit
constant, so downstream arguments can use whichever pairing they need.

### Formal layer — exponential sums depend only on residues

`formal/GaloisForLFunctions/RHTower/Sieve/ResidueSum.lean` is the entry point that lets a sieve
hypothesis about residue classes reach the large sieve.

- `circleFreq_add_int` — `e(·)` is invariant under integer translation.
- `circleFreq_div_eq_rootOfUnity_pow` — `e(m/q)` is the `m`-th power of the standard `q`-th root of
  unity, linking this layer to the orthogonality already in `RootOrthogonality.lean`.
- `circleFreq_mod` — `e(na/q) = e((n mod q)a/q)`; the two arguments differ by the integer `(n/q)·a`.
- `sum_circleFreq_eq_residue` — **`∑_{n ∈ A} e(na/q) = ∑_{h<q} #{n ∈ A : n ≡ h} · e(ha/q)`**, with
  `residueCount` naming the class counts.

All unconditional. The exponential sum of an arbitrary finite set now collapses to a sum of length
`q` in the residue counts, which is the form Montgomery's sieve inequality needs before Parseval
over the residues turns it into a count.

### Formal layer — Parseval over the residues

`formal/GaloisForLFunctions/RHTower/Sieve/ResidueParseval.lean` turns the exponential sum of a set
into a count.

- `countVec`, `norm_inner_expRow_countVec` — the residue counts as a Euclidean vector; its
  coefficient against an exponential row *is* the exponential sum (up to conjugation, the counts
  being real).
- `norm_sq_countVec` — its energy is `∑_h A_h²`.
- `sum_residue_parseval` — `∑_{a<q} |∑_h A_h e(ha/q)|² = q ∑_h A_h²`.
- `sum_full_expSum_sq` — **`∑_{a<q} |∑_{n ∈ A} e(na/q)|² = q ∑_{h<q} #{n ∈ A : n ≡ h}²`**.

All unconditional. No new orthogonality was needed: the corpus's orthonormal root basis
(`DiscreteParseval.sum_norm_inner_expRow_root`) applies directly once the count vector is identified
as the vector whose exponential-row coefficients are the values of the sum.

This is the identity by which a sieve hypothesis becomes a count — bounding the left side below by
the classes `A` avoids and above by the large sieve bounds `|A|`, which is Montgomery's sieve
inequality. The remaining step is the passage from all residues `a < q` to the primitive ones
`(a,q) = 1`, where the large sieve lives.

### Formal layer — omitted classes force large exponential sums

`formal/GaloisForLFunctions/RHTower/Sieve/MontgomerySieve.lean` builds the lower-bound half of
Montgomery's sieve, the counterpart to the large sieve's upper bound.

- `occupiedClasses`, `sum_residueCount`, `sum_residueCount_occupied` — the classes `A` meets, and
  the fact that the counts sum to `|A|`.
- `sq_card_le_occupied_mul` — Cauchy–Schwarz over the occupied classes: `|A|² ≤ c ∑_h A_h²`.
- `expSum_zero` — `S(0) = |A|`.
- `occupied_mul_sum_nonzero_ge` — **`|A|²(q − c) ≤ c ∑_{a ≠ 0} |S(a/q)|²`**, `c` the number of
  occupied classes.

All unconditional. A set missing many residue classes modulo `q` therefore has large exponential
sums at the fractions with denominator `q`; the large sieve bounds those same sums from above, and
the two together bound `|A|`.

The inequality is deliberately stated multiplicatively rather than as `∑_h A_h² ≥ |A|²/c`, so it
stays true (and vacuous) when `A` is empty and `c = 0` — the divided form would be junk there.

### Formal layer — the large sieve for a set of integers

`formal/GaloisForLFunctions/RHTower/Sieve/IndicatorExpSum.lean` applies the sieve at an indicator,
which is where a set of integers enters.

- `circleFreq_pow` — `e(θ)^n = e(nθ)`.
- `indicatorVec`, `expSum_indicatorVec` — the trigonometric polynomial of an indicator is the
  exponential sum of the set.
- `sum_normSq_indicatorVec` — its energy is `|A|`.
- `largeSieve_set_fareySet` — **`∑_{(a,q) Farey of order Q} |∑_{n ∈ A} e(na/q)|² ≤
  (N + Q²(1 + log(Q²/2+1))) |A|`** for `A ⊆ [0,N)`.

All unconditional. This is the upper-bound half in the form Montgomery's sieve needs; the
lower-bound half (`occupied_mul_sum_nonzero_ge`) is already present. The two now speak about the
same object — the exponential sum of a set of integers at fractions — so the only remaining step to
a sieve bound on `|A|` is the observation that for prime `q` the non-zero residues are exactly the
primitive ones, and the sum over primes `q ≤ Q` of the Farey contributions.

### Formal layer — the prime fibre

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeFibre.lean` identifies the index sets of the two
halves of Montgomery's sieve at a prime denominator.

- `sum_erase_fin_eq_range` — erasing the zero frequency over `Fin p` or over `range p` gives the
  same sum.
- `fareySet_fibre_prime` — the fibre of the Farey set of order `Q` above a prime `p ≤ Q` is exactly
  `{a/p : 1 ≤ a < p}`; a numerator coprime to a prime is a numerator not divisible by it.
- `sum_fareySet_fibre_eq` — **the lower bound's index set (nonzero residues mod `p`) is the prime
  fibre of the Farey set**, so `∑_{a ≠ 0} |S(a/p)|²` is literally a sub-sum of what the large sieve
  bounds.

All unconditional. With this, `occupied_mul_sum_nonzero_ge` and `largeSieve_set_fareySet` are
statements about the same sums, and the sieve inequality follows by summing the fibres over primes
`p ≤ Q` (they are disjoint subsets of the Farey set) and dividing by `|A|`.

### Formal layer — Montgomery's sieve inequality (complete)

`formal/GaloisForLFunctions/RHTower/Sieve/MontgomeryInequality.lean` closes the chain:

- `occupiedClasses_card_pos` — a nonempty set meets at least one class.
- `montgomery_sieve` — **`|A| ∑_{p ∈ P} (p − c_p)/c_p ≤ N + Q²(1 + log(Q²/2 + 1))`** for
  `A ⊆ [0,N)` nonempty, `P` any family of primes `≤ Q`, and `c_p` the number of residue classes
  modulo `p` that `A` meets.

Unconditional. A set omitting many residue classes modulo many primes is small — the sieve
statement itself, not an ingredient of one.

The full chain, all unconditional, all in `RHTower/Sieve/`: Bessel with an assumed `Δ`
(`LargeSieveWeak`) → separation (`SeparatedPoints`, `SeparatedRowSum`) → circle distance and chord
bound (`CircleSeparation`, `CircleDistance`) → circle row sum (`CircleRowSum`) → closed form
(`HarmonicLogBound`, `LargeSieveExplicit`) → Farey separation and coprimality (`FareySeparation`,
`FareyCoprime`, `FareySet`) → exponential sums (`LargeSieveExpSum`, `IndicatorExpSum`) → residues
and Parseval (`ResidueSum`, `ResidueParseval`) → the lower bound (`MontgomerySieve`) → the prime
fibre (`PrimeFibre`) → this inequality. The dual form (`LargeSieveDual`) runs alongside for
Halász–Montgomery.

The one quantitative gap to the classical statement remains the logarithmic factor, and
`sum_inv_abs_dist_le` proves it is the ceiling of the absolute-value method rather than an artefact
of this assembly.

### Formal layer — the sieve bound in usable form

`formal/GaloisForLFunctions/RHTower/Sieve/SieveBound.lean` restates the sieve the way applications
quote it: in terms of the classes *omitted* rather than those occupied.

- `deficiency_ge` — `(p − c_p)/c_p ≥ w_p/(p − w_p)` when `A` misses at least `w_p` classes; the
  deficiency ratio decreases as occupancy grows.
- `card_mul_omitted_le` — **`|A| ∑_{p ∈ P} w_p/(p − w_p) ≤ N + Q²(1 + log(Q²/2+1))`**.
- `card_le_of_sieve` — **`|A| ≤ (N + Q²(1 + log(Q²/2+1))) / L`** for any positive `L` bounding the
  sum from below.

All unconditional. The hypothesis is now the natural one — "`A` omits at least `w_p` classes mod
`p`" — with no reference to the internal occupancy count, so the sieve can be applied without
unfolding its proof.

### Formal layer — the sieve is non-vacuous

`formal/GaloisForLFunctions/RHTower/Sieve/SquareSieve.lean` exhibits the chain producing a real
bound, not merely an inequality between defined quantities.

- `third_le_ratio` — omitting half the classes gives `w/(p − w) ≥ 1/3` (the value at `w = (p−1)/2`,
  `p = 2`; it improves to `1` as `p` grows).
- `card_le_of_half_omitted` — **`|A| ≤ 3(N + Q²(1 + log(Q²/2+1)))/|P|`** for a set missing at least
  half the residue classes modulo each prime of a family `P` of primes `≤ Q`.

Both unconditional. No prime counting enters — only `|P|` — so the statement is self-contained, and
it is the classical square-root phenomenon: with `Q` of order `√N` the bound is `≍ N log N / |P|`.

This settles that the sieve layer is inhabited rather than formally true and empty, which is the
standard failure mode for a formalised inequality chain.

### Formal layer — Dirichlet rows (toward Matomäki–Radziwiłł)

The card's sole remaining input is Matomäki–Radziwiłł's Theorem 2. Its proof runs through mean
values of Dirichlet polynomials, and `formal/GaloisForLFunctions/RHTower/Sieve/DirichletRow.lean`
sets up that frame in the corpus.

- `dirRow N t` — the row `n ↦ n^{it} = exp(it log n)`, `1 ≤ n ≤ N`.
- `norm_dirRow_coord`, `norm_dirRow_sq` — the rows are unimodular coordinatewise, so `‖dirRow‖² = N`.
- `inner_dirRow` — the Gram entry is the exponential sum `∑_{n ≤ N} n^{i(u−t)}`.
- `dirichlet_bessel`, `dirichlet_bilinear` — **Halász–Montgomery for Dirichlet polynomials**: the
  mean square over a family of frequencies is controlled by the largest Gram row, in both the Bessel
  and bilinear pairings.

All unconditional; the almost-orthogonality bound they rest on
(`AlmostOrthogonality.sum_norm_inner_sq_le_of_schur`) was already corpus-owned.

What is *not* proved here, and is the next analytic obligation, is the estimate for
`∑_{n ≤ N} n^{iu}` at `u ≠ 0` — the input that makes the Gram rows small. The corpus's Abel
summation layer is the natural tool. This module is the frame that estimate drops into; it does not
assume it.

### Formal layer — the trivial Dirichlet benchmark

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTrivial.lean` records what the analytic input
must beat.

- `inner_dirRow_self` — the diagonal Gram entry is exactly `N`.
- `norm_inner_dirRow_le` — every Gram entry is at most `N` in modulus.
- `dirichlet_pointwise` — `|F(t)|² ≤ N ∑_n |a_n|²`.
- `dirichlet_bessel_trivial` — `∑_r |F(t_r)|² ≤ R N ∑_n |a_n|²`.

All unconditional and deliberately crude. Their role is to make the content of a genuine mean value
theorem explicit: it is that the *off-diagonal* Gram entries `∑_{n ≤ N} n^{i(u−t)}` are much smaller
than `N` for separated frequencies, so the Gram row is dominated by its diagonal term. Nothing in
the corpus assumes that yet; the next analytic obligation is exactly that estimate.

### Formal layer — the near-diagonal half

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLipschitz.lean`:

- `norm_exp_phase_sub_le` — the phase exponential is 1-Lipschitz, `‖e^{ia} − e^{ib}‖ ≤ |a − b|`
  (the chord never exceeds the arc; proved from the corpus's `norm_exp_I_sub_one`).
- `norm_inner_dirRow_sub_card_le` — **`‖⟪dirRow N t, dirRow N u⟫ − N‖ ≤ |u − t| ∑_{n ≤ N} log n`**.

Both unconditional. This is the *near-diagonal* half of the mean value problem, and it is a genuine
constraint rather than a step: no cancellation whatever is available while the frequencies stay
within `≈ 1/log N` of each other, so any separation hypothesis that a mean value theorem uses must
exceed that scale. It is proved independently of the far-field estimate and does not assume it.

The complementary far-field estimate — cancellation in `∑_{n ≤ N} n^{iv}` for `|v|` large — remains
the open analytic obligation. The corpus's `HTGeometry/DirichletLinePartialSum.lean` carries out
exactly this Euler–Maclaurin comparison for the *one-line* exponent `x^{-1+iα}`; the zero-line case
`x^{iv}` needs the same argument with antiderivative `x^{1+iv}/(1+iv)`, whose telescoped part is of
size `N/|1+iv|` rather than `1/|α|`.

### Formal layer — the zero-line power

`formal/GaloisForLFunctions/RHTower/Sieve/ZeroLinePower.lean` builds the analytic objects the
far-field estimate needs, mirroring `HTGeometry/DirichletLinePartialSum.lean` at the abscissa
`Re s = 0`.

- `zpow0 v x = x^{iv}`, `Zpow0 v x = x^{1+iv}/(1+iv)`.
- `one_add_mul_I_ne_zero` — the denominator never vanishes (its real part is `1`), so no hypothesis
  `v ≠ 0` is needed anywhere in this layer.
- `norm_zpow0` — the power is unimodular.
- `exp_one_add_mul_log`, `norm_Zpow0` — `‖Zpow0 v x‖ = x/‖1+iv‖`.
- `hasDerivAt_zpow0`, `hasDerivAt_Zpow0` — **the antiderivative differentiates to the power**.
- `continuousOn_zpow0`, `intervalIntegrable_zpow0` — the hypotheses an interval integral consumes.

All unconditional. The contrast with the one-line case is the size of the antiderivative: constant
`1/|α|` there, growing like `x` here. That is exactly why `∑_{n ≤ N} n^{iv}` is of size `N/‖1+iv‖`
rather than `O(1)`, and it is the source of the `N` in the mean value theorem.

Remaining for the far-field estimate: the fundamental theorem of calculus on `[k, k+1]`, the
correction bound `‖x^{iv} − k^{iv}‖ ≤ |v|/k` (which follows from `norm_exp_phase_sub_le` already
proved), telescoping, and the harmonic sum — for which `sum_Icc_one_div_le_one_add_log` is in place.

### Formal layer — the far-field estimate

`formal/GaloisForLFunctions/RHTower/Sieve/ZeroLineSum.lean` proves the estimate the mean value
theorem was waiting on.

- `integral_zpow0_eq` — FTC for the zero-line power.
- `norm_zpow0_sub_le` — `‖x^{iv} − k^{iv}‖ ≤ |v|/k` on `[k, k+1]`, from the 1-Lipschitz phase bound
  and `log(x/k) ≤ 1/k`.
- `norm_zpow0_sub_integral_le` — the Euler–Maclaurin correction at one step.
- `norm_sum_zpow0_le` — **`‖∑_{n ≤ N} n^{iv}‖ ≤ (N+2)/‖1+iv‖ + |v|(1 + log N)`**.

All unconditional. For a frequency difference with `1 ≪ |v| ≪ N/log N` this is far below the trivial
bound `N` of `DirichletTrivial.lean`, so the Gram row of a separated family of frequencies is
dominated by its diagonal term — which is precisely the content a mean value theorem needs and which
nothing in the corpus previously supplied.

The two competing terms `N/‖1+iv‖` and `|v| log N` are why a mean value theorem carries both an `N`
and a term growing with the number of frequencies; they cross at `|v| ≍ √(N/log N)`.

### Formal layer — the Gram entry bracketed on both sides

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletFarField.lean` connects the analytic estimate to
the Halász–Montgomery frame.

- `inner_dirRow_eq_sum_zpow0` — **the Gram entry is the zero-line exponential sum**,
  `⟪dirRow N t, dirRow N u⟫ = ∑_{n ≤ N} n^{i(u−t)}`.
- `norm_inner_dirRow_le_far`, `abs_le_norm_one_add_mul_I`, `norm_inner_dirRow_le_gap` —
  **`‖⟪dirRow N t, dirRow N u⟫‖ ≤ (N+2)/|u−t| + |u−t|(1 + log N)`**.

All unconditional. With `DirichletLipschitz.norm_inner_dirRow_sub_card_le` the Gram entry is now
bracketed from both sides: within `|u−t| ≪ 1/log N` of the diagonal it is close to `N`, and once
`|u−t|` exceeds `1` while staying below `N/log N` it is much smaller than `N`. That transition is
the whole content a mean value theorem exploits, and both halves are now proved in the corpus.

### Formal layer — a mean value theorem for Dirichlet polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletMeanValue.lean`:

- `ne_of_gap` — separated frequencies are pairwise distinct.
- `dirichlet_meanValue` — for `F(t) = ∑_{n ≤ N} a_n n^{it}` and frequencies `τ` with consecutive
  gaps at least `δ`, all within a window of length `V`:

  **`∑_{r < R} |F(τ_r)|² ≤ (N + 2(N+2)(1 + log R)/δ + R V (1 + log N)) ∑_n |a_n|²`.**

Unconditional. The diagonal contributes `N`, the reciprocal separations a harmonic sum (bounded by
`SeparatedRowSum.lean`), and the linear term of the far-field estimate the spread. This beats the
trivial `R N` of `DirichletTrivial.lean` whenever `R` is large compared with `log R`, so it is a
genuine mean value theorem rather than a restatement.

It is *not* the sharp Montgomery–Vaughan form. The factor `log R` multiplying `N` is the price of
bounding `∑_{t ≠ r} |τ_t − τ_r|^{-1}` term by term, and `sum_inv_abs_dist_le` proves that price is
unavoidable for any absolute-values argument. That is the same obstruction that caps the large sieve
constant in this folder: the two open quantitative problems in the corpus's analytic layer are one
problem, namely obtaining cancellation in a sum of reciprocal separations rather than bounding it.

### Formal layer — Gallagher's Sobolev lemma

`formal/GaloisForLFunctions/RHTower/Sieve/GallagherSobolev.lean`:

- `gallagher_sobolev` — **`|f(a)| ≤ (2h)^{-1} ∫_{a−h}^{a+h} |f| + ∫_{a−h}^{a+h} |f'|`** for `f` with a
  derivative on the interval and `f'` continuous there.

Unconditional. FTC plus averaging: `f(a) = f(x) + ∫_x^a f'` for every `x` in the interval, so
`|f(a)| ≤ |f(x)| + ∫|f'|`, and integrating in `x` over a window of length `2h` gives the bound.

This opens the route past the obstruction that caps every other constant in this folder. The bound
`sum_inv_abs_dist_le` proves unavoidable applies to arguments that form a sum of reciprocal
separations; Gallagher's proof of the large sieve never forms one. Applied to `|S|²` at separated
points the surrounding intervals are *disjoint*, so the local averages assemble into `∫_0^1 |S|²` and
`∫_0^1 |S||S'|`, which Parseval evaluates — yielding a constant of the sharp shape `N + δ^{-1}` with
no logarithm, for both the large sieve and the Dirichlet mean value theorem.

Remaining for that route: Parseval on the circle for trigonometric polynomials and the derivative
identity `∫ |S'|² = ∑ (2πn)² |a_n|²`, then the disjointness assembly.

### Formal layer — orthogonality of the characters

`formal/GaloisForLFunctions/RHTower/Sieve/CircleOrthogonality.lean`:

- `circleFreq_intCast` — the characters take the value `1` at the integers.
- `circleAnti`, `hasDerivAt_circleAnti` — the explicit antiderivative `e(kt)/(2πik)` of a nonzero
  character.
- `intervalIntegrable_circleFreq_mul` — continuity, hence interval-integrability.
- `integral_circleFreq_intCast` — **`∫_0^1 e(kt) dt = 1` if `k = 0`, else `0`.**

All unconditional, and proved entirely on `[0,1]` with Lebesgue measure via the fundamental theorem
of calculus. This deliberately avoids the additive circle: mathlib's torus Fourier development uses
a file-local `MeasureSpace` instance on `AddCircle` that is not defeq to the global one, so
importing its orthogonality would force the corpus to re-declare that instance. The antiderivative
argument needs none of it — the periodicity that makes the endpoints cancel is just
`e(k) = 1` for integral `k`.

This is the orthogonality that converts `∫_0^1 |S|²` into `∑_n |a_n|²`, the remaining analytic input
for Gallagher's route to the sharp constant.

### Formal layer — the squared modulus of a trigonometric polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/TrigExpansion.lean`:

- `expSum_eq_sum` — the trigonometric polynomial as a sum of characters, `S(t) = ∑_n c_n e(nt)`.
- `normSq_expSum_eq` — **`|S(t)|² = ∑_m ∑_n c_m conj(c_n) e((m−n)t)`**.
- `integral_cross_term` — **`∫_0^1 e((m−n)t) dt = 1` if `m = n`, else `0`**.

All unconditional. These are the two ingredients of Parseval for trigonometric polynomials; the only
step left is interchanging the integral with the two finite sums, after which
`∫_0^1 |S|² = ∑_n |c_n|²` and Gallagher's route to the sharp large sieve constant has all its
analytic inputs.

### Formal layer — Parseval for trigonometric polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/TrigParseval.lean`:

- `intervalIntegrable_circleFreq_sub` — the cross-term characters are interval-integrable.
- `integral_normSq_expSum` — **`∫_0^1 |S(t)|² dt = ∑_{n < N} |c_n|²`** for `S(t) = ∑_{n<N} c_n e(nt)`.

Unconditional. The double sum of `TrigExpansion.lean` is interchanged with the integral (finitely
many integrable terms), orthogonality kills every off-diagonal term, and `c_n conj(c_n) = |c_n|²`
remains on the diagonal.

With `gallagher_sobolev`, `integral_circleFreq_intCast` and this identity, all three analytic inputs
of Gallagher's route to the sharp large sieve are now in the corpus. What remains is the assembly:
the derivative energy `∫_0^1 |S'|² = ∑_n (2πn)² |c_n|²` and the disjointness argument turning local
averages at `δ`-separated points into a single integral over `[0,1]`.

### Formal layer — the derivative energy

`formal/GaloisForLFunctions/RHTower/Sieve/TrigDerivative.lean`:

- `hasDerivAt_circleFreq_mul` — the derivative of a single character.
- `derivCoeff`, `hasDerivAt_expSum` — **the derivative of a trigonometric polynomial is again one**,
  with coefficients multiplied by `2πin`.
- `integral_normSq_derivCoeff` — **`∫_0^1 |S'|² = ∑_{n<N} (2πn)² |c_n|²`**.

All unconditional. Because the derivative is itself a trigonometric polynomial, its energy needs no
new analysis: Parseval applies to the new coefficient vector, and the norm computation
`‖2πin·c_n‖ = 2πn‖c_n‖` finishes it.

Both integrals appearing in Gallagher's Sobolev bound are now expressed in the coefficient energy.
The only remaining step to the sharp large sieve constant is the disjointness assembly: at
`δ`-separated points the surrounding intervals of length `δ` do not overlap, so summing the local
bounds gives one integral over `[0,1]` and the constant `N + δ^{-1}` in place of the logarithmic one.

### Formal layer — the derivative of the squared modulus

`formal/GaloisForLFunctions/RHTower/Sieve/TrigNormSqDeriv.lean`:

- `continuous_expSum` — a trigonometric polynomial is continuous.
- `hasDerivAt_normSq_expSum` — **`(|S|²)' = ⟪S, S'⟫ + ⟪S', S⟫`**, obtained by writing the squared
  modulus as the *real* inner product `⟪S, S⟫` on `ℂ` and differentiating the bilinear pairing.
- `abs_deriv_normSq_le` — **`|(|S|²)'| ≤ 2‖S‖‖S'‖`** by Cauchy–Schwarz.

All unconditional. Viewing `|z|²` as a real inner product rather than `re² + im²` avoids
differentiating the components separately; mathlib's `HasDerivAt.inner` then gives the product rule
in one step.

Gallagher's Sobolev bound applied to `f = |S|²` now has both of its integrals expressed in `|S|` and
`|S'|`, which Parseval and the derivative energy evaluate. The remaining step is the disjointness
assembly at `δ`-separated points.

### Formal layer — Gallagher's bound at a point

`formal/GaloisForLFunctions/RHTower/Sieve/GallagherPointwise.lean`:

- `gallagher_at_point` — **`|S(a)|² ≤ δ^{-1} ∫_{a−δ/2}^{a+δ/2} |S|² + ∫_{a−δ/2}^{a+δ/2} 2|S||S'|`**
  for any trigonometric polynomial `S` and any `δ > 0`.

Unconditional, and with no integrability side conditions: every ingredient is continuous, so the
Sobolev lemma's hypotheses are discharged from `continuous_expSum` alone.

This is the local half of Gallagher's argument, now in a form specialised to trigonometric
polynomials. The remaining step is global: the windows of length `δ` around `δ`-separated points are
pairwise disjoint, so summing this bound over such a family replaces the local integrals by a single
integral over one period, which `TrigParseval.lean` and `TrigDerivative.lean` evaluate as
`∑_n |c_n|²` and `∑_n (2πn)²|c_n|²`. That yields the constant `N + δ^{-1}` in place of the
logarithmic one — the sharp shape.

### Formal layer — disjoint windows

`formal/GaloisForLFunctions/RHTower/Sieve/WindowDisjointness.lean`:

- `sum_window_le` — **`∑_{r ≤ R} ∫_{λ_r−δ/2}^{λ_r+δ/2} g ≤ ∫_A^{λ_R+δ/2} g`** for continuous
  nonnegative `g` and points with consecutive gaps at least `δ`.

Unconditional. The separation gives `λ_r + δ/2 ≤ λ_{r+1} − δ/2`, so the windows do not overlap and
the induction step splits the enclosing integral into the part already counted, a gap carrying a
nonnegative integrand, and the new window. No measure theory beyond additivity over adjacent
intervals is used — in particular no `Set.PairwiseDisjoint` or `integral_iUnion`, which the ordered
case makes unnecessary.

This is the global half of Gallagher's argument. Applied to `g = |S|²` and `g = 2|S||S'|` it converts
the local bounds of `GallagherPointwise.lean` into integrals over a single enclosing interval, which
`TrigParseval.lean` and `TrigDerivative.lean` evaluate in the coefficient energy.

### Formal layer — Gallagher's bound over a separated family

`formal/GaloisForLFunctions/RHTower/Sieve/GallagherSum.lean`:

- `gallagher_sum` — **`∑_{r ≤ R} |S(λ_r)|² ≤ δ^{-1} ∫_A^{λ_R+δ/2} |S|² + ∫_A^{λ_R+δ/2} 2|S||S'|`**
  for points with consecutive gaps at least `δ`.

Unconditional. The right-hand side no longer mentions the points at all — only the enclosing
interval. That is the substance of the method: no sum of reciprocal separations is ever formed, so
the logarithmic loss `sum_inv_abs_dist_le` proves unavoidable for term-by-term arguments simply does
not arise here.

What remains to the sharp constant is arithmetic on the right-hand side: Cauchy–Schwarz on
`∫ |S||S'|`, then `TrigParseval.lean` and `TrigDerivative.lean` to replace the two integrals by
`∑_n |c_n|²` and `∑_n (2πn)² |c_n|²`, giving `δ^{-1} + 4πN` in place of the current
`N + O(δ^{-1} log δ^{-1})`.

### Formal layer — splitting the mixed term

`formal/GaloisForLFunctions/RHTower/Sieve/AmGmIntegral.lean`:

- `two_mul_le_amgm` — `2ab ≤ ε a² + ε^{-1} b²` for every `ε > 0`, from `(εa − b)² ≥ 0`.
- `integral_mixed_le` — **`∫ 2|S||S'| ≤ ε ∫ |S|² + ε^{-1} ∫ |S'|²`**.

Both unconditional. The pointwise inequality is used rather than Cauchy–Schwarz for integrals: it
keeps the argument elementary, avoids any `L^p` theory, and leaves `ε` free so the two contributions
can be balanced at the end. Choosing `ε = 2πN` will make both equal, since the derivative energy
carries the factor `(2πN)²`.

With `gallagher_sum` this reduces the sharp large sieve to the two energies alone. What remains is
substituting Parseval and the derivative energy over a full period and choosing `ε`.

### Formal layer — the large sieve with the SHARP constant

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveGallagher.lean`:

- `gallagher_period` — Gallagher's bound with both integrals over a full period.
- `largeSieve_gallagher` — **`∑_{r ≤ R} |S(λ_r)|² ≤ (δ^{-1} + 4πN) ∑_{n < N} |c_n|²`** for
  `S(t) = ∑_{n<N} c_n e(nt)` and points inside one period with consecutive gaps at least `δ`.

Unconditional. **The constant has the sharp shape `N + δ^{-1}` — the logarithm is gone.**

This settles the quantitative question left open by the earlier chain in this folder. The weak form
(`largeSieve_separated_explicit`) carries `Δ = N + O(δ^{-1} log δ^{-1})`, and `sum_inv_abs_dist_le`
proves that logarithm is unavoidable for *any* argument that bounds `∑_{t ≠ r} |λ_t − λ_r|^{-1}` term
by term. Gallagher's route reaches the sharp constant by never forming that sum at all: the local
Sobolev bounds at the separated points are absorbed into a single integral over the period by
disjointness of their windows, and the two resulting energies are evaluated by Parseval and the
derivative energy, with the AM–GM parameter set to `2πN` to balance them.

Both statements now coexist in the corpus, and neither contradicts the other: the no-go applies to
the method, not to the theorem.

### Formal layer — the sharp large sieve for finitely many points

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveFinite.lean`:

- `extendSeq`, `extendSeq_of_le`, `gap_extendSeq` — a finite family of points continued
  arithmetically past the last one; the continuation keeps the gap at every step and changes nothing
  below `R`.
- `largeSieve_gallagher_finite` — **`∑_{r ≤ R} |S(λ_r)|² ≤ (δ^{-1} + 4πN) ∑_{n<N} |c_n|²`**, needing
  the gap only between consecutive points that are actually used.

All unconditional. `largeSieve_gallagher` asks for a sequence whose *every* consecutive gap is at
least `δ`, which no application can supply — points come in finite families. The arithmetic
continuation removes that mismatch without touching the proof.

Note that `gap_extendSeq` needs no positivity hypothesis on `δ`: continuing by arithmetic steps
preserves the inequality whatever the sign, and the linter caught the unused assumption.

### Formal layer — the sharp large sieve for a separated set

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveFinset.lean`:

- `largeSieve_gallagher_finset` — **`∑_{x ∈ s} |S(x)|² ≤ (δ^{-1} + 4πN) ∑_{n<N} |c_n|²`** for any
  finite `s ⊆ [δ/2, 1−δ/2]` whose distinct elements are `δ` apart.

Unconditional. Applications supply a *set* with pairwise separation, never an increasing sequence;
listing the set in increasing order (`Finset.orderIsoOfFin`) converts pairwise separation into
consecutive separation, because for an increasing enumeration the consecutive gap is the smallest
one. The reindexing of the sum is the order isomorphism.

The sharp constant is now available in the form a sieve argument consumes — the same interface as
the weak `largeSieve_separated_explicit`, but with `δ^{-1} + 4πN` in place of
`N + O(δ^{-1} log δ^{-1})`. For the Farey set of order `Q` (`δ = Q^{-2}`, established by
`fareySet_sep`) this reads `Q² + 4πN`, the classical `N + Q²` up to the constant.

### Formal layer — the sharp bound from circle separation

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveCircleSharp.lean`:

- `toIntDist_le_abs` — the circle distance never exceeds the ordinary one (it is the distance to the
  *nearest* integer, and `0` is one of them).
- `largeSieve_gallagher_circle` — **the sharp bound `(δ^{-1} + 4πN)` under a `ℝ/ℤ`-separation
  hypothesis**, which is the form arithmetic families supply.

Unconditional. This is the last interface mismatch: `fareySet_sep` and every other arithmetic
separation statement in this folder bound `toIntDist`, whereas Gallagher's argument is stated for
real separation. Circle separation is the stronger hypothesis, so the implication is one lemma.

Caveat recorded for the Farey instantiation: `fareySet Q` as defined here contains the pair `(1,1)`,
whose value is the endpoint `1`, and the window condition `x + δ/2 ≤ 1` excludes it. The set the
sharp bound applies to is the *proper* Farey set `1 ≤ a < q ≤ Q`, which lies in
`[Q^{-1}, 1 − Q^{-1}] ⊆ [δ/2, 1 − δ/2]` for `δ = Q^{-2}`. That restriction is genuine, not an
artefact — the endpoint and `0` are the same point of `ℝ/ℤ`, so they cannot both sit in an interval
of the line.

### Formal layer — the SHARP arithmetic large sieve

`formal/GaloisForLFunctions/RHTower/Sieve/FareySharp.lean`:

- `properFareySet`, `properFareyReals`, `mem_properFareySet` — the proper Farey fractions of order
  `Q` (reduced `a/q` with `1 ≤ a < q ≤ Q`) and their values.
- `largeSieve_farey_sharp` — **`∑_{a/q} |S(a/q)|² ≤ (Q² + 4πN) ∑_{n<N} |c_n|²`** for `Q ≥ 2`.

Unconditional. This is the classical `N + Q²` up to the absolute constant, with **no logarithm** —
the arithmetic form of the sharp large sieve, and the endpoint of the Gallagher construction begun
sixteen modules ago.

Compare `largeSieve_expSum_farey` earlier in this folder, which gives
`N + Q²(1 + log(Q²/2 + 1))` over the full Farey set. Both are proved; the sharp one restricts to the
proper fractions, for the reason recorded above: `1/1` has value `1`, the same point of `ℝ/ℤ` as `0`,
and no interval of the line can contain both while keeping the family separated.

The route's large-sieve input is therefore complete at the classical strength, in both the
inner-product, exponential-sum, and arithmetic formulations.

### Formal layer — the sharp sieve indexed by fractions

`formal/GaloisForLFunctions/RHTower/Sieve/FareySharpSet.lean`:

- `properFarey_val_injOn` — distinct proper Farey fractions have distinct values (immediate from the
  separation, since a zero circle distance would contradict it).
- `sum_properFareyReals_eq` — the sum over values equals the sum over fractions.
- `largeSieve_set_properFarey` — **`∑_{1 ≤ a < q ≤ Q, (a,q)=1} |∑_{n ∈ A} e(na/q)|² ≤
  (Q² + 4πN)|A|`** for `A ⊆ [0,N)`.

Unconditional. `largeSieve_farey_sharp` is indexed by the *values* of the fractions, but a sieve
application presents them as pairs `(a,q)`; the two indexings agree because the values are distinct.
Specialising to an indicator gives the sharp bound in exactly the shape `MontgomerySieve.lean`
consumes.

For a prime denominator `p`, the proper fractions are `a/p` with `1 ≤ a < p` — precisely the nonzero
residues, which is what `fareySet_fibre_prime` already produces. So Montgomery's sieve inequality can
be re-derived with the constant `N + Q²` in place of `N + Q²(1 + log(Q²/2+1))` with no change to its
combinatorial half.

### Formal layer — Montgomery's sieve with the sharp constant

`formal/GaloisForLFunctions/RHTower/Sieve/MontgomerySharp.lean`:

- `properFareySet_fibre_prime` — at a prime denominator the Farey fibre is *already* proper, since a
  numerator coprime to a prime and at most it is strictly less than it.
- `montgomery_sieve_sharp` — **`|A| ∑_{p ∈ P} (p − c_p)/c_p ≤ Q² + 4πN`**.

Unconditional. This is the classical `N + Q²` in place of the earlier `N + Q²(1 + log(Q²/2+1))`. The
combinatorial half of the argument is unchanged: restricting to proper fractions costs nothing at
prime moduli, which is exactly what `properFareySet_fibre_prime` establishes, so only the analytic
input was swapped.

Both versions remain in the corpus. `montgomery_sieve` applies to any family of primes with the
weaker constant and no lower bound on `Q`; `montgomery_sieve_sharp` needs `Q ≥ 2` and `N ≥ 1` and
gives the classical constant.

### Formal layer — the sieve bound at the classical constant

`formal/GaloisForLFunctions/RHTower/Sieve/SieveBoundSharp.lean`:

- `card_mul_omitted_le_sharp` — **`|A| ∑_{p ∈ P} w_p/(p − w_p) ≤ Q² + 4πN`**.
- `card_le_of_sieve_sharp` — **`|A| ≤ (Q² + 4πN)/L`**.
- `card_le_of_half_omitted_sharp` — **`|A| ≤ 3(Q² + 4πN)/|P|`** for a set missing at least half the
  classes modulo each prime of `P`.

All unconditional. Only the analytic input differs from the logarithmic versions; `deficiency_ge`
and the `1/3` of `third_le_ratio` are reused unchanged, so the two families of statements share their
combinatorial content and differ exactly in the large sieve they invoke.

The sieve layer is therefore complete at classical strength in every formulation the route uses:
inner-product, exponential-sum, arithmetic (Farey), Montgomery's inequality, and the usable
cardinality bounds.

### Formal layer — Dirichlet polynomials and their derivatives

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletPoly.lean`:

- `dirPoly`, `dirDerivCoeff` — `F(t) = ∑_{n<N} a_n n^{it}` and the coefficients of its derivative.
- `hasDerivAt_exp_phase`, `continuous_dirPoly`, `hasDerivAt_dirPoly` — **the derivative of a
  Dirichlet polynomial is again one**, with coefficients multiplied by `i log n`.
- `hasDerivAt_normSq_dirPoly`, `abs_deriv_normSq_dirPoly_le` — `(|F|²)' = ⟪F,F'⟫ + ⟪F',F⟫` and
  `|(|F|²)'| ≤ 2‖F‖‖F'‖`.

All unconditional. These are the inputs Gallagher's Sobolev bound needs to control `F` at separated
points by integrals over an interval, which is the first step of every large-values argument for
Dirichlet polynomials.

One structural difference from the trigonometric case, recorded so it is not assumed away: there is
no Parseval for Dirichlet polynomials on a finite interval. `∫_0^T |F|²` is *not* `T ∑_n |a_n|²` — the
error term is exactly the Montgomery–Vaughan mean value theorem, whose sharp form needs the Hilbert
inequality this folder does not own. So the reduction to the integrals is what this layer supplies;
their evaluation is a separate obligation and is not smuggled in.

### Formal layer — Gallagher's reduction for Dirichlet polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletGallagher.lean`:

- `gallagher_dirPoly_at_point` — `|F(x)|² ≤ δ^{-1} ∫_{x−δ/2}^{x+δ/2} |F|² + ∫ 2|F||F'|`.
- `gallagher_dirPoly_sum` — **`∑_{r ≤ R} |F(t_r)|² ≤ δ^{-1} ∫_A^{t_R+δ/2} |F|² + ∫_A^{t_R+δ/2}
  2|F||F'|`** for points with consecutive gaps at least `δ`.

Both unconditional, and both are instantiations of the *general* `gallagher_sobolev` and
`sum_window_le` — those were stated for an arbitrary continuous function, so the Dirichlet case
needed no new analysis, only the derivative facts of `DirichletPoly.lean`.

The right-hand side depends on the points only through the enclosing interval: the discrete sum has
been traded for a continuous mean, which is the standard first step of a large-values argument.

The two integrals are *not* evaluated, and cannot be by the trigonometric route: Parseval has no
finite-interval analogue for Dirichlet polynomials. Supplying one is the Montgomery–Vaughan mean
value theorem, which remains open in this corpus alongside Matomäki–Radziwiłł.

### Formal layer — integrals of a pure phase

`formal/GaloisForLFunctions/RHTower/Sieve/PhaseIntegral.lean`:

- `integral_exp_phase_zero` — `∫_0^T e^{it·0} dt = T`.
- `integral_exp_phase` — `∫_0^T e^{itL} dt = (e^{iTL} − 1)/(iL)` for `L ≠ 0`.
- `norm_integral_exp_phase_le` — **`‖∫_0^T e^{itL} dt‖ ≤ 2/|L|`**.

All unconditional. These are the cross-term integrals of `∫_0^T |F|²` for a Dirichlet polynomial:
the diagonal terms have `L = 0` and contribute `T ∑_n |a_n|²`, while the off-diagonal terms carry
`L = log m − log n` and are bounded by `2/|log(m/n)|`.

This is the dichotomy that extracts the diagonal from the mean square — the identity underlying the
Montgomery–Vaughan mean value theorem. What that theorem adds beyond this is the bound on the
resulting off-diagonal sum `∑_{m≠n} |a_m||a_n| / |log(m/n)|`, which is a Hilbert inequality for the
frequencies `log n` and remains the open input.

### Formal layer — the squared modulus of a Dirichlet polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExpansion.lean`:

- `exp_phase_mul_conj` — a phase times the conjugate of a phase is the phase of the difference.
- `log_succ_injective` — distinct indices give distinct frequencies, so the off-diagonal bound
  `2/|log(m/n)|` never divides by zero.
- `normSq_dirPoly_eq` — **`|F(t)|² = ∑_m ∑_n a_m conj(a_n) e^{it(log m − log n)}`**.

All unconditional. Each cross term is a pure phase, so integrating over `[0,T]` and applying the
dichotomy of `PhaseIntegral.lean` separates the diagonal (frequency zero, integral `T`) from the
off-diagonal (integral at most `2/|log(m/n)|`).

`log_succ_injective` is recorded separately because it is the fact that makes the off-diagonal bound
meaningful at all: without it the frequencies could coincide for distinct indices and the `2/|L|`
estimate would be vacuous.

### Formal layer — the mean square of a Dirichlet polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletMeanSquare.lean`:

- `integral_normSq_dirPoly_eq` — **`∫_0^T |F|² = ∑_m ∑_n a_m conj(a_n) ∫_0^T e^{it(log m − log n)}`**,
  the termwise integration of the expansion.
- `integral_dirPhase_diag` — the diagonal phase integral is `T`.
- `norm_integral_dirPhase_off` — the off-diagonal ones are at most `2/|log(m/n)|`.

All unconditional. The diagonal therefore contributes `T ∑_n |a_n|²` and the remainder is an
off-diagonal sum of reciprocal logarithmic separations, weighted by `|a_m||a_n|`.

That remainder is exactly where Montgomery–Vaughan enters, and it is *not* bounded here. Controlling
`∑_{m≠n} |a_m||a_n| / |log(m/n)|` by `∑_n |a_n|²·O(n)` is a Hilbert inequality for the frequencies
`log n` — the same obstruction `sum_inv_abs_dist_le` proves fatal to term-by-term arguments. On the
circle that obstruction was bypassed by Gallagher's method using periodicity; the frequencies `log n`
are not periodic, so the bypass does not transfer, and this is the honest boundary of the corpus's
Dirichlet layer.

### Formal layer — the diagonal extracted

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletDiagonal.lean`:

- `integral_normSq_dirPoly_sub_diag` — **`∫_0^T |F|² − T ∑_n |a_n|² = ∑_m ∑_{n ≠ m} a_m conj(a_n)
  ∫_0^T e^{it(log m − log n)}`**, an exact identity.
- `norm_integral_normSq_dirPoly_sub_diag_le` — **`‖∫_0^T |F|² − T ∑_n |a_n|²‖ ≤
  ∑_m ∑_{n ≠ m} |a_m||a_n| · 2/|log(m/n)|`**.

Both unconditional. The mean value theorem for Dirichlet polynomials is now reduced to a single
inequality: everything still missing is a bound for that off-diagonal sum.

Stated plainly, the corpus's position on this problem: the reduction is complete and exact, and the
remaining input is a Hilbert inequality for the frequencies `log n`. The circle case was settled by
Gallagher's method, but that method used periodicity — disjoint windows inside one period, and
Parseval to evaluate the resulting integrals — and neither ingredient exists for `log n`. So the
Dirichlet mean value theorem is not a corollary of what this folder proved for the large sieve; it
is a genuinely separate obligation, and it sits alongside Matomäki–Radziwiłł as the route's open
input.

### Formal layer — logarithmic separation

`formal/GaloisForLFunctions/RHTower/Sieve/LogSeparation.lean`:

- `log_sub_ge` — `log x − log y ≥ (x−y)/x` for `0 < y ≤ x`, from `log(y/x) ≤ y/x − 1`.
- `abs_log_succ_sub_ge` — **`|log(m+1) − log(n+1)| ≥ |m − n|/N`** for `m, n < N`.
- `two_div_abs_log_le` — **`2/|log(m/n)| ≤ 2N/|m − n|`**.

All unconditional. This corrects the assessment recorded two batches ago. The off-diagonal sum of the
Dirichlet mean square does *not* require a Hilbert inequality at the frequencies `log n` in order to
be bounded at all — only to be bounded *sharply*. Comparing the logarithmic separation with the
integer separation costs a factor `N`, and `N` is already the size of the mean value theorem's error
term, so the elementary comparison suffices for a mean value theorem with an `N log N` error.

Concretely: `∑_{m≠n} |a_m||a_n| · 2/|log(m/n)| ≤ 2N ∑_{m≠n} |a_m||a_n|/|m−n|`, and the right-hand
side is controlled by AM–GM plus the harmonic row sum. Montgomery–Vaughan remains needed for the
sharp error `O(N)`; it is not needed for `O(N log N)`.

### Formal layer — the integer row sum

`formal/GaloisForLFunctions/RHTower/Sieve/IntegerRowSum.lean`:

- `sum_inv_abs_int_dist_le` — **`∑_{n < N, n ≠ m} |n − m|^{-1} ≤ 2(1 + log N)`**.

Unconditional, and obtained by instantiating `SeparatedRowSum.sum_inv_abs_dist_le` at the arithmetic
progression `λ_i = i` with gap `1`, then applying the closed-form harmonic bound. No new argument
was needed: the general separated row sum proved early in this folder specialises directly.

This is the row sum that appears once `LogSeparation.lean` has traded the logarithmic separations of
a Dirichlet polynomial for integer ones. With AM–GM to decouple `|a_m||a_n|` it gives the mean value
theorem with error `O(N log N)`.

### Formal layer — the row sum over `Fin N`

`formal/GaloisForLFunctions/RHTower/Sieve/FinRowSum.lean`:

- `sum_erase_inv_abs_eq`, `sum_erase_inv_abs_range_eq` — erasing the diagonal changes neither sum.
- `sum_inv_abs_fin_dist_le` — **`∑_{n ≠ m} |n − m|^{-1} ≤ 2(1 + log N)` over `Fin N`**.

Unconditional. The Dirichlet sums of this folder are indexed by `Fin N` while the row sum was proved
over `range N`; the transfer is immediate once one notices that the omitted diagonal term is
`|m − m|^{-1} = 0` under Lean's `1/0 = 0` convention, so both erased sums equal their full sums and
`Fin.sum_univ_eq_sum_range` identifies those.

That convention is usually a nuisance; here it removes the need for any bijection between
`univ.erase m` and `(range N).erase m`.

### Formal layer — swapping the off-diagonal double sum

`formal/GaloisForLFunctions/RHTower/Sieve/OffDiagonalSwap.lean`:

- `sum_erase_eq_sum_ite` — an erased sum is the full sum with the diagonal term zeroed.
- `sum_erase_swap` — **`∑_m ∑_{n ≠ m} g m n = ∑_n ∑_{m ≠ n} g m n`**.

Unconditional. `Finset.sum_comm` cannot be applied to iterated sums whose inner index set depends on
the outer index; rewriting `univ.erase m` as `univ` with the diagonal zeroed removes that dependence
and makes the swap a one-line application.

This is the decoupling step for the Dirichlet mean value theorem: it identifies the two halves of
`∑_m ∑_{n ≠ m} (|a_m|² + |a_n|²) K(m,n)` for a symmetric kernel `K`, so the AM–GM bound on
`|a_m||a_n|` collapses to a single row sum.

### Formal layer — the off-diagonal sum bounded

`formal/GaloisForLFunctions/RHTower/Sieve/OffDiagonalBound.lean`:

- `offDiagonal_le` — **`∑_m ∑_{n ≠ m} |a_m||a_n| · 2/|log(m/n)| ≤ 4N(1 + log N) ∑_m |a_m|²`**.

Unconditional. Three steps, each already in the corpus: `LogSeparation` trades logarithmic
separations for integer ones at a cost of `N`; AM–GM decouples `|a_m||a_n|` into
`(|a_m|² + |a_n|²)/2`; `OffDiagonalSwap` identifies the two resulting halves, each a row sum bounded
by `2(1 + log N)` via `FinRowSum`.

Combined with `norm_integral_normSq_dirPoly_sub_diag_le` this gives the mean value theorem for
Dirichlet polynomials with error `O(N log N)`:

`‖∫_0^T |F|² − T ∑_n |a_n|²‖ ≤ 4N(1 + log N) ∑_n |a_n|²`.

The sharp Montgomery–Vaughan error `O(N)` still requires the Hilbert inequality at the frequencies
`log n`; the `log N` here is the price of the elementary comparison, exactly as the `log` in the weak
large sieve was.

### Formal layer — THE MEAN VALUE THEOREM FOR DIRICHLET POLYNOMIALS

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletMVT.lean`:

- `dirichlet_meanValue_complex`, `dirichlet_meanValue_theorem` —

  **`|∫_0^T |F(t)|² dt − T ∑_{n<N} |a_n|²| ≤ 4N(1 + log N) ∑_{n<N} |a_n|²`**

  for `F(t) = ∑_{n<N} a_n n^{it}`.

Unconditional. This is the mean value theorem for Dirichlet polynomials, with error `O(N log N)`.

Corrected assessment: an earlier entry on this card reported the theorem as blocked behind
Montgomery–Vaughan. That was wrong — Montgomery–Vaughan is needed only for the *sharp* error `O(N)`.
The elementary comparison between logarithmic and integer separations (`LogSeparation.lean`) costs a
factor `N`, which is already the order of the error term, so `O(N log N)` follows from material this
folder owns.

Route status: the Dirichlet-polynomial layer now has the reduction (`DirichletGallagher`), the
mean value theorem, and the large sieve at classical strength. The card's stated remaining input,
Matomäki–Radziwiłł Theorem 2, is unchanged.

### Formal layer — the derivative energy

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletDerivEnergy.lean`:

- `norm_dirDerivCoeff` — `‖i log n · a_n‖ = log n · ‖a_n‖`.
- `sum_normSq_dirDerivCoeff_le` — **`∑_{n<N} ‖i log n · a_n‖² ≤ (log N)² ∑_{n<N} ‖a_n‖²`**.

Unconditional. The largest frequency of a Dirichlet polynomial of length `N` is `log N`, so
differentiation multiplies the energy by at most `(log N)²`.

Applying the mean value theorem to `F'` — itself a Dirichlet polynomial with these coefficients —
bounds `∫_0^T |F'|²`, the second integral in Gallagher's reduction. With that and `∫_0^T |F|²`, the
reduction of `DirichletGallagher.lean` becomes a large-values estimate: a bound on
`∑_r |F(t_r)|²` at separated points purely in terms of `T`, `N` and the coefficient energy.

### Formal layer — both integrals of Gallagher's reduction

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletIntegralBound.lean`:

- `integral_normSq_dirPoly_le` — **`∫_0^T |F|² ≤ (T + 4N(1 + log N)) ∑_n |a_n|²`**.
- `window_factor_nonneg` — the factor `T + 4N(1 + log N)` is nonnegative for `T ≥ 0`.
- `integral_normSq_dirPoly_deriv_le` — **`∫_0^T |F'|² ≤ (T + 4N(1 + log N))(log N)² ∑_n |a_n|²`**.

All unconditional. The second follows from the first applied to `F'`, which is itself a Dirichlet
polynomial whose coefficient energy is at most `(log N)²` times that of `F`.

Both integrals appearing in `gallagher_dirPoly_sum` are now controlled by `T`, `N` and the
coefficient energy alone, so that reduction is no longer conditional on evaluating them. Feeding
these bounds in — with the AM–GM split of `AmGmIntegral.lean` for the mixed term — yields a
large-values estimate for Dirichlet polynomials at separated points.

### Formal layer — splitting the mixed term for Dirichlet polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/AmGmDirichlet.lean`:

- `integral_mixed_dirPoly_le` — **`∫_A^B 2|F||F'| ≤ ε ∫_A^B |F|² + ε^{-1} ∫_A^B |F'|²`** for every
  `ε > 0`.

Unconditional. The pointwise inequality `two_mul_le_amgm` is shared with the trigonometric case; only
the continuity and integrability facts differ, and those come from `continuous_dirPoly`.

Every ingredient of a large-values estimate for Dirichlet polynomials is now present: the Gallagher
reduction (`DirichletGallagher`), bounds for both integrals (`DirichletIntegralBound`), and this
split. Choosing `ε = log N` — the largest frequency — equalises the two contributions and gives a
bound of the shape `(T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_n |a_n|²`.

### Formal layer — A LARGE-VALUES ESTIMATE FOR DIRICHLET POLYNOMIALS

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLargeValues.lean`:

- `largeValues_dirPoly` —

  **`∑_{r ≤ R} |F(t_r)|² ≤ (T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_{n<N} |a_n|²`**

  for `F(t) = ∑_{n<N} a_n n^{it}`, `N ≥ 2`, and points in `[δ/2, T − δ/2]` with consecutive gaps at
  least `δ`.

Unconditional. Gallagher's reduction trades the discrete sum for two integrals over `[0,T]`, the
mixed one is split with balancing parameter `log N`, and both are bounded by the mean value theorem.

This is the estimate a large-values or zero-density argument consumes, and it completes the Dirichlet
layer: reduction, mean value theorem, derivative energy, and now the large-values bound itself — all
unconditional and all at `log`-lossy but usable strength.

### Formal layer — counting large values

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLargeValuesCount.lean`:

- `card_largeValues_le` — **`(R+1)V² ≤ (T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_{n<N} |a_n|²`**
  whenever `|F| ≥ V` at `R+1` points separated by `δ` inside `[δ/2, T − δ/2]`.

Unconditional. This is the form in which a large-values estimate is used — a cap on how often a
Dirichlet polynomial can be large — rather than a bound on a sum the caller would have to unpack.

With this the corpus's analytic layer for Route E stands complete at usable strength: the large sieve
(sharp), Montgomery's sieve (sharp), the Dirichlet mean value theorem, and the large-values estimate
with its counting form. The card's stated remaining input is unchanged: Matomäki–Radziwiłł Theorem 2.

### Corpus check — Plancherel IS in mathlib (2026-08-03)

Recorded to prevent a future session from building it.

`Mathlib/Analysis/Fourier/LpSpace.lean` supplies the `L²` Fourier theory this route's remaining
input needs:

- `fourierTransformₗᵢ : Lp F 2 ≃ₗᵢ[ℂ] Lp F 2` — the Fourier transform as a linear *isometric
  equivalence* on `L²`;
- `norm_fourier_eq : ‖𝓕 f‖ = ‖f‖` — Plancherel;
- `inner_fourier_eq : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` — Parseval;
- `SchwartzMap.toLp_fourier_eq`, `fourier_toTemperedDistribution_eq` — compatibility with the
  Schwartz and tempered-distribution pictures.

So the Parseval bridge Matomäki–Radziwiłł uses — passing from a short-interval average to an
integral of a Dirichlet polynomial — is an **instantiation** problem, not a construction problem.
The analytic engine exists; what has to be built is the arithmetic side: exhibiting the
short-interval average as an `L²` Fourier pair, which means a logarithmic change of variable turning
the Dirichlet series into a function on `ℝ` and identifying the resulting kernel.

Note the earlier assessment on these cards that "nothing in mathlib approaches" the remaining input
is correct about Matomäki–Radziwiłł itself and about Menon's theorem, but should not be read as
covering their analytic prerequisites: Plancherel, the large sieve, the Dirichlet mean value theorem
and the large-values estimate are all now available, the last three from this corpus.

### Formal layer — pairing a Dirichlet polynomial against a kernel

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletPairing.lean`:

- `integral_dirPoly_mul` — **`∫_A^B F(t)K(t) dt = ∑_{n<N} a_n ∫_A^B n^{it} K(t) dt`** for continuous
  `K`.

Unconditional. For a *finite* Dirichlet polynomial this is linearity of the integral, so no
convergence question arises — which is why it can be stated with no hypothesis on `K` beyond
continuity, and on any interval.

This is the finite form of the Parseval bridge. The inner integral is the transform of the kernel at
the frequency `log n`, so pairing against a kernel evaluates the coefficient sum against that
transform. Choosing `K` to concentrate near a point turns the left side into a short-interval average
and the right side into a weighted coefficient sum — the shape Matomäki–Radziwiłł's argument works
in. With `norm_fourier_eq` available from mathlib, what remains on this route is the choice of kernel
and the estimation of its transform, not the construction of the transform theory.

### Formal layer — the symmetric phase integral (Dirichlet kernel)

`formal/GaloisForLFunctions/RHTower/Sieve/SymmetricPhaseIntegral.lean`:

- `exp_phase_sub_neg` — `e^{iθ} − e^{−iθ} = 2i sin θ`.
- `integral_exp_phase_symm_zero` — `∫_{−T}^{T} e^{it·0} dt = 2T`.
- `integral_exp_phase_symm` — **`∫_{−T}^{T} e^{itL} dt = 2 sin(TL)/L`** for `L ≠ 0`.

All unconditional. Paired with a Dirichlet polynomial through `integral_dirPoly_mul`, this *is* the
Dirichlet kernel: `∫_{−T}^{T} F(t) dt = ∑_n a_n · 2 sin(T log n)/log n`, and twisting by `x^{−it}`
moves the frequencies to `log(n/x)`, so the kernel concentrates on `n ≈ x` with width `e^{1/T}`. Its
modulus is at most `min(2T, 2/|L|)`, which is what makes far frequencies negligible.

That is the concrete kernel the Parseval bridge needs; with `integral_dirPoly_mul` supplying the
pairing and mathlib supplying Plancherel, the short-interval side of Matomäki–Radziwiłł is now a
matter of estimating this kernel rather than of building transform theory.

### Formal layer — the Dirichlet kernel against a Dirichlet polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletKernelPairing.lean`:

- `norm_integral_exp_phase_symm_le_inv` — the kernel decays: `‖∫_{−T}^{T} e^{itL}‖ ≤ 2/|L|`.
- `norm_integral_exp_phase_symm_le_len` — and is capped by the interval: `≤ 2T`.
- `integral_dirPoly_symm` — **`∫_{−T}^{T} F(t) dt = ∑_{n<N} a_n ∫_{−T}^{T} n^{it} dt`**.

All unconditional. The two bounds are what make the pairing *selective*: near the trivial frequency
the kernel has size `2T`, and away from it the kernel decays like the reciprocal of the frequency.
After a twist by `x^{−it}` the frequencies become `log(n/x)`, so the pairing localises the
coefficient sum to `n ≈ x` — which is the mechanism by which a short-interval average is read off a
Dirichlet polynomial.

The short-interval side of the route is therefore assembled from proved parts: pairing identity,
explicit kernel, decay and cap. What is not yet built is the quantitative localisation — turning
these into an approximation of the short-interval sum with a controlled error.

### Formal layer — linear weights against a phase

`formal/GaloisForLFunctions/RHTower/Sieve/LinearPhaseIntegral.lean`:

- `linPhaseAnti`, `hasDerivAt_linPhaseAnti` — the explicit antiderivative
  `t e^{itL}/(iL) − e^{itL}/(iL)²` of `t e^{itL}`.
- `intervalIntegrable_linPhase`, `integral_linPhase` — the resulting closed-form integral on any
  interval.

All unconditional. With the constant case of `SymmetricPhaseIntegral.lean` this computes the
transform of *every piecewise-linear kernel* in closed form.

Why that matters here rather than being a convenience: the sharp kernel `2 sin(TL)/L` decays only
like `|L|^{-1}`, so its tail over the frequencies `log(n/x)` is not absolutely summable and a
localisation argument cannot simply discard it. The triangular (Fejér) weight `1 − |t|/T` decays like
`|L|^{-2}` and is nonnegative, which is what makes the discard legitimate. Building its transform
needs exactly the linear-times-phase antiderivative proved here.

### Formal layer — the triangular weight on a half interval

`formal/GaloisForLFunctions/RHTower/Sieve/FejerHalf.lean`:

- `integral_fejerHalf_split` — **`∫_0^T (1 − t/T)e^{itL} dt = ∫_0^T e^{itL} dt −
  T^{-1} ∫_0^T t e^{itL} dt`**.

Unconditional. Both pieces on the right have closed forms already in the corpus
(`PhaseIntegral.integral_exp_phase` and `LinearPhaseIntegral.integral_linPhase`), so the triangular
weight's transform is now explicit.

Reflecting and adding gives the symmetric Fejér transform `2(1 − cos TL)/(TL²)`, which is
nonnegative — because `cos ≤ 1` — and decays like `|L|^{-2}`. Those are precisely the two properties
the sharp kernel lacks and that a localisation argument needs: nonnegativity to discard tails
without sign cancellation, and square-summable decay so the discard is quantitatively small.

### Formal layer — the half-interval Fejér transform in closed form

`formal/GaloisForLFunctions/RHTower/Sieve/FejerHalf.lean`, second theorem:

- `integral_fejerHalf` — **`∫_0^T (1 − t/T)e^{itL} dt = i/L − (e^{iTL} − 1)/(TL²)`** for `L ≠ 0`,
  `T > 0`.

Unconditional. Obtained by substituting the two closed forms into `integral_fejerHalf_split`; the
whole content is complex algebra with `i² = −1`.

Adding this to its reflection gives the symmetric Fejér transform: the `i/L` terms cancel (they are
purely imaginary and odd), leaving `2(1 − cos TL)/(TL²)` — real, nonnegative, and `O(|L|^{-2})`. The
cancellation of the `i/L` term is the point: it is the part that decays only like `|L|^{-1}`, and it
is exactly what symmetrising removes.

### Formal layer — the symmetric Fejér transform

`formal/GaloisForLFunctions/RHTower/Sieve/FejerSymmetric.lean`:

- `exp_phase_add_neg` — `e^{iθ} + e^{−iθ} = 2 cos θ`.
- `integral_fejer_symm` — **the half-interval transform at `L` plus its value at `−L` equals
  `(2 − 2 cos TL)/(TL²)`**.

Unconditional. The `i/L` terms cancel — purely imaginary and odd — and they are exactly the part
decaying only like `|L|^{-1}`. What survives is real, nonnegative (`cos ≤ 1`) and `O(|L|^{-2})`.

The transform at `−L` is what the reflection `t ↦ −t` turns the left half of a symmetric triangular
weight into, so this is the Fejér transform; stating it as a sum over the two signs avoids carrying
`|t|` through the computation and needs no change-of-variables lemma.

The smoothed kernel with the properties a localisation argument requires is therefore now explicit
and proved in the corpus.

### Formal layer — the Fejér transform's two properties

`formal/GaloisForLFunctions/RHTower/Sieve/FejerBounds.lean`:

- `fejer_transform_nonneg` — **`0 ≤ (2 − 2cos TL)/(TL²)`**.
- `fejer_transform_le_inv` — **`≤ 4/(TL²)`**, the decay.
- `fejer_transform_le_len` — **`≤ T`**, the cap near the trivial frequency.

All unconditional. The first two follow from `−1 ≤ cos ≤ 1`; the third is the quadratic bound
`1 − θ²/2 ≤ cos θ` (mathlib's `Real.one_sub_sq_div_two_le_cos`) at `θ = TL`.

Together these say the transform is a *nonnegative weight of total size `T` concentrated on
`|L| ≲ T^{-1}`, with a square-summable tail* — the three facts a localisation argument cites, now
proved rather than assumed. The sharp Dirichlet kernel satisfies the analogue of the cap but neither
of the other two.

### Formal layer — pairing a Dirichlet polynomial with the Fejér weight

`formal/GaloisForLFunctions/RHTower/Sieve/FejerPairing.lean`:

- `integral_fejerHalf_dirPoly` — **`∫_0^T F(t)(1 − t/T) dt = ∑_{n<N} a_n ∫_0^T n^{it}(1 − t/T) dt`**.
- `integral_fejer_comm` — the inner integrals in the order the closed form uses.
- `integral_fejer_zero` — **the term whose frequency vanishes contributes `T/2`**.

All unconditional. The Fejér-weighted average of a Dirichlet polynomial is therefore the coefficient
sum weighted by an explicit, nonnegative, rapidly decaying kernel, with the `n = 1` term (frequency
`log 1 = 0`) contributing the main term `a_1 · T/2` and every other term controlled by
`FejerBounds.lean`.

That separation — main term from the vanishing frequency, error from the rest — is the structure a
short-interval argument needs, and it is now proved rather than asserted.

### Formal layer — bounding the half-interval Fejér transform

`formal/GaloisForLFunctions/RHTower/Sieve/FejerHalfBound.lean`:

- `norm_integral_fejerHalf_le` — **`‖∫_0^T (1 − t/T)e^{itL} dt‖ ≤ |L|^{-1} + 2/(TL²)`**.

Unconditional. Both terms of the closed form are bounded separately: `i/L` has modulus exactly
`|L|^{-1}`, and the second term at most `2/(TL²)`.

Recorded precisely because the half-interval bound is *weaker* than the symmetric one: the
`|L|^{-1}` term is odd and cancels on symmetrising, which is what leaves the pure `|L|^{-2}` decay of
`FejerBounds.lean`. On a half interval it survives, and this is the honest bound there. A localisation
argument that works on `[0,T]` rather than `[−T,T]` therefore carries the weaker tail, and the
difference is not cosmetic — `|L|^{-1}` is not summable over the frequencies `log n` while `|L|^{-2}`
is.

### Formal layer — the symmetric Fejér pairing is real and small

`formal/GaloisForLFunctions/RHTower/Sieve/FejerSymmBound.lean`:

- `integral_fejer_symm_real` — the symmetric pairing is the cast of the real number
  `(2 − 2cos TL)/(TL²)`.
- `norm_integral_fejer_symm_le_inv` — **its modulus is at most `4/(TL²)`**.
- `norm_integral_fejer_symm_le_len` — **and at most `T`**.

All unconditional. This is the pairing a localisation argument must use, for the reason recorded on
the previous entry: the half-interval bound carries a `|L|^{-1}` term that is not summable over the
frequencies `log n`, and symmetrising cancels it exactly.

With these the short-interval side of the route is complete as a *toolkit*: pairing identity
(`integral_dirPoly_mul`), explicit kernel with closed form (`FejerHalf`, `FejerSymmetric`), the two
kernel properties (`FejerBounds`), the main-term separation (`FejerPairing`), and now the bounds in
the form a sum over `n` consumes.

### Formal layer — LOCALISATION OF A DIRICHLET POLYNOMIAL

`formal/GaloisForLFunctions/RHTower/Sieve/FejerLocalisation.lean`:

- `fejerWeightAt`, `fejerWeightAt_zero`, `norm_fejerWeightAt_le` — the symmetric Fejér weight at a
  frequency: exactly `T` at the trivial frequency, at most `4/(TL²)` elsewhere.
- `log_succ_zero`, `log_succ_ne_zero` — the frequency `log n` vanishes only at `n = 1`.
- `norm_fejer_dirPoly_sub_main_le` —

  **`‖∑_{n<N} a_n W(T, log n) − a_1 T‖ ≤ ∑_{n ≥ 2} |a_n| · 4/(T (log n)²)`**.

All unconditional. The Fejér average of a Dirichlet polynomial equals its first coefficient times
`T`, with an error governed entirely by the remaining coefficients against a square-summable kernel
tail. That is the localisation a short-interval argument performs, and it is now a theorem.

The structural point: the frequency `log n` vanishes at exactly one index, so the main term is
isolated by an algebraic fact rather than an estimate, and everything else is uniformly small. This
is what the earlier kernel work was for.

### Formal layer — the Fejér pairing as an integral

`formal/GaloisForLFunctions/RHTower/Sieve/FejerIntegralPair.lean`:

- `integral_dirPoly_neg_mul` — pairing the *reflected* polynomial `F(−t)` against a kernel negates
  the frequencies.
- `integral_fejer_pair_eq` — **`∫_0^T F(t)(1 − t/T) dt + ∫_0^T F(−t)(1 − t/T) dt =
  ∑_{n<N} a_n W(T, log n)`**.

Both unconditional. Reflecting the argument is exactly the second half of the symmetric weight, so
this needs no change of variables and no absolute value — the `|t|` that a literal symmetric
triangular weight would introduce never appears.

Composed with `norm_fejer_dirPoly_sub_main_le`, the statement is now about integrals of the
polynomial itself: **the symmetrised Fejér average of a Dirichlet polynomial over `[0,T]` is `a_1 T`
up to `∑_{n ≥ 2} |a_n| · 4/(T(log n)²)`.** That is the short-interval localisation in the form an
argument uses, with both sides expressed in the original objects rather than in kernel weights.

### Formal layer — THE SHORT-INTERVAL LOCALISATION

`formal/GaloisForLFunctions/RHTower/Sieve/FejerShortInterval.lean`:

- `norm_fejer_integral_sub_main_le` —

  **`‖∫_0^T F(t)(1−t/T) dt + ∫_0^T F(−t)(1−t/T) dt − a_1 T‖ ≤ ∑_{n ≥ 2} |a_n| · 4/(T (log n)²)`**

  for `F(t) = ∑_{n<N} a_n n^{it}`.

Unconditional, and not asymptotic: an inequality valid for every `N`, every coefficient vector and
every `T > 0`. The symmetrised Fejér average of a Dirichlet polynomial over `[0,T]` is its first
coefficient times `T`, with an error that is `O(T^{-1})` for fixed coefficients.

This completes the short-interval side of the corpus's Matomäki–Radziwiłł programme as a proved
statement rather than a toolkit. Together with the sharp large sieve, Montgomery's sieve, the
Dirichlet mean value theorem and the large-values estimate — all built in this corpus — the analytic
prerequisites of that route are in place. What remains is the multiplicative structure: the
decomposition by prime factors (for which `RamareWeight.lean` supplies the exact identity) and the
Halász-type input, neither of which is a consequence of the analytic layer alone.

### Formal layer — Ramaré's weight on a coprime factorisation

`formal/GaloisForLFunctions/RHTower/Sieve/RamarePrimeFactor.lean` opens the multiplicative side.

- `primeFactorsIn_mul_prime` — **`primeFactorsIn P (pm) = insert p (primeFactorsIn P m)`** for a
  designated prime `p ∤ m`.
- `card_primeFactorsIn_mul_prime` — hence **`ω_P(pm) = ω_P(m) + 1`**.
- `map_mul_prime_of_not_dvd` — a multiplicative `f` satisfies `f(pm) = f(p)f(m)` there.

All unconditional. These are what make Ramaré's bilinear decomposition genuinely bilinear on the
coprime part: the weight `1/ω_P(pm)` becomes `1/(ω_P(m)+1)`, a function of the cofactor alone, and
the multiplicative function factors.

Stated precisely so the limit is visible: the identities hold only where `p ∤ m`. The part with
`p ∣ m` is a remainder that a sieve must bound separately — it is not governed by these identities,
and treating the decomposition as bilinear everywhere would be wrong.

The primality hypothesis on the designated set is necessary, not decorative: `primeFactorsIn` is
defined for an arbitrary `P`, and `q ∣ pm ↔ q = p ∨ q ∣ m` requires `q` prime.

### Formal layer — the bilinear Ramaré sum for a multiplicative function

`formal/GaloisForLFunctions/RHTower/Sieve/RamareBilinearSplit.lean`:

- `sum_ramare_bilinear_split` —

  **`∑_{m ∈ T} f(pm)/ω_P(pm) = f(p) ∑_{p ∤ m} f(m)/(ω_P(m)+1) + ∑_{p ∣ m} f(pm)/ω_P(pm)`**

  for a multiplicative `f` and a designated prime `p`.

Unconditional. On the first part the function factors and the weight depends on the cofactor alone,
so the sum is genuinely bilinear in `p` and `m` — which is the structure Matomäki–Radziwiłł's
argument exploits.

The second part is isolated deliberately rather than absorbed. There `p` occurs to a higher power,
`f` does **not** factor, and a sieve must bound it separately. Quoting the Ramaré decomposition as
bilinear throughout would hide exactly the term an argument has to control, so the split is stated
with the remainder explicit.

### Formal layer — bounding the Ramaré remainder

`formal/GaloisForLFunctions/RHTower/Sieve/RamareRemainder.lean`:

- `one_le_card_primeFactorsIn_mul` — the designated prime always divides its own multiple, so
  `ω_P(pm) ≥ 1`.
- `abs_ramare_remainder_le` — **`|∑_{p ∣ m} f(pm)/ω_P(pm)| ≤ #{m ∈ T : p ∣ m}`** for `|f| ≤ 1`.

Both unconditional. This bounds the term that `RamareBilinearSplit.lean` isolates, so the
decomposition is now complete: bilinear main part plus a controlled remainder.

The bound is deliberately crude — no cancellation is used, each term simply has modulus at most one.
It suffices because the count on the right is the number of multiples of `p` in the cofactor range,
which is itself small; the corpus's `Sieve/IntervalMultiples` supplies that count. Claiming anything
sharper here would require cancellation in a sum where `f` does not factor, which is precisely what
is unavailable.

### Formal layer — THE COMPLETE MULTIPLICATIVE RAMARÉ DECOMPOSITION

`formal/GaloisForLFunctions/RHTower/Sieve/RamareDecomposition.lean`:

- `abs_ramare_inner_sub_bilinear_le` —
  **`|∑_{m∈T} f(pm)/ω_P(pm) − f(p)·B_p| ≤ #{m ∈ T : p ∣ m}`**.
- `abs_sum_ramare_sub_bilinear_le` — the same summed over the designated primes, with total error
  `∑_{p∈P} #{m ∈ T_p : p ∣ m}`.

Both unconditional, for any bounded multiplicative `f`.

Ramaré's weighted factorisation of such an `f` is therefore **bilinear up to a term counted by
multiples** — the structure Matomäki–Radziwiłł's argument requires, with its error explicit rather
than absorbed.

Route status. The corpus now owns, all unconditionally: the sharp large sieve, Montgomery's sieve,
the Dirichlet mean value theorem, the large-values estimate, the short-interval localisation, and
this multiplicative decomposition. The remaining input is the Halász-type bound — a mean-value
theorem for multiplicative functions in terms of their distance from `n^{it}` — which is a separate
theorem and not a consequence of the layers above.

### Formal layer — the distance from a character

`formal/GaloisForLFunctions/RHTower/Sieve/MultiplicativeDistance.lean` opens the Halász layer.

- `mulDistSq` — **`D(f,t;P)² = ∑_{p ∈ P} (1 − Re(f(p)p^{-it}))/p`**, the quantity Halász's theorem
  is stated in.
- `one_sub_re_nonneg`, `mulDist_term_nonneg` — each summand is nonnegative when `|f(p)| ≤ 1`.
- `mulDistSq_nonneg`, `mulDistSq_mono` — the distance is a genuine nonnegative quantity, monotone in
  the set of primes.

All unconditional.

This is the *object*, not the theorem. Halász's bound — that a multiplicative function has small mean
value unless it is close to some `n^{it}` in this distance — is a separate result and is not proved
here. Defining the distance and establishing that it is well-behaved is the prerequisite; the
inequality itself remains the route's open input, alongside nothing else.

### Formal layer — the distance is a genuine distance

`formal/GaloisForLFunctions/RHTower/Sieve/DistancePointwise.lean` and `.../DistanceTriangle.lean`.

Pointwise (`DistancePointwise`):

- `normSq_sub_eq` — the polarisation identity `‖u−v‖² = ‖u‖² + ‖v‖² − 2 Re(u conj v)`.
- `half_normSq_sub_le` — on the closed unit disc, `‖u−v‖²/2 ≤ 1 − Re(u conj v)`.
- `one_sub_re_eq_half_normSq` — on the unit circle the two are **equal**.

Global (`DistanceTriangle`):

- `mulDistSqPair` — `D(f,g;P)² = ∑_{p∈P}(1 − Re(f(p) conj g(p)))/p`.
- `distVec`, `distVec_add`, `norm_distVec` — the distance is exactly the Euclidean norm of the vector
  `p ↦ (f(p) − g(p))/√(2p)` in `EuclideanSpace ℂ P`, and that vector is additive in the middle
  argument.
- `sqrt_mulDistSqPair_triangle` — **the Granville–Soundararajan triangle inequality**
  `D(f,h;P) ≤ D(f,g;P) + D(g,h;P)` for unimodular `f, g, h`.
- `charFn`, `norm_charFn`, `conj_charFn`, `mulDistSq_eq_pair` — the character `n ↦ n^{it}` is
  unimodular and `mulDistSq f t P` is the pairwise distance to it.
- `sqrt_mulDistSq_triangle_char` — distance to a character is transitive through any unimodular
  function.

All unconditional.

The equality on the unit circle is what makes this work: it turns the distance into a norm, so the
triangle inequality is `norm_add_le` rather than an inequality needing proof. On the open disc only
the inequality `half_normSq_sub_le` survives, in the direction that does *not* give the triangle
inequality — so the unimodular hypothesis in the triangle theorem is doing real work, not tidiness.
The disc case is the Granville–Soundararajan lemma proper and is not proved here.

### Formal layer — the triangle inequality on the closed unit disc

`formal/GaloisForLFunctions/RHTower/Sieve/DistanceDiscTriangle.lean` removes the unimodularity
hypothesis, giving the Granville–Soundararajan triangle inequality in the form it is actually used.

- `sqrt_one_sub_re_triangle` — **pointwise on the closed unit disc**:
  `√(1−Re(u w̄)) ≤ √(1−Re(u v̄)) + √(1−Re(v w̄))` for `‖u‖,‖v‖,‖w‖ ≤ 1`.
- `sqrt_sum_sq_add_le` — Minkowski for a finite sum of squares, via `EuclideanSpace ℝ P`.
- `one_sub_re_mul_conj_nonneg` — the summands are nonnegative on the disc.
- `sqrt_mulDistSqPair_triangle_disc` — **the full theorem**: `D(f,h;P) ≤ D(f,g;P) + D(g,h;P)`
  for `‖f(p)‖, ‖g(p)‖, ‖h(p)‖ ≤ 1`.
- `mulDistSqPair_nonneg_disc`, `sqrt_mulDistSq_triangle_char_disc` — nonnegativity and transitivity
  of closeness to a character, on the disc.

All unconditional.

The naive comparison `C ≤ A + B` is **false** on the disc: at `u = e^{iπ/3}`, `v = 1`,
`w = e^{-iπ/3}` it reads `3/2 ≤ 1/2 + 1/2`. The cross term is not slack, it is the content. What
carries the proof is the identity `2(1−Re(u v̄)) = ‖u−v‖² + (1−‖u‖²) + (1−‖v‖²)`; writing
`2A = X²+a+b`, `2B = Y²+b+c`, `2C = Z²+a+c` gives
`4AB ≥ (X²+b)(Y²+b) = (XY+b)² + b(X−Y)²`, so `2√(AB) ≥ XY+b`, and `Z ≤ X+Y` finishes.
The slack `b(X−Y)²` — the *defect* of the middle value — is exactly what pays for the cross term,
which is why the unimodular case (`b = 0`) is the tight one.

This closes the metric geometry of the Halász distance. The mean-value bound itself remains the
route's open input.

### Formal layer — the divisor swap and Halász's recursion

`formal/GaloisForLFunctions/RHTower/Sieve/DivisorSwap.lean`.

- `sum_divisors_swap` — **the general divisor swap**
  `∑_{m ≤ N} ∑_{d ∣ m} G(d, m/d) = ∑_{d ≤ N} ∑_{k ≤ N/d} G(d,k)`, by the explicit bijection
  `(m,d) ↦ (d, m/d)` with inverse `(d,k) ↦ (dk, d)`.
- `sum_mul_log_eq_vonMangoldt` — **Halász's recursion** for completely multiplicative `f`:
  `∑_{m ≤ N} f(m) log m = ∑_{d ≤ N} Λ(d) f(d) ∑_{k ≤ N/d} f(k)`.

Both unconditional.

`RHTower.Mertens.log_summatory_eq` already had the constant-summand case (`∑_{m≤n} log m =
∑_{d≤n} Λ(d)⌊n/d⌋`), proved by counting multiples; `sum_divisors_swap` is the general form that
carries an arbitrary summand through the same reindexing, which is what a weighted sum needs.

The recursion is the identity the mean-value theory turns on: it expresses the log-weighted sum of
`f` through the *unweighted* sums of `f` over the shorter ranges `N/d`, and so converts information
about `f` at primes into information about its partial sums. Complete multiplicativity is used
exactly once, to split `f(m) = f(d) f(m/d)` — for merely multiplicative `f` the same shape holds
with `Λ` replaced by the Dirichlet inverse `f^{-1} * (f·log)`, which is not built here.

### Formal layer — the Möbius log recursion

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusLogRecursion.lean`.

- `one_pmul_log` — the logarithmic derivation kills the convolution identity.
- `moebius_pmul_log` — **`μ·log = −(Λ * μ)`**.
- `moebius_mul_log_apply` — pointwise: `μ(n) log n = −∑_{d ∣ n} Λ(d) μ(n/d)`.
- `sum_moebius_mul_log_eq` — **the recursion**:
  `∑_{m ≤ N} μ(m) log m = −∑_{d ≤ N} Λ(d) ∑_{k ≤ N/d} μ(k)`,
  the log-weighted Möbius sum expressed through the Mertens function on the ranges `N/d`.

All unconditional.

This is the identity these cards actually need. `sum_mul_log_eq_vonMangoldt` (previous section)
assumes complete multiplicativity, which **μ does not have** — `μ(4) = 0` while `μ(2)² = 1` — so it
does not apply to μ at all. The replacement is obtained by applying the logarithmic derivation to
`μ * ζ = 1`: the derivation kills the identity element, `ζ·log = log` and `μ * log = Λ`, giving
`(μ·log) * ζ = −Λ`, and multiplying by μ finishes.

`RHTower.pmul_log_mul` and `RHTower.zeta_pmul_log` (`DirichletLogDerivation.lean`, built for
Selberg's identity) supplied the derivation; only the Möbius specialisation was missing.

### Formal layer — Chebyshev's ψ through the Möbius function

`formal/GaloisForLFunctions/RHTower/Sieve/ChebyshevMoebius.lean`.

- `vonMangoldt_eq_sum_moebius_mul_log` — `Λ(n) = ∑_{d ∣ n} μ(d) log(n/d)`.
- `vonMangoldt_eq_sum_log_mul_moebius` — `Λ(n) = ∑_{d ∣ n} log d · μ(n/d)`.
- `sum_vonMangoldt_eq_moebius_logSummatory` — **`ψ(N) = ∑_{d ≤ N} μ(d) ∑_{k ≤ N/d} log k`**.
- `sum_vonMangoldt_eq_log_mertens` — **`ψ(N) = ∑_{d ≤ N} log d ∑_{k ≤ N/d} μ(k)`**.

All unconditional.

These are the two elementary bridges between the prime count and the Möbius function. The first
carries a cancellation hypothesis on μ into ψ (with Stirling controlling the inner log summatory);
the second carries prime information back to the Mertens function. Both are exact finite identities;
no estimate is made.

Corpus check: `RHTower.MobiusLogDivisorParaproduct` already applies `μ * log = Λ` but deliberately
keeps the result in *pair-labelled* antidiagonal form and never performs the reindexing, so the
summed identities above were absent. `RHTower.MoebiusFloorSummatory` already owns
`moebius_floor_summatory` (`∑_{d≤N} μ(d)⌊N/d⌋ = 1`) and `abs_sum_moebius_div_le_one`
(`|∑_{d≤N} μ(d)/d| ≤ 1`) — those were not rebuilt.

### Formal layer — the Euler product is damped by the distance

`formal/GaloisForLFunctions/RHTower/Sieve/EulerDamping.lean`.

- `norm_one_add_le_exp` — **`‖1 + z‖ ≤ exp(Re z + ‖z‖²)` for every complex `z`**, with no smallness
  hypothesis.
- `prod_norm_one_add_le_exp` — the product form over any finite index set.
- `sum_re_eq_sub_mulDistSq` — `∑_p Re(f(p)p^{−it}/p) = ∑_p 1/p − D(f,t;P)²`.
- `prod_euler_factor_le` — **`∏_{p∈P} ‖1 + f(p)p^{−it}/p‖ ≤ exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − D(f,t;P)²)`**.

All unconditional.

This is the structural reason Halász's theorem is stated in terms of `D`: the Euler product is below
its trivial size by exactly `exp(−D²)`, so a multiplicative function far from every character has a
small product, and the squared distance is the exponential rate.

The pointwise bound needs no hypothesis at all, which is worth recording since the textbook version
carries one. Squaring gives `‖1+z‖² = 1 + 2Re z + ‖z‖² ≤ 1 + 2Re z + 2‖z‖²`, and `1 + u ≤ exp u`
finishes — the discarded `‖z‖²` is precisely the slack that removes the usual `|z| ≤ 1/2`
restriction, so no series expansion of `log(1+z)` is required.

### Formal layer — the damped product as a Dirichlet sum

`formal/GaloisForLFunctions/RHTower/Sieve/EulerExpansion.lean`.

- `prod_one_add_eq_sum_powerset` — `∏_{p∈P}(1+z_p) = ∑_{T ⊆ P} ∏_{p∈T} z_p`.
- `primeFactors_prod_of_subset`, `prod_injOn_powerset` — on a set of primes, `T ↦ ∏_{p∈T} p` is
  injective (a subset is recovered as the prime factors of its product), so the subset sum is
  literally a sum over distinct squarefree `P`-smooth integers.
- `norm_sum_powerset_le_exp` — **`‖∑_{T⊆P} ∏_{p∈T} f(p)p^{−it}/p‖ ≤
  exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − D(f,t;P)²)`**.

All unconditional.

This converts the damping bound into a statement about a Dirichlet-type sum: a multiplicative
function far from every character has small partial sums over squarefree smooth numbers, at the
exponential rate `exp(−D²)`.

The estimate is not a triangle inequality. The sum is first rewritten *as* the product and only then
bounded, so no cancellation is discarded in the passage — a term-by-term bound on the same sum would
give `∏(1+1/p)`, with no dependence on the distance at all and hence no damping.

### Formal layer — the damped sum indexed by integers

`formal/GaloisForLFunctions/RHTower/Sieve/EulerIntegerIndex.lean`.

- `prod_eq_of_multiplicative` — `∏_{p∈T} f(p) = f(∏_{p∈T} p)` for multiplicative `f` on a finite set
  of distinct primes (induction, with pairwise coprimality from `Nat.coprime_primes`).
- `prod_term_eq` — the subset factor collapses to the integer term:
  `∏_{p∈T} f(p)p^{−it}/p = f(n) n^{−it}/n` with `n = ∏_{p∈T} p`.
- `norm_sum_smooth_le_exp` — **`‖∑_{n squarefree, P-smooth} f(n) n^{−it}/n‖ ≤
  exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − D(f,t;P)²)`**, the sum running over genuine distinct integers.

All unconditional.

The hypotheses are exactly multiplicativity (`f(ab) = f(a)f(b)` for coprime `a,b`), `f(1) = 1` and
`‖f‖ ≤ 1` — satisfied by μ, unlike the complete multiplicativity that the general Halász recursion
needs. Three separate facts are required to collapse a subset factor to an integer term:
multiplicativity across distinct primes, `log` additivity on the product, and `∏ 1/p = 1/n`; the
first is the only one that uses primality, via coprimality of distinct primes.

### Formal layer — the damping bound for μ itself

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusEulerDamping.lean`.

- `moebiusC`, `norm_moebiusC_le_one`, `moebiusC_one`, `moebiusC_mul_of_coprime`, `moebiusC_prime` —
  μ as a complex-valued function meets every hypothesis of the damped bound.
- `mulDistSq_moebiusC` — **`D(μ,t;P)² = ∑_{p∈P}(1 + cos(t log p))/p`**.
- `norm_sum_moebius_smooth_le_exp` — **`‖∑_{n squarefree, P-smooth} μ(n) n^{−it}/n‖ ≤
  exp(∑_{p∈P} 1/p² − ∑_{p∈P} cos(t log p)/p)`**.

All unconditional.

Because `μ(p) = −1` at every prime, the `∑_p 1/p` in the damping exponent cancels *exactly* against
the same term inside `D(μ,t;P)²`. What survives is the convergent `∑ 1/p²` against
`∑_p cos(t log p)/p`.

At `t = 0` this reads `exp(∑ 1/p² − ∑ 1/p)`, which tends to 0 as `P` exhausts the primes — the
elementary cancellation of μ over squarefree smooth numbers, with an explicit rate. This also marks
the boundary precisely: for `t ≠ 0` the bound is only as strong as a lower bound for
`∑_p cos(t log p)/p`, and supplying one uniformly in `t` is exactly the non-elementary input. The
formal layer now states the cards' obstruction as a single scalar quantity rather than as a citation.

### Formal layer — unconditional cancellation with an explicit rate

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSmoothCancellation.lean`.

- `sum_inv_sq_le_two_of_pos` — `∑_{p∈P} 1/p² ≤ 2` for any finite set of positive integers.
- `norm_sum_moebius_smooth_le_exp_two` — **`‖∑_{n sf, P-smooth} μ(n)n^{−it}/n‖ ≤
  exp(2 − ∑_{p∈P} cos(t log p)/p)`**, with the `∑1/p²` clutter replaced by an absolute constant.
- `norm_sum_moebius_smooth_zero_le` — **`‖∑_{n sf, P-smooth} μ(n)/n‖ ≤ exp(2 − ∑_{p∈P} 1/p)`**.

All unconditional.

The `t = 0` statement is genuine unconditional cancellation with an explicit rate: since `∑_p 1/p`
diverges, the left side tends to zero as `P` exhausts the primes, and the rate is the prime harmonic
sum itself.

It also isolates what is *not* available. Nothing analogous follows here for `t ≠ 0`: the exponent is
governed by `∑_p cos(t log p)/p`, and a lower bound for that uniform in `t` is precisely the
non-elementary input these cards name as Menon 2026 / Matomäki–Radziwiłł. The gap is now a single
explicit scalar inequality rather than a literature citation.

`RHTower.Sieve.SquarefreeHarmonic.sum_inv_sq_le_two` supplied the telescoping bound; only the
restriction from `Icc 1 Y` to an arbitrary finite prime set was added.

### Formal layer — the cancellation in the limit

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSmoothLimit.lean`.

- `tendsto_sum_primesBelow_inv_atTop` — the prime harmonic sum diverges, in `Finset` form
  (`∑_{p ∈ primesBelow N} 1/p → ∞`), obtained from mathlib's `not_summable_one_div_on_primes`.
- `tendsto_exp_two_sub` — `exp(2 − u) → 0` along any divergent `u`.
- `tendsto_norm_sum_moebius_smooth_zero` — **`‖∑_{n squarefree, p∣n ⇒ p<N} μ(n)/n‖ → 0`**.

All unconditional.

This is the limit form of the cancellation bound. The entire decay comes from the divergence of
`∑ 1/p` — no prime number theorem, no zero-free region.

Note what this does and does not give. The smooth-number restriction is essential: the statement is
about squarefree integers all of whose prime factors lie below `N`, not about `∑_{n ≤ N} μ(n)/n`,
which is a different (and already corpus-owned, `abs_sum_moebius_div_le_one`) quantity. The
corresponding limit at `t ≠ 0` remains out of reach from this chain, for the reason recorded above.

### Formal layer — at most one character can be close

`formal/GaloisForLFunctions/RHTower/Sieve/CharacterSeparation.lean`.

- `mulDistSqPair_comm` — the pairwise distance is symmetric.
- `mulDistSqPair_charFn` — **`D(n^{it}, n^{iu}; P)² = ∑_{p∈P}(1 − cos((t−u) log p))/p`**.
- `char_separation_of_close` — if `D(f, n^{it};P) ≤ δ` and `D(f, n^{iu};P) ≤ δ` then
  `D(n^{it}, n^{iu};P) ≤ 2δ`.
- `sum_one_sub_cos_le_of_close` — explicitly, **`∑_{p∈P}(1 − cos((t−u) log p))/p ≤ 4δ²`**.

All unconditional.

This is why a Halász-type argument only ever needs one distinguished frequency: the set of characters
within `δ` of a given `f` has diameter `2δ`, and `mulDistSqPair_charFn` converts that diameter bound
into a genuine constraint on `t − u`.

The hypothesis is only `‖f(p)‖ ≤ 1` — no multiplicativity — because the disc triangle inequality was
proved without it. This is where that earlier work pays: with only the unimodular version, the result
would not apply to μ.

### Formal layer — quantitative frequency separation

`formal/GaloisForLFunctions/RHTower/Sieve/FrequencySeparation.lean`.

- `two_div_pi_sq_mul_sq_le_one_sub_cos` — Jordan's inequality as `1 − cos x ≥ (2/π²)x²` on `|x| ≤ π`.
- `sq_mul_sum_sq_log_le_of_close` — **if `D(f, n^{it};P) ≤ δ` and `D(f, n^{iu};P) ≤ δ` and
  `|(t−u) log p| ≤ π` on `P`, then `(t−u)² ∑_{p∈P}(log p)²/p ≤ 2π²δ²`.**

Both unconditional.

This converts the qualitative uniqueness statement into a bound on the frequency itself: since the
weight `∑_p (log p)²/p` grows with `P`, the window of admissible `t − u` shrinks. A multiplicative
function cannot be close to two genuinely distinct characters, with an explicit rate.

The `|x| ≤ π` restriction is intrinsic, not an artefact — `1 − cos x` is periodic while `x²` is not,
so no inequality of this shape can hold globally. It is carried as a hypothesis on `P` rather than
silently assumed.

mathlib's `Real.cos_le_one_sub_mul_cos_sq` supplied the inequality; `Real.mul_le_sin` (Jordan) is
also present. Neither needed rebuilding.

### Formal layer — the Halász dichotomy

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszDichotomy.lean`.

- `eq_of_both_close` — **uniqueness**: under the separation hypothesis, two frequencies both within
  `δ` of `f` are equal.
- `norm_sum_smooth_le_exp_of_far` — **damping**: a frequency at distance at least `δ` gives
  `‖∑_{n sf, P-smooth} f(n)n^{−it}/n‖ ≤ exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − δ²)`.

Both unconditional.

Together these are the dichotomy Halász's theorem rests on: for every frequency except at most one,
the Dirichlet sum is damped, and the bound away from the exceptional frequency is uniform in `t`.

What this does **not** do, stated plainly: it neither identifies the exceptional frequency nor gives
any lower bound on `δ`. Those are the analytic content, and no part of the elementary chain built
here supplies them. The formal layer now separates the two cleanly — the combinatorial/metric half is
complete and unconditional, and the remaining gap is exactly the analytic half named on these cards
as Menon 2026 / Matomäki–Radziwiłł.

### Formal layer — prime-power tail weights

`formal/GaloisForLFunctions/RHTower/Sieve/PowerWeightBound.lean`. First half of the explicit lower
bound for `∑_{p ≤ N}(log p)²/p`, which is what turns the frequency separation into a bound of the
shape `|t − u| ≲ δ/log N`.

- `sum_range_add_two_mul_half_pow` — the exact identity
  `∑_{j<M}(j+2)(1/2)^j = 6 − 2(M+3)/2^M`.
- `sum_range_add_two_mul_pow_le`, `sum_range_shift_pow_le` — **`∑_{k≥2} k x^k ≤ 6x²` for
  `0 ≤ x ≤ 1/2`**, so the proper prime powers of `p` contribute at most `6(log p)²/p²`.
- `log_sq_le_four_mul` — **`(log x)² ≤ 4x` for `x ≥ 1`**, via `log x ≤ 2√x`.

All unconditional.

The weight `k` (not just `x^k`) is forced by `log(p^k) = k log p`, which is why the ordinary
geometric series does not suffice. Together these give
`∑_{p^k ≤ N, k≥2} k(log p)²/p^k ≤ 24 ∑_{p ≤ √N} 1/p`, and with the corpus's
`HarmonicLogBound.sum_Icc_one_div_le_one_add_log` that is `O(log N)` — small against the main term
`½log²N` of `RHTower.abs_sum_vonMangoldt_log_div_sub_le`. The remaining step is the reindexing of
`∑_{m≤N} Λ(m)log m/m` into primes plus proper prime powers.

### Formal layer — the proper prime powers are a lower-order correction

`formal/GaloisForLFunctions/RHTower/Sieve/PrimePowerWeightTail.lean`.

- `sum_range_primePower_weight_le` — at a single prime,
  `∑_{j<M}(j+2)(log p)²/p^{j+2} ≤ 24/p`.
- `sum_primePower_weight_le` — **`∑_{p ≤ b} ∑_{j<M}(j+2)(log p)²/p^{j+2} ≤ 24(1 + log b)`**,
  uniformly in the number `M` of exponents allowed.

Both unconditional.

Combining last section's `∑_{k≥2} k x^k ≤ 6x²` at `x = 1/p` with `(log p)² ≤ 4p` gives `24/p` per
prime; the corpus's `HarmonicLogBound.sum_Icc_one_div_le_one_add_log` then sums it. Against the
`½log²N` main term of `abs_sum_vonMangoldt_log_div_sub_le` this `O(log N)` correction is lower order,
which is exactly what is needed to pass from `∑_{m≤N} Λ(m)log m/m` to `∑_{p≤N}(log p)²/p`.

The uniformity in `M` matters: no truncation of the exponent range is assumed, so the bound applies
whatever cutoff the reindexing later supplies. The remaining step is the support identification —
that the non-prime part of `Λ`'s support inside `Icc 1 N` embeds in `primesLE N ×ˢ range M` under
`(p,j) ↦ p^{j+2}`; `Sieve/PrimePowerSum.primePow_injOn` is the corresponding injectivity fact.

### Formal layer — separating the primes from their powers

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeLogSqLower.lean`.

- `primePowShift_injOn` — `(p,j) ↦ p^{j+2}` is injective on `primesLE N ×ˢ range M`.
- `mem_image_of_nonprime` — every non-prime `m ≤ N` with `Λ(m) ≠ 0` is such a shifted prime power,
  with `j < Nat.log 2 N`.
- `sum_nonprime_vonMangoldt_log_div_le` — **`∑_{m ≤ N, m not prime} Λ(m)log m/m ≤ 24(1 + log N)`**.

All unconditional.

This is the support identification the previous section needed. `Λ(m) ≠ 0 ↔ IsPrimePow m`, and a
prime power that is not prime has exponent at least 2; the exponent bound `j < log₂N` comes from
`2^k ≤ p^k = m ≤ N`. With the injectivity, `Finset.sum_image` converts the sum over the image into
the double sum already bounded by `sum_primePower_weight_le`.

Combined with `RHTower.abs_sum_vonMangoldt_log_div_sub_le`
(`|∑_{m≤N} Λ(m)log m/m − ½log²N| ≤ 15 log N + 1`), the prime part now satisfies
`∑_{p≤N}(log p)²/p ≥ ½log²N − 39 log N − 25`: the weight in the frequency-separation bound grows like
`½log²N`, so the admissible window for `t − u` is `O(δ/log N)`.

### Formal layer — the explicit weight lower bound

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeLogSqLower.lean` (capstone).

- `filter_prime_Icc_eq_primesLE` — `{m ∈ Icc 1 N | m.Prime} = primesLE N`.
- `sum_prime_log_sq_div_ge` — **`∑_{p ≤ N}(log p)²/p ≥ ½log²N − 39 log N − 25`**.

Unconditional.

This completes the four-part build begun with `PowerWeightBound`: split the `Λ·log/id` summatory at
`N`, identify the prime part as `∑_{p≤N}(log p)²/p`, bound the proper prime powers by `24(1+log N)`,
and read the main term off `RHTower.abs_sum_vonMangoldt_log_div_sub_le`.

Its purpose is to make `sq_mul_sum_sq_log_le_of_close` quantitative. That bound reads
`(t−u)² ∑_{p∈P}(log p)²/p ≤ 2π²δ²`; with the weight now known to grow like `½log²N`, the admissible
window is `|t−u| = O(δ/log N)` — the classical shape. No prime number theorem is used: the input is
Mertens-level, and every constant is explicit.

### Formal layer — the frequency window is O(δ / log N)

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszWindow.lean`.

- `logSqWeight N := ½log²N − 39 log N − 25`.
- `sq_sub_mul_logSqWeight_le` — **`(t−u)² · logSqWeight N ≤ 2π²δ²`**.
- `sq_sub_le_div` — once the weight is positive, **`(t−u)² ≤ 2π²δ² / logSqWeight N`**.

Both unconditional.

This is the assembled quantitative uniqueness statement: two frequencies both within `δ` of the same
`f` in the multiplicative distance over the primes below `N` must satisfy `|t−u| = O(δ/log N)`.
Every constant is explicit, and the only arithmetic input is Mertens-level — no prime number theorem
and no zero-free region enter anywhere.

The elementary Halász layer for these cards is now complete end to end: distance geometry → disc
triangle inequality → Euler damping → integer indexing → μ instantiation → cancellation and its
limit → character separation → quantitative frequency separation → dichotomy → explicit window.

What is untouched, and cannot be reached from this chain, is the analytic half: identifying the
exceptional frequency and bounding `δ` from below. That is exactly the input these cards name as
Menon 2026 / Matomäki–Radziwiłł.

### Formal layer — window multiplicity and the trivial variance bound

`formal/GaloisForLFunctions/RHTower/Sieve/WindowMultiplicity.lean`. First step toward the
mean-square input `(6)`.

- `card_window_starts_le` — **`#{x < X : n ∈ (x, x+L]} ≤ L`**: a point is seen by at most `L` window
  starts, since `n ∈ (x,x+L] ⟺ n−L ≤ x < n`.
- `sum_window_sum_le` — exchanging the order of summation, `∑_x ∑_{n ∈ (x,x+L]} w(n) ≤ L ∑_n w(n)`
  for nonnegative `w`.
- `sum_normSq_window_le` — **`∑_{x<X} ‖∑_{x<n≤x+L} a_n‖² ≤ L² ∑_n ‖a_n‖²`**.

All unconditional.

This is the trivial variance bound that every short-interval argument improves on. Recording it fixes
the shape: the `L²` is `L` from Cauchy–Schwarz inside each window times `L` from the multiplicity of
starts, and it is the *multiplicity* count — not the Cauchy–Schwarz — that any saving must attack.
Menon's bound `(6)` is exactly the statement that for `a = μ` the true size is smaller by
`(log log L / log L)²`.

### Formal layer — the exact short-interval variance kernel

`formal/GaloisForLFunctions/RHTower/Sieve/WindowKernel.lean`.

- `windowOverlap X L n m := #{x < X : n, m ∈ (x, x+L]}`.
- `windowOverlap_eq_zero` — **the kernel vanishes when `|n − m| ≥ L`**.
- `windowOverlap_le` — `K(n,m) ≤ L`.
- `sum_window_pair_swap` — the double window sum equals the pair sum against `K`.
- `sum_normSq_window_eq` — **`∑_{x<X} ‖∑_{x<n≤x+L} a_n‖² = ∑_{n,m} K(n,m)·Re(a_n conj a_m)`**,
  an exact identity.

All unconditional.

Previous section gave the trivial bound; this replaces it by an equality. The substantive fact is the
support: both `n` and `m` lie in `(x,x+L]` only if `|n−m| ≤ L−1`, so short-interval variance is a
*local* problem — only pairs closer than `L` interact. This is the discrete counterpart of the Fejér
kernel's support, and it is what makes a correlation estimate for `μ(n)μ(m)` over near-diagonal pairs
the right target for `(6)`.

### Formal layer — the triangular (Fejér) weight

`formal/GaloisForLFunctions/RHTower/Sieve/WindowTriangularWeight.lean`.

- `windowOverlap_comm` — the kernel is symmetric.
- `windowOverlap_le_sub_dist` — **`K(n,m) ≤ L − |n − m|`**, the discrete triangular weight.
- `sum_normSq_window_le_triangular` — **`∑_{x<X} ‖∑_{x<n≤x+L} a_n‖² ≤
  ∑_{n,m} (L − |n−m|)‖a_n‖‖a_m‖`**.

All unconditional.

The kernel is exactly the discrete Fejér weight: `L` on the diagonal, decaying linearly, zero at
`|n−m| = L`. So the support statement of the previous section is the endpoint of a linear decay
rather than an isolated fact, and the constant-`L` bound is recovered only on the diagonal.

This completes the elementary framing of the mean-square input `(6)`: exact identity, symmetric
kernel, triangular bound, and the trivial `L²` estimate it improves. Any proof of `(6)` must exploit
cancellation in `∑_{n,m} (L−|n−m|) μ(n)μ(m)` over near-diagonal pairs — which is the analytic content
that remains open.

### Formal layer — the kernel bound is attained

`formal/GaloisForLFunctions/RHTower/Sieve/WindowKernelExact.lean`.

- `windowOverlap_eq_sub_dist` — **`K(n,m) = L − |n − m|`** whenever `|n−m| ≤ L` and the pair sits in
  the bulk (`L ≤ n, m ≤ X`), the common starts being exactly `[max(n,m) − L, min(n,m))`.
- `windowOverlap_self` — `K(n,n) = L` on the diagonal.

Both unconditional.

The triangular bound of the previous section is therefore an **equality** in the bulk, not merely a
valid estimate. This settles the accounting: the kernel side of the short-interval variance is exact,
so no sharpening is available there, and the whole of any improvement on the trivial `L²` bound must
come from arithmetic cancellation in the coefficients `μ(n)μ(m)`.

That is a negative result about method, and it is worth having explicitly: it rules out attacking
`(6)` by refining the geometry of the windows.

### Formal layer — reindexing the pair sum by the shift

`formal/GaloisForLFunctions/RHTower/Sieve/ShiftReindex.lean`.

- `sum_upper_triangle_eq_sum_shift` — **`∑_{n<m<R} F(n,m) = ∑_{1≤h<R} ∑_{n<R−h} F(n, n+h)`**, by the
  explicit bijection `(n,m) ↦ (m−n, n)` with inverse `(h,n) ↦ (n, n+h)`.
- `sum_pair_eq_diag_add_two_upper` — for symmetric real `W`,
  **`∑_{n,m<R} W(n,m) = ∑_n W(n,n) + 2∑_{n<m} W(n,m)`**.

Both unconditional.

Together these convert any symmetric pair sum into a diagonal term plus a sum of *shifted
correlations*. Applied to the triangular kernel this puts the short-interval variance in the form

`L ∑_n |a_n|² + 2 ∑_{h=1}^{L−1} (L−h) ∑_n Re(a_n conj a_{n+h})`,

which is the shape in which such a variance is actually estimated. For `a = μ` the diagonal term is
`L` times the squarefree count (density `6/π²`, already formalized in `Sieve/SquarefreeCount.lean`),
and the entire remaining question is cancellation in the shifted correlations `∑_n μ(n)μ(n+h)` — an
Elliott/Chowla-type input. This localises `(6)` precisely.

### Formal layer — the variance in autocorrelation form

`formal/GaloisForLFunctions/RHTower/Sieve/WindowAutocorrelation.lean`.

- `sum_pair_triangular_eq_autocorrelation` — **`∑_{n,m<R}(L−|n−m|)‖a_n‖‖a_m‖ =
  L∑_{n<R}‖a_n‖² + 2∑_{h≥1}(L−h)∑_{n<R−h}‖a_n‖‖a_{n+h}‖`**, an identity.
- `sum_normSq_window_le_autocorrelation` — the short-interval variance bounded in that form.

Both unconditional.

This is the terminus of the elementary reduction of `(6)`. The variance splits into a diagonal term
plus shifted correlations weighted by the same triangular factor `L − h`, hence supported on `h < L`.

The accounting is now complete and every piece is either done or identified:
the diagonal is `L` times the squarefree count (`Sieve/SquarefreeCount.lean`, density `6/π²`);
the kernel is exact (`WindowKernelExact`), so no saving is available from the geometry;
and the whole of the remaining problem is cancellation in `∑_n μ(n)μ(n+h)` for `1 ≤ h < L`.

That last item is an Elliott/Chowla-type correlation input — precisely what Menon 2026 /
Matomäki–Radziwiłł supply, and precisely what no elementary argument in this corpus reaches.

### Formal layer — the variance of μ is carried by the squarefree numbers

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusWindowVariance.lean`.

- `normSq_moebiusC_eq_indicator` — `‖μ(n)‖²` is the squarefree indicator.
- `sum_normSq_moebiusC_eq_card` — `∑_{n<R}‖μ(n)‖² = #{n < R : n squarefree}`.
- `sum_normSq_window_moebius_le` — **`∑_{x<X}‖∑_{x<n≤x+L}μ(n)‖² ≤ L²·#{n < X+L+1 : n squarefree}`**.

All unconditional.

Against the trivial `L²R` this saves the squarefree density `6/π²` (`squarefreeDensity_eq`), because
the support of μ is the squarefree set and nothing else.

Being precise about how small this gain is: it is a constant factor, not a saving in the `L` or `R`
dependence, and it is the *entire* unconditional improvement available from this direction. The
kernel was already shown exact, and the off-diagonal terms here are bounded only by their support.
Any further progress must come from cancellation in `∑_n μ(n)μ(n+h)` — which is the cited input.

### Formal layer — the variance against squarefree pair counts

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusPairVariance.lean`.

- `norm_moebiusC_eq_indicator` — `‖μ(n)‖` is the squarefree indicator.
- `sum_norm_moebiusC_shift_eq_card` — `∑_{n<R}‖μ(n)‖‖μ(n+h)‖ = P_h(R)`, the squarefree pair count.
- `sum_normSq_window_moebius_le_pairs` — **`∑_{x<X}‖∑_{x<n≤x+L}μ(n)‖² ≤ L·Q(R) + 2∑_{h≥1}(L−h)P_h(R)`**
  with `R = X+L+1`, `Q` the squarefree count and `P_h` the squarefree pair count at shift `h`.

All unconditional.

This is the sharpest form the elementary theory reaches, and it is worth stating exactly what it does
not do: **no cancellation between `μ(n)` and `μ(n+h)` is used anywhere.** Each off-diagonal term is
bounded by the size of its support alone. The triangular weight confines the sum to shifts `h < L`
and the diagonal is the squarefree count; everything else is the pair counts `P_h`, which are
*counts*, not cancelling sums.

Supplying that cancellation — a nontrivial bound for `∑_n μ(n)μ(n+h)` — is the single input the whole
reduction waits on, and it is exactly the published theorem these cards cite.

### Formal layer — a real window is an integer window

`formal/GaloisForLFunctions/RHTower/Sieve/RealWindow.lean`.

- `realWindow x L M` — the integers of `(x, x+L]` for a **real** start `x`.
- `realWindow_eq_Ioc` — **`realWindow x L M = Ioc ⌊x⌋ (⌊x⌋+L)`** for `x ≥ 0`.
- `sum_realWindow_eq` — hence the real-start window sum equals the integer-start sum at `⌊x⌋`.

Both unconditional.

This is the bridge between the cited estimates, which average over *real* starts with an integral
(`(1/Y)∫_Y^{2Y}|…|²dx`), and the discrete variance layer built above, which sums over integer starts.
The window sum is constant on each `[k, k+1)`, so the two formulations carry the same content and no
approximation is involved: `n > x ↔ ⌊x⌋ < n` and `n ≤ x+L ↔ n ≤ ⌊x+L⌋ = ⌊x⌋+L`.

Recording it matters because the discrete/continuous mismatch would otherwise be an unstated gap
between the formal layer and the statement of `(6)`/`(15)` on these cards.

### Formal layer — the integral over real starts is the discrete sum

`formal/GaloisForLFunctions/RHTower/Sieve/RealWindowIntegral.lean`.

- `floor_eq_of_mem_Ico`, `realWindow_const` — on `[k, k+1)` the real window *is* `(k, k+L]`.
- `integral_unit_window` — **`∫_k^{k+1} ‖∑_{x<n≤x+L} a_n‖² dx = ‖∑_{k<n≤k+L} a_n‖²`**.

Both unconditional.

This completes the bridge started in `RealWindow.lean`. The integrand is a step function: only the
right endpoint `x = k+1` sees a different window, and a single point is null, so the unit-interval
integral is exactly the value on the interior. Summing over `k` therefore turns the cited integral
mean square `(1/Y)∫_Y^{2Y}|…|²dx` into the discrete variance of the modules above, with **no error
term and no approximation**.

The discrete layer and the cited statement are now formally the same object, so the only remaining
gap on these cards is the arithmetic one — cancellation in `∑_n μ(n)μ(n+h)`.

### Formal layer — the continuous mean square IS the discrete variance

`formal/GaloisForLFunctions/RHTower/Sieve/WindowStepIntegral.lean`.

- `stepWindow c L k := ‖∑_{k<n≤k+L} c_n‖²`, and `stepWindow_floor_const` — the integrand `g ∘ ⌊·⌋`
  is constant on each **open** unit interval.
- `intervalIntegrable_stepWindow`, `integral_unit_stepWindow` — integrable, with
  `∫_k^{k+1} g⌊x⌋ dx = g k`.
- `integral_stepWindow_eq_sum` — **`∫_Y^{Y+K} g⌊x⌋ dx = ∑_{k<K} g(Y+k)`**.

All unconditional.

The bridge from `RealWindow.lean` is now complete in both directions: the mean square taken as an
integral over real starts — the form in which `(6)`/`(15)` are stated — equals the discrete variance
of the modules above **exactly**, with no error term.

The proof turns on using mathlib's *open*-interval congruences (`integral_congr_uIoo`,
`IntervalIntegrable.congr_uIoo`): the step function is constant precisely on `(k, k+1)` and jumps at
the right endpoint, so the open interval is the correct object and no null-set argument is needed.

### Formal layer — the bridge, stated for the real window

`formal/GaloisForLFunctions/RHTower/Sieve/RealWindowVariance.lean`.

- `integral_realWindow_eq_sum` — **`∫_Y^{Y+K} ‖∑_{x<n≤x+L} c_n‖² dx =
  ∑_{k<K} ‖∑_{Y+k<n≤Y+k+L} c_n‖²`**, for any cutoff `M > Y+K+L`.

Unconditional.

This states the bridge directly for the real-start window `(x, x+L]` rather than for the auxiliary
step function, so it is the identity the cited estimates `(6)`/`(15)` are literally about. The
hypothesis on `M` is only that every window met on `[Y, Y+K]` fits below the cutoff.

The short-interval layer is now closed as a chain of exact statements: continuous mean square =
discrete variance = pair sum against the overlap kernel = (kernel exact) triangular weight =
diagonal + shifted correlations, with the diagonal evaluated for μ as the squarefree count. The
single open link is arithmetic cancellation in `∑_n μ(n)μ(n+h)`.

### Formal layer — the trivial variance bound is attained

`formal/GaloisForLFunctions/RHTower/Sieve/WindowVarianceSharp.lean`.

- `sum_window_one` — every window of length `L` carries mass `L` for the constant sequence.
- `sum_normSq_window_one` — **`∑_{x<X} ‖∑_{x<n≤x+L} 1‖² = X·L²`**.

Unconditional.

The general bound gives `L²·(X+L+1)` for this sequence, so the two agree up to the boundary factor
`(X+L+1)/X → 1`. **No coefficient-free improvement of the trivial bound exists.**

This is the second no-go of the layer, and together with the exactness of the overlap kernel
(`WindowKernelExact`) it closes off the non-arithmetic routes completely: neither a sharper treatment
of the windows nor a better general inequality can help. Every remaining saving must come from
arithmetic cancellation in `∑_n μ(n)μ(n+h)`.

That is a useful negative result to have proved rather than assumed — it shows the cited input is
*necessary*, not an artefact of a lossy reduction.

### Formal layer — the variance *equals* the correlations

`formal/GaloisForLFunctions/RHTower/Sieve/WindowExactAutocorrelation.lean`.

- `re_mul_conj_comm`, `re_mul_conj_self` — the Hermitian pair weight is symmetric, and its diagonal
  is `‖a_n‖²`.
- `sum_normSq_window_eq_autocorrelation` — **an equality**:
  `∑_{x<X}‖∑_{x<n≤x+L} a_n‖² = ∑_n K(n,n)‖a_n‖² + 2∑_{h≥1}∑_n K(n,n+h)·Re(a_n conj a_{n+h})`.

Unconditional.

This upgrades the earlier autocorrelation *bound* to an identity. The previous version replaced
`Re(a_n conj a_{n+h})` by `‖a_n‖‖a_{n+h}‖` and so discarded every cancellation; here nothing is
discarded.

The consequence is a two-way statement rather than a one-way estimate: since `K` is `L` on the
diagonal and `L−h` at shift `h` in the bulk (`WindowKernelExact`), the short-interval variance is
**determined** by the shifted correlations — it is small exactly when `∑_n μ(n)μ(n+h)` cancels.
Small variance and correlation cancellation are the same statement, so the cited input is not merely
sufficient for `(6)`/`(15)`, it is equivalent to it.

### Formal layer — only the shifts below L matter

`formal/GaloisForLFunctions/RHTower/Sieve/WindowShiftRange.lean`.

- `windowOverlap_shift_eq_zero` — shifts `h ≥ L` contribute nothing.
- `sum_normSq_window_eq_autocorrelation_lt` — the identity with the correlation sum restricted:
  **`variance = ∑_n K(n,n)‖a_n‖² + 2∑_{h=1}^{L−1}∑_n K(n,n+h)·Re(a_n conj a_{n+h})`**.

Unconditional.

The number of correlations involved is `L − 1`, **independent of the averaging length `X`**. That is
what makes the reduction usable: a bound at the finitely many shifts `h < L` suffices, and no
statement about long-range correlations is needed.

Combined with the previous section, the position on these cards is now completely explicit. `(6)`/`(15)`
is *equivalent* to cancellation in the `L−1` shifted Möbius correlations `∑_n μ(n)μ(n+h)`,
`1 ≤ h < L`; the kernel weights are known exactly; and both non-arithmetic routes to a saving have
been ruled out by proof.

### Formal layer — the reduction as an implication

`formal/GaloisForLFunctions/RHTower/Sieve/CorrelationToVariance.lean`.

- `sum_normSq_window_le_of_correlation` — **if `|∑_n K(n,n+h)·Re(a_n conj a_{n+h})| ≤ δ` for every
  `1 ≤ h < L`, then `∑_{x<X}‖∑_{x<n≤x+L} a_n‖² ≤ L∑_n‖a_n‖² + 2Lδ`.**

Unconditional (as an implication).

This is the reduction in usable form. Everything to the left of the implication is proved: the exact
identity, the diagonal bound `K(n,n) ≤ L`, and the restriction to fewer than `L` shifts. Only the
hypothesis — the correlation estimate — is open, and it is exactly the published input these cards
cite.

Applied to `a = μ` with `Q` the squarefree count, a correlation bound `δ` yields
`variance ≤ L·Q + 2Lδ`, which is `(6)`/`(15)` once `δ` is of the required size. The elementary side of
these cards is therefore complete: no further unconditional work can shorten the gap, and the gap is
a single named hypothesis rather than a body of missing theory.

### Formal layer — the sign-count identity (14)

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSignCount.lean`.

- `moebius_trichotomy` — `μ(n) ∈ {0, 1, −1}`.
- `moebius_eq_sub_indicator`, `moebius_sq_eq_add_indicator` — `μ = [μ=1] − [μ=−1]` and
  `μ² = [μ=1] + [μ=−1]`.
- `two_mul_card_moebius_eq_one`, `two_mul_card_moebius_eq_neg_one` — **equation (14)**:
  `#{n ∈ (t,t+L] : μ(n) = ±1} = (Q(t,L) ± M(t,L))/2`.

All unconditional.

Found by a numbered-statement audit of this card rather than by reading the Lean-status line: `(14)`
was not formalized anywhere in the corpus, although it is the step that converts the two summatory
estimates into the sign counts the theorem is about.

Its role is exactly the conversion the proof needs: a lower bound for `Q` (elementary, `(11)`/`(13)`,
already formalized) together with an upper bound for `|M|` (the cited input, `(6)`) bounds **both**
sign counts from below simultaneously. Without `(14)` the two estimates do not combine.

### Formal layer — both signs occur linearly often

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSignLower.lean`.

- `card_moebius_sign_ge` — **if `Q(t,L) ≥ ½DL` and `|M(t,L)| ≤ ⅛DL` then both sign counts are at
  least `(3/16)DL`** — the conclusion of `(14)`.

Unconditional (as an implication).

This closes the `(14)` step of the proof. Its two hypotheses come from opposite sources: the lower
bound on `Q` is elementary sieve theory (`(11)`/`(13)`, formalized), and the upper bound on `|M|` is
the mean-square input `(6)` via Markov `(10)`. The sign-count identity is exactly what allows them to
be used together, and this lemma performs that combination.

The constant `3/16` is not sharp and the card says so; only its positivity is used downstream.

### Formal layer — counting a shifted congruence

`formal/GaloisForLFunctions/RHTower/Sieve/ShiftedCongruenceCount.lean`.

- `card_filter_dvd_add_shift` — `#{n ∈ (t,t+L] : M ∣ n+s} = #{m ∈ (t+s,t+s+L] : M ∣ m}`.
- `abs_card_filter_dvd_add_shift_sub_lt` — **the count differs from `L/M` by less than one,
  uniformly in the shift `s`**.

Both unconditional.

This is the second congruence a shifted correlation requires: `d² ∣ n` together with `e² ∣ n+h`. The
corpus already owned the unshifted sieve remainder bound (`Sieve/IntervalMultiples`); translating the
window rather than the modulus reduces the shifted case to it exactly, with no error term of its own.

Translation also avoids truncated subtraction entirely — the shifted window is `(t+s, t+s+L]`, never
a difference of naturals — which is what makes the reduction exact rather than approximate.

### Formal layer — the two congruences have a common solution

`formal/GaloisForLFunctions/RHTower/Sieve/JointCongruence.lean`.

- `negShift b h := (b − h % b) % b` — the natural representative of `−h` mod `b`.
- `negShift_add_dvd` — `b ∣ negShift b h + h` (axioms: `[propext]` only).
- `exists_joint_solution` — **for coprime moduli there is `n₀` with `a ∣ n₀` and `b ∣ n₀ + h`.**

Both unconditional.

A shifted correlation weighted by the squarefree identity `μ²(n) = ∑_{d²∣n} μ(d)` meets the pair of
conditions `d² ∣ n` and `e² ∣ n+h`. For coprime `d, e` the Chinese remainder theorem makes that pair
a single residue class, whose count in a window is then governed by the shifted-congruence bound of
the previous module.

One correctness note worth recording: the natural-number formula `b − h % b` is *not* the right
representative when `b ∣ h` (it gives `b`, not `0`), which is why `negShift` carries the outer `% b`.
The proof goes through `Nat.mod_add_mod` rather than assuming the two agree.

### Formal layer — the joint congruence is one residue class

`formal/GaloisForLFunctions/RHTower/Sieve/JointCongruenceClass.lean`.

- `joint_iff_dvd_shift` — for coprime moduli, **`a ∣ n ∧ b ∣ n+h ↔ ab ∣ n + negShift(ab) n₀`**,
  where `n₀` is any common solution.
- `abs_card_joint_sub_lt` — **the joint count in a window differs from `L/(ab)` by less than one**.

Both unconditional.

So the pair of conditions produced by expanding `μ²(n) = ∑_{d²∣n} μ(d)` on both `n` and `n+h` is no
harder to count than a single congruence: for coprime `d, e` the conditions `d² ∣ n` and `e² ∣ n+h`
cut out one class mod `d²e²`, counted with error below one uniformly in the shift `h` and the start.

Both directions of the equivalence run through `Nat.ModEq`, so no truncated natural subtraction
occurs anywhere — which is what keeps the statement exact rather than approximate. The positivity
hypothesis `0 < ab` is genuinely needed: at `a = 0` the modulus degenerates and the residue class
argument fails.

### Formal layer — the truncated pair sum as a weighted joint count

`formal/GaloisForLFunctions/RHTower/Sieve/TruncatedPairSwap.lean`.

- `sum_truncated_pair_eq` — **`∑_{n ∈ (t,t+L]} (∑_{d≤R, d²∣n} μ(d))(∑_{e≤R, e²∣n+h} μ(e))
  = ∑_{d,e≤R} μ(d)μ(e)·#{n ∈ (t,t+L] : d²∣n ∧ e²∣n+h}`**.

Unconditional, and exact — the exchange of summation incurs no error of its own.

With the previous module this assembles the two-variable sieve for a shifted correlation: the double
sum is reduced to joint counts, and each joint count with `gcd(d,e) = 1` equals `L/(d²e²)` to within
one, uniformly in `h` and `t`.

What is deliberately *not* claimed: the pairs with `gcd(d,e) > 1` are not evaluated here. Their
modulus is `lcm(d²,e²)` and solvability depends on whether the gcd divides `h`, so they need separate
treatment. The reduction above is exact regardless; only the evaluation of those terms is outstanding.

### Formal layer — the non-coprime pairs

`formal/GaloisForLFunctions/RHTower/Sieve/JointCongruenceEmpty.lean`.

- `gcd_sq_dvd_of_joint` — a common solution forces **`gcd(d,e)² ∣ h`**.
- `card_joint_eq_zero` — hence pairs with `gcd(d,e)² ∤ h` contribute **nothing**.
- `coprime_of_joint_of_squarefree` — **for squarefree `h`, every contributing pair is coprime.**

All unconditional.

This closes the gap flagged in the previous section. The non-coprime pairs are not evaluated but
*eliminated*: if `d² ∣ n` and `e² ∣ n+h` then `g = gcd(d,e)` satisfies `g² ∣ n` and `g² ∣ n+h`, so
`g² ∣ h`. The shift therefore decides which non-coprime pairs can occur at all, and when `h` is
squarefree only `g = 1` survives — so the truncated pair sum is entirely coprime and
`abs_card_joint_sub_lt` applies to every term.

The two-variable sieve for a shifted correlation is complete for squarefree shifts.

### Formal layer — the truncated squarefree pair count

`formal/GaloisForLFunctions/RHTower/Sieve/TruncatedPairCount.lean`.

- `abs_truncated_pair_sub_le` — for **squarefree** `h`,
  **`|∑_{n ∈ (t,t+L]} Q_R(n)Q_R(n+h) − L·∑_{d,e≤R, (d,e)=1} μ(d)μ(e)/(d²e²)| ≤ R²`**,
  uniformly in the start `t` and the shift `h`.

Unconditional.

This is the two-variable analogue of the corpus's `abs_truncated_squarefree_sub_le` and completes the
elementary sieve treatment of a shifted *squarefree* correlation: swap identity, elimination of the
non-coprime pairs, joint counts each accurate to within one, and `R²` pairs in total.

Scope, stated precisely: this evaluates the correlation of the **squarefree indicator** `μ²`, not of
`μ` itself. The `μ(d)μ(e)` appearing above are sieve coefficients, not values of the correlated
function. The genuinely open input remains cancellation in `∑_n μ(n)μ(n+h)`, where the signs of μ at
`n` and `n+h` must interact — something no counting argument reaches.

### Formal layer — the pair main term is bounded

`formal/GaloisForLFunctions/RHTower/Sieve/PairMainTermBound.lean`.

- `abs_main_pair_le` — **`|∑_{d,e≤R, (d,e)=1} μ(d)μ(e)/(d²e²)| ≤ 4`**, uniformly in `R`.

Unconditional.

With `abs_truncated_pair_sub_le` this makes the truncated pair sum `O(L) + O(R²)` with explicit
constants, and it does so **without evaluating the density as an Euler product** — the bound is just
`(∑_{d≤R} 1/d²)² ≤ 4`, using the corpus's `SquarefreeHarmonic.sum_inv_sq_le_two`.

Worth noting for what it avoids: the natural route to the pair density is
`∏_p(1 − 2/p²)` adjusted at primes with `p² ∣ h`, which needs infinite products and their
convergence. That is unnecessary for every use these cards make of the pair count, where only an
upper bound of the correct order is required.

### Formal layer — explicit upper bound for the truncated pair sum

`formal/GaloisForLFunctions/RHTower/Sieve/TruncatedPairUpper.lean`.

- `abs_truncated_pair_le` — for squarefree `h`,
  **`|∑_{n ∈ (t,t+L]} Q_R(n)Q_R(n+h)| ≤ 4L + R²`**, uniformly in `t`, `h` and `R`.

Unconditional, with both constants explicit.

This is the usable form of the two-variable sieve: a single inequality with no density constant to
evaluate and no hypothesis beyond squarefreeness of the shift. It follows from the pair count and the
main-term bound by the triangle inequality.

The seven-module shifted squarefree sieve is now complete and self-contained:
`ShiftedCongruenceCount` → `JointCongruence` → `JointCongruenceClass` → `TruncatedPairSwap` →
`JointCongruenceEmpty` → `TruncatedPairCount` → `PairMainTermBound` → this.

### Formal layer — assembling step 1 of the proof

`formal/GaloisForLFunctions/RHTower/Sieve/GoodStartCount.lean`.

- `card_le_good_add_bad` — **`#S ≤ #{good starts} + #Bad₁ + #Bad₂`**, where a start is *good* when
  both Möbius sign counts on `(t, t+L]` are at least `(3/16)DL`, `Bad₁` is where the Möbius sum
  exceeds `⅛DL`, and `Bad₂` is where the squarefree count falls below `½DL`.

Unconditional.

This assembles step 1 of the proof — `(10)`, `(13)` and `(14)` combined. The two exceptional sets
enter from opposite directions: `Bad₁` comes from the mean-square input through Markov, `Bad₂` from
the elementary squarefree count, and `card_moebius_sign_ge` converts a start outside both into one
carrying linearly many integers of each sign.

Phrased as a covering inequality in `ℕ` rather than a subtraction, so it composes with the
exceptional-set bounds without any truncation caveat.

### Formal layer — step 1 with the mean-square input as a hypothesis

`formal/GaloisForLFunctions/RHTower/Sieve/GoodStartMarkov.lean`.

- `card_le_good_add_meanSquare` — **`#S ≤ #{good starts} + V/(DL/8)² + #Bad₂`**, assuming only
  `∑_{t ∈ S} M(t,L)² ≤ V`.

Unconditional as an implication.

The hypothesis `hms` *is* the published mean-square input; everything else in the statement is
proved here — Markov via `RHTower.card_large_le_of_sum_sq_le`, the sign-count identity, and the
covering argument.

This is the form the cards' dependence should be read in: step 1 of the proof is a single theorem
whose only unproved ingredient is one named hypothesis. Supplying `V` of the size Menon's theorem
gives makes the exceptional term `o(#S)` and the conclusion is the card's `(14)` for almost every
start.

### Formal layer — equation (7), squarefree half; and an audit correction

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeIndicator.lean`.

- `filter_sq_dvd_eq_singleton` — at squarefree `n`, the only `d` with `d² ∣ n` is `d = 1`.
- `sum_moebius_sq_dvd_of_squarefree` — hence **`∑_{d² ∣ n} μ(d) = 1 = μ²(n)`** there.

Unconditional.

**Audit correction.** The Lean-status line above claims "the squarefree count `(7)`/`(11)`" is
formalized. That is accurate for `(11)` but not for `(7)`: `Sieve/SquarefreeCount.lean` works
throughout with the *truncated* sum `∑_{d ≤ R, d²∣n} μ(d)` and does not mention the predicate
`Squarefree` at all — the string does not occur in the file. The identity `μ²(n) = ∑_{d²∣n} μ(d)` is
absent from mathlib as well.

This module supplies the squarefree half. The complementary half — that the sum vanishes at
non-squarefree `n` — needs `{d : d² ∣ n}` identified with the divisors of the square part of `n`, and
is **not** proved here. It is recorded as outstanding rather than assumed.

### Formal layer — μ² is the squarefree indicator

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeIndicator.lean`.

- `moebius_sq_eq_indicator` — **`μ(n)² = 1` exactly when `n` is squarefree, `0` otherwise.**
- `sum_moebius_sq_eq_card` — hence `∑_{n ∈ (t,t+L]} μ(n)² = #{n ∈ (t,t+L] : n squarefree}`.

Unconditional.

This supplies the *other* side of equation `(7)`. The identity `μ²(n) = ∑_{d²∣n} μ(d)` has two
halves, and the position is now exactly:

- `μ²(n) = squarefree indicator` — **proved** (this section);
- `∑_{d²∣n} μ(d) = 1` at squarefree `n` — **proved** (previous section);
- `∑_{d²∣n} μ(d) = 0` at non-squarefree `n` — **outstanding**; it needs `{d : d² ∣ n}` identified
  with the divisors of the square part of `n`.

`sum_moebius_sq_eq_card` is what lets the squarefree *count* `Q(t,L)` appearing in
`card_moebius_sign_ge` and `GoodStartMarkov` be written as a sum of `μ²`, which is the form the
sieve estimates produce.

### Formal layer — equation (7) is now complete

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeIndicatorZero.lean`.

- `sum_sq_dvd_eq_sum_squarefree` — the square-divisor sum may be restricted to squarefree `d`.
- `sum_moebius_sq_dvd_of_not_squarefree` — **the sum vanishes at non-squarefree `n`.**
- `moebius_sq_eq_sum_sq_dvd` — **equation `(7)`: `μ²(n) = ∑_{d²∣n} μ(d)`, for every `n ≥ 1`.**

All unconditional.

The outstanding half flagged in the previous section is closed, so the audit gap on `(7)` is
resolved and the status line above is now accurate.

The proof avoids factorisation entirely. Fix a prime `p` with `p² ∣ n`; on the squarefree `d` with
`d² ∣ n` the map `d ↦ d/p` (if `p ∣ d`) or `d ↦ dp` (otherwise) is an involution reversing the sign
of μ, so the sum cancels in pairs. Well-definedness needs only that `d² ∣ n` and `p² ∣ n` with
`p ∤ d` give `d²p² ∣ n` by coprimality — the square part of `n` is never constructed, and no
`Nat.factorization` machinery is used.

Restriction to squarefree `d` is essential rather than cosmetic: on `d` divisible by `p²` the map is
not an involution, and those terms are discarded first precisely because `μ` vanishes there.

### Formal layer — the truncation defect of the squarefree identity

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeTruncationDefect.lean`.

- `le_of_sq_dvd` — `d² ∣ n` with `n ≥ 1` forces `d ≤ n`.
- `abs_moebius_sq_sub_trunc_le` — **`|μ²(n) − ∑_{d ≤ R, d²∣n} μ(d)| ≤ #{d ∈ (R,M] : d² ∣ n}`**
  for `n ≤ M`.

Unconditional.

This is the bridge the corpus was missing between its two halves. `Sieve/SquarefreeCount.lean`
estimates the *truncated* sum `Q_R`, and `(13)` needs the *true* squarefree count `Q`; the defect
between them is now bounded pointwise by the count of omitted square divisors — which is exactly the
object `Sieve/AveragedSquarefreeTail.sum_tail_divisor_count_le` bounds on average over starts.

`le_of_sq_dvd` removes what would otherwise be a side condition: since `d² ∣ n` already forces
`d ≤ n`, the truncated sum is a genuine subsum of the full one for **every** `R`, with no hypothesis
relating `R` to `n`.

### Formal layer — the window truncation defect

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeTruncationDefect.lean`.

- `abs_window_squarefree_sub_trunc_le` — **`|Q(t,L) − Q_R(t,L)| ≤ ∑_{d ∈ (R,M]} #{n ∈ (t,t+L] : d²∣n}`**
  for `t + L ≤ M`.

Unconditional.

The right-hand side is *exactly* the summand of `AveragedSquarefreeTail.sum_tail_divisor_count_le`,
so the two results now compose directly: summing over starts bounds the averaged defect by
`L·((B+L−A)/R + M)`, which is the card's `(12)`.

Chain for `(11)`–`(13)`, now complete and unconditional:
`(7)` `moebius_sq_eq_sum_sq_dvd` → pointwise defect → window defect (this) → averaged defect
(`sum_tail_divisor_count_le`) → Markov (`card_large_le_of_sum_sq_le`) → `(13)`. The corpus previously
had the two ends and neither of the two middle links.

### Formal layer — lower bound for the true squarefree count

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeTruncationDefect.lean`.

- `squarefree_count_ge` — **`Q(t,L) ≥ D·L − (R + L/R) − defect(t)`**, where `D = squarefreeDensity`
  and `defect(t) = ∑_{d ∈ (R,M]} #{n ∈ (t,t+L] : d²∣n}`.

Unconditional.

This is the deterministic core of `(11)`–`(13)` for the **true** squarefree count, as opposed to the
truncated one: the sieve main term, its error `R + L/R`, and the truncation defect combined in a
single inequality, valid for every start with no exceptional set.

Only one step now separates it from `(13)`: the defect is `o(L)` for all but few starts, which is
Markov applied to `AveragedSquarefreeTail.sum_tail_divisor_count_le`. Both of those are already in
the corpus, so `Bad₂` in `GoodStartMarkov` is discharged by existing results rather than assumed.

### Formal layer — equation (13): the deficient starts are few

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeExceptional.lean`.

- `card_large_le_of_sum_le` — **Markov for a nonnegative quantity**: if the values sum to at most `V`,
  at most `V/θ` of them reach `θ`. (The corpus previously had only the mean-*square* form.)
- `card_squarefree_deficient_le` — **equation `(13)`**: the starts with
  `Q(t,L) < ½DL` number at most `V/θ`, where `θ = ½DL − (R + L/R)` and `V` bounds the summed
  truncation defect.

Both unconditional.

`Bad₂` in `GoodStartMarkov` is now supplied by a proved theorem rather than assumed. The elementary
half of step 1 is complete: `(7)` → truncation defect → `squarefree_count_ge` → `(13)`, with the
averaged tail (`AveragedSquarefreeTail`) providing `V`.

What remains hypothetical in step 1 is only `Bad₁`, which is the mean-square input `(6)`/`(15)` — as
the cards state.

### Formal layer — step 1, fully explicit

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeExceptional.lean`.

- `card_le_good_add_explicit` — **`#S ≤ #{good starts} + V/(DL/8)² + W/θ`**, where
  `θ = ½DL − (R + L/R)`, `V` bounds the mean square of the Möbius sums, and `W` bounds the summed
  truncation defect.

Unconditional as an implication.

Both exceptional sets are now explicit, and the two hypotheses have different status: `hdef` (the
`W` bound) is elementary and supplied by `AveragedSquarefreeTail.sum_tail_divisor_count_le`, while
`hms` (the `V` bound) **is** the published mean-square input.

Step 1 of the Hall-law argument is therefore a single theorem with exactly one non-elementary
hypothesis, and that hypothesis is `(6)`/`(15)` verbatim. Everything else — the sign-count identity,
equation `(7)`, the truncated-to-true squarefree bridge, `(13)`, Markov in both the mean-square and
nonnegative forms, and the covering argument — is proved in the corpus.

### Formal layer — equation (13) with no free parameter

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeExceptional.lean`.

- `card_squarefree_deficient_Ico_le` — **`#{t ∈ [A,B) : Q(t,L) < ½DL} ≤ L((B+L−A)/R + M)/θ`**,
  `θ = ½DL − (R + L/R)`.

Unconditional, with no free parameter: the averaged truncation tail
(`AveragedSquarefreeTail.sum_tail_divisor_count_le`) supplies the numerator directly.

This is the card's `(13)` in closed form. Combined with `card_le_good_add_explicit`, the *only*
remaining hypothesis anywhere in step 1 is the mean-square bound on the Möbius sums — the published
input. Every elementary ingredient is now a proved theorem with explicit constants.

Audit note: the same status-line overstatement found on the Hall-law card (claiming `(7)` proved)
also affected this card's `(20)`. Both are corrected above, and both statements are now genuinely
proved. Range citations such as "`(19)`-`(21)`" are what concealed the gap — the endpoints were
formalized and the middle statement was not.

### Formal layer — the marker block contribution

`formal/GaloisForLFunctions/RHTower/Sieve/MarkerBlockLower.lean`.

- `card_markerBlockTargets_ge` — **`#P · c ≤ #(markerBlockTargets P C)`** whenever every retained
  marker has at least `c` cofactors.

Unconditional.

This is the step that converts "many good starts" into "many distinct targets", i.e. `(25)`. It rests
on `card_markerBlockTargets`, which gives the target count as *exactly* `∑_{p∈P} #(C p)` — the
pair-to-product map being injective — so no multiplicity correction is needed and the bound counts
physical integers.

In the application `c = (3/16)DL` comes from `card_moebius_sign_ge` at a good start, and `#P` is the
number of retained markers after the discards of `(10)` and `(13)`.

### Formal layer — matching inside a cell

`formal/GaloisForLFunctions/RHTower/Sieve/CellMatching.lean`.

- `exists_injOn_of_card_le` — **`#s ≤ #t → ∃ f, Set.InjOn f s ∧ ∀ x ∈ s, f x ∈ t`.**

Unconditional.

This is the step that turns the counting statement into the transport map the Hall claim asserts:
"matching inside disjoint cells yields a literal injection". Without it the theorem would only say
targets outnumber sources, which is not the same as exhibiting an injection.

Nothing beyond cardinality is used — a subset `t' ⊆ t` of equal size is chosen and the equivalence
`s ≃ t'` transported — so the matching is available cell by cell, and disjoint cells compose because
the images stay inside their own cell.

### Formal layer — matching with bounded displacement

Added to `formal/GaloisForLFunctions/RHTower/Sieve/CellMatching.lean`.

- `exists_injOn_displacement_le` — sources and targets in a common window of length `H`, with
  `#s ≤ #t`, are matched by an injection satisfying **`|f(x) − x| ≤ H`** for every source.

Unconditional.

This is step 4's conclusion as a statement about an actual map: an injection from source primes to
targets, inside the cell, **with the displacement bound the Gibbs cost estimate `(5)`/`(27)` consumes**.
Previously the displacement was argued informally from both sets lying in `(X, X+H]`; it is now
derived, and the bound is stated in `ℤ` so no truncated subtraction hides the negative case.

Combined with `card_markerBlockTargets_ge` (targets are plentiful) and `Sieve/BrunTitchmarsh` (source
primes are few), this completes the elementary content of step 4.

### Formal layer — the transport cost of the matching

`formal/GaloisForLFunctions/RHTower/Sieve/TransportCostWindow.lean`.

- `finiteDampedLaplaceTransportCost_le` — **`cost ≤ #s · (x · H)`** once every edge moves no further
  than `H`, since the damping factor `exp(−min(u,v)x)` never exceeds one on nonnegative data.

Unconditional.

With `#s = O(X)` edges across a dyadic shell and `x ≍ X⁻¹` this is `O(H) = X^{1/2+o(1)}`, the cards'
cost claim `(5)`/`(27)`/`(36)`.

Corpus check: `MobiusBoundaryOppositeSignTransport.lean` already owns the sharp one-edge estimate
`abs_exp_neg_mul_sub_exp_neg_mul_le_transportCost`, the aggregate definition, and a Hall-based
injective matching built on mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`. Only
the specialisation of the aggregate to a bounded-displacement window was missing; the one-edge
estimate was not rebuilt.

### Audit — the formalization does not use the prime number theorem

The prose derives the marker supply `(19)` from "the ordinary PNT on fixed dyadic intervals", and the
hostile audit above defends that choice against Maier's theorem. The **formalization does not need
it**: `Sieve/PrimeWindow.card_bigPrimeSet_ge` and `card_bigPrimeSet_ratio_ge` give

`(log Q − 2·mertensFirstConst)·M / log M ≤ #{primes in (M, QM]}`

from **Mertens' first theorem alone** — an elementary Chebyshev-type lower bound, with an explicit
constant and no PNT anywhere in its dependency cone.

So the formal argument rests on a strictly weaker hypothesis set than the paper argument: the only
non-elementary input remaining is the mean-square theorem `(6)`/`(15)`. This is worth recording
because a reader of the prose would reasonably expect two external inputs, and there is only one.

### Formal layer — the kernel is constant on the bulk

`formal/GaloisForLFunctions/RHTower/Sieve/WindowKernelBulk.lean`.

- `windowOverlap_bulk` — at shift `h ≤ L`, **`K(n, n+h) = L − h`** for every start with `L ≤ n` and
  `n + h ≤ X`.
- `card_boundary_le` — fewer than `2L + 1` starts lie outside that bulk.

Both unconditional.

This is what makes the reduction usable with the literature's form of a correlation estimate. The
weighted sum `∑_n K(n,n+h)μ(n)μ(n+h)` appearing in the exact variance identity differs from
`(L−h)·∑_n μ(n)μ(n+h)` — the **unweighted** correlation that Chowla/Elliott-type results bound — by
at most `2L·L`, since the kernel is constant except on two boundary strips of fewer than `L` starts
each, where it never exceeds `L`.

So the hypothesis of `CorrelationToVariance.sum_normSq_window_le_of_correlation`, which is stated in
weighted form, can be discharged from an unweighted bound with an explicit `O(L²)` boundary loss.

### Formal layer — weighted correlation from unweighted

Added to `formal/GaloisForLFunctions/RHTower/Sieve/WindowKernelBulk.lean`.

- `abs_sum_kernel_sub_bulk_le` — for coefficients bounded by one,
  **`|∑_n K(n,n+h)c_n − (L−h)·∑_{bulk} c_n| ≤ (2L+1)·L`**.

Unconditional.

The remark of the previous section is now a theorem. The exact variance identity is stated with the
kernel weights, whereas Chowla/Elliott-type results bound the *unweighted* correlation
`∑_n μ(n)μ(n+h)`; this converts between them with an explicit `O(L²)` boundary loss, so the
hypothesis of `CorrelationToVariance.sum_normSq_window_le_of_correlation` can be discharged from a
literature-form bound.

Recorded because the two objects are genuinely different and the difference was previously
unexamined — the weighted form is what the identity produces, the unweighted form is what any
citable estimate would supply.

### Formal layer — the variance from an unweighted correlation bound

`formal/GaloisForLFunctions/RHTower/Sieve/UnweightedCorrelation.lean`.

- `sum_normSq_window_le_of_unweighted` — **`∑_{x<X}‖∑_{x<n≤x+L} a_n‖² ≤ L∑_n‖a_n‖² + 2L(Lε + (2L+1)L)`**
  from `|∑_{n ∈ bulk} a_n conj a_{n+h}| ≤ ε` at the shifts `1 ≤ h < L`, and nothing else.

Unconditional as an implication (axioms `[propext, Classical.choice, Quot.sound]`).

This is the reduction in the form a citable theorem can actually discharge. Earlier versions stated
the hypothesis in the kernel-weighted form the exact identity produces; no result in the literature is
phrased that way. Here the hypothesis is the plain correlation sum — what a Chowla/Elliott-type
estimate bounds — with the conversion cost `(2L+1)L` per shift carried explicitly rather than hidden.

The mean-square input `(6)`/`(15)` is therefore reduced, unconditionally and with explicit constants,
to a bound on the `L−1` unweighted shifted Möbius correlations.

### Formal layer — the Möbius mean square from a correlation bound

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusUnweighted.lean`.

- `re_moebiusC_mul_conj` — for the real-valued μ the Hermitian pair weight is the plain product
  `μ(n)μ(n+h)`.
- `sum_normSq_window_moebius_le_of_correlation` — **`∑_{x<X}‖∑_{x<n≤x+L} μ(n)‖² ≤
  L·#{n < X+L+1 : squarefree} + 2L(Lε + (2L+1)L)`** whenever `|∑_{n∈bulk} μ(n)μ(n+h)| ≤ ε` at the
  shifts `1 ≤ h < L`.

Unconditional as an implication.

This is the cards' mean-square input `(6)`/`(15)` stated for μ itself, reduced with explicit
constants to a bound on `L−1` shifted Möbius correlations — the exact statement a Chowla/Elliott-type
theorem provides. The diagonal is the squarefree count, already estimated elementarily.

The reduction is complete: no step between "correlations cancel" and "the mean square is small"
remains unproved.

### Formal layer — the mean square in the shape step 1 consumes

Added to `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusUnweighted.lean`.

- `normSq_sum_moebiusC_eq` — the complex window sum of μ has the real window sum as its modulus.
- `sum_sq_moebius_le_of_correlation` — **`∑_{t<X} M(t,L)² ≤ L·Q + 2L(Lε + (2L+1)L)`** from the
  correlation bound.

Unconditional as an implication.

The left side is exactly the hypothesis `hms` of `card_le_good_add_explicit`, so the two halves now
compose: a bound on the `L−1` shifted Möbius correlations gives step 1 of the Hall-law argument
directly, with no mean-square theorem cited in between.

The bridge lemma is needed because the variance layer works with `‖·‖²` of a complex window sum while
step 1 is stated for the real sum `M(t,L)`; they agree because μ is real-valued, but that had to be
proved rather than assumed.

### Formal layer — step 1 from a correlation bound

`formal/GaloisForLFunctions/RHTower/Sieve/Step1FromCorrelation.lean`.

- `card_le_good_add_correlation` — **`X ≤ #{good starts} + (L·Q + 2L(Lε + (2L+1)L))/(DL/8)² + W/θ`**,
  `θ = ½DL − (R + L/R)`, from a bound `ε` on the `L−1` shifted Möbius correlations and the elementary
  truncation-tail bound `W`.

Unconditional as an implication.

**No mean-square theorem is cited anywhere in this chain.** Step 1 of the Hall-law argument now
follows from a bound on `∑_n μ(n)μ(n+h)` alone, with every intermediate step proved and every
constant explicit.

This is a strictly better dependency than the card's prose: the prose invokes Menon's mean-square
theorem `(6)` and the prime number theorem; the formalization uses neither — the marker supply comes
from Mertens (`Sieve/PrimeWindow`), and the mean square is *derived* from the correlations rather
than assumed.

### The low-breadth layer: the sieve error is now bounded

The card's `(8)` needs the low-breadth set `L_{c₀}(X,H)` to be smaller than the marker supply by a
power of `log X`.  The corpus already owns the entropy mechanism —
`Sieve/RateBridge.card_omega_le_le_rate` gives the lower tail with the rate
`woldBreadthDeviationRate t = 1 − t + t log t`, positive on `(0,1)`
(`MobiusWoldBreadthTwoSidedDeviationRate.woldBreadthDeviationRate_pos_of_lt_one`), and
`Sieve/OmegaDeviation.lean` assembles both tails — but its bound carries two error terms that must
be shown subpolynomial before it becomes an explicit negative power of `log z`.

One of the two is now bounded, unconditionally
(`Sieve/TruncDivisorCount.lean`, `[propext, Classical.choice, Quot.sound]`):

- `le_pow_of_mem_truncDivisors_primorial` — a Brun-truncated divisor of `z#` is squarefree with all
  prime factors at most `z` and at most `r` of them, hence at most `z^r`;
- **`card_truncDivisors_primorial_le`** — distinct such divisors are distinct integers of
  `[1, z^r]`, so

      #{d ∣ z# : ω d ≤ r}  ≤  z^r.

No combinatorics is involved: the count is bounded by the range, not by a binomial sum.  What remains
for `(8)`'s unconditional half is the parameter choice `(z, r, λ)` making both the tilt error
`exp(λc₁)(log z)^λ/(λ^r t^k)` and this sieve error `z^r/t^k` fall below `(log z)^{−δ}` — with
`r ≍ log log z` and `z` subpolynomial, which is what `z^r` being subpolynomial requires.

### The tilt error is gone too

`Sieve/OmegaTailAbsorbed.lean`, unconditional.  The tilt error of the lower tail is not intrinsic
either: it carries `λ^r` in the denominator, which grows geometrically in `r` while everything else
is fixed, so it can always be buried under the entropy main term.

- **`card_omega_le_le_absorbed`** — with the absorption hypothesis, both errors collapse:

      #{n ∈ (a,b] : ω n ≤ k}  ≤  2(b−a)·exp((1−t)c₀)·(log z)^{−I(t)}  +  z^r/t^k;

- **`exists_even_absorbing`** — the hypothesis is satisfiable for every tilt `λ > 1`: some even `r`
  works, because `λ^r` is unbounded;
- **`exists_card_omega_le_le_absorbed`** — hence, with no hypothesis beyond `k = t·log log z` and
  `0 < t ≤ 1`, there is an `r` with

      #{n ∈ (a,b] : ω n ≤ k}  ≤  2(b−a)·exp((1−t)c₀)·(log z)^{−I(t)}  +  z^r/t^k.

**Both error terms of the lower tail are now explicit and elementary**: the sieve one is `z^r`
(`TruncDivisorCount`), the tilt one is gone.  What remains for `(8)`'s unconditional half is purely
the schedule: choose `z` with `log z = (log X)^{1−ε}` so that `t = c₀/(1−ε) < 1` realises the card's
breadth cut `k = c₀ log log X`, and check `z^r = X^{o(1)}` against `H = X^{1/2+o(1)}` — with
`r ≍ log log z` from the absorption, `z^r = exp(O((log X)^{1−ε} log log X))`, which is `X^{o(1)}`.

### The absorbing exponent, explicitly

The existential `r` of `exists_even_absorbing` is not enough for the schedule: the sieve error `z^r`
has to be estimated, so `r` must be explicit.  It now is
(`Sieve/OmegaTailAbsorbed.lean`, unconditional):

- `mul_neg_log_le` — `t(−log t) ≤ 1 − t` on `(0,1]`, from `log u ≤ u − 1` at `u = 1/t`;
- **`one_div_pow_le_log`** — hence **the tilt weight costs at most one logarithm**: with
  `k = t·log log z` and `0 < t ≤ 1`,

      t^{−k}  =  exp(t(−log t)·log log z)  ≤  log z;

- `woldBreadthDeviationRate_le_one` — the entropy rate is at most one on `(0,1]`, so
  `(log z)^{−I(t)} ≥ (log z)^{−1}`;
- **`absorbing_of_pow_ge`** — combining the two, the absorption hypothesis holds as soon as

      2^r  ≥  exp(2c₁ + |c₀|) · (log z)^4 ,

  an explicit condition with no reference to `t` beyond `0 < t ≤ 1`.

**Only four logarithms are needed**, because both the tilt weight `t^{−k}` and the entropy weight
`(log z)^{−I}` cost at most one logarithm each, on top of the `(log z)^λ` of the tilt at `λ = 2`.  So
`r ≍ log log z` suffices, which is exactly what makes `z^r = exp(O(log z · log log z))` subpolynomial
in the card's schedule.

### The lower tail in final form

`Sieve/OmegaTailAbsorbed.lean` (continued), unconditional.

- **`card_omega_le_le_explicit`** — with the explicit absorbing exponent, the tilt disappears from
  the constants and `t^k` from the error (using `t^{−k} ≤ log z`):

      #{n ∈ (a,b] : ω n ≤ k}  ≤  2(b−a)·e^{|c₀|}·(log z)^{−I(t)}  +  z^r·log z .

  The tilt `t` now appears in exactly one place: the entropy exponent `I(t) = 1 − t + t log t`.

- `exists_even_pow_between` — the least even power of two above a positive `C` is below `4C + 1`;
- **`exists_card_omega_le_le_explicit`** — hence such an `r` exists with

      exp(2c₁+|c₀|)(log z)^4  ≤  2^r  ≤  4·exp(2c₁+|c₀|)(log z)^4 + 1 ,

  i.e. `r = O(log log z)` with an explicit constant, together with the bound above.

**The lower tail is now a closed formula in `(b−a, z, t)` alone**, with `r` pinned to within a factor
of four.  The remaining step for `(8)` is arithmetic on the schedule: with `log z = (log X)^{1−ε}`,
`r ≍ 4 log₂ log z` gives `z^r = exp(O((log X)^{1−ε} log log X)) = X^{o(1)}`, which is below
`H = X^{1/2+o(1)}`, while `t = c₀/(1−ε) < 1` realises the breadth cut `k = c₀ log log X` and leaves
the genuine saving `(log z)^{−I(t)}`.

### `(8)`'s unconditional half: the low-breadth density vanishes

`Sieve/OmegaTailAbsorbed.lean` (continued), unconditional.

- **`card_omega_le_div_le`** — the density form of the tail:

      #{n ∈ (a,b] : ω n ≤ k} / (b−a)  ≤  2e^{|c₀|}(log z)^{−I(t)}  +  z^r·log z/(b−a);

- **`tendsto_rpow_neg_rate`** — the entropy factor vanishes along any schedule with `log z → ∞`,
  because `I(t) > 0` strictly for `0 < t < 1`
  (`woldBreadthDeviationRate_pos_of_lt_one`);
- **`tendsto_card_omega_le_div_zero`** — hence, along any schedule with `log z → ∞`, breadth cut
  `k = t·log log z` at a fixed `t < 1`, absorbing exponent `r`, and sieve error small against the
  interval,

      #{n ∈ (a,b] : ω n ≤ k} / (b−a)  →  0 .

**This is the unconditional half of the card's `(8)`**: the low-breadth vertices are a vanishing
fraction of every cell, so the marker supply — which is a positive proportion of `H/log X` times a
growing factor — dominates them.  The two hypotheses are exactly the schedule conditions:
`log z → ∞` (a growing sieving level) and `z^r log z = o(b−a)` (a subpolynomial sieve error), both
satisfied by `log z = (log X)^{1−ε}` against `H = X^{1/2+o(1)}`, since `r = O(log log z)`.

### The cut may drift

The breadth cut of `(8)` is `k = ⌊c₀ log log X⌋`, so the tilt it induces,
`t = k / log log z`, is not a constant: it drifts with `X`.  The bound is nevertheless uniform,
because the entropy rate is monotone (`Sieve/OmegaTailAbsorbed.lean`, unconditional):

- **`woldBreadthDeviationRate_antitone`** — `I` is antitone on `(0,1]`.  Elementary, no calculus:
  `t·log(t′/t) ≤ t′ − t` by `log x ≤ x − 1`, hence

      I(t) − I(t′)  ≥  (t′ − t)(−log t′)  ≥  0 ;

- **`card_omega_le_div_le_of_le`** — so any cut with `t ≤ t₀` obeys the density bound with the
  entropy exponent frozen at `t₀`;
- **`tendsto_card_omega_le_div_zero_of_le`** — hence the low-breadth density vanishes for a
  *drifting* cut, provided only that it stays below a fixed `t₀ < 1`.

That is exactly the card's situation: `log log z ≥ (1−ε) log log X` gives
`t = k/log log z ≤ c₀/(1−ε) =: t₀ < 1` for `ε` small, uniformly in `X`.  The unconditional half of
`(8)` is therefore available in the form the schedule produces it, not only for a constant tilt.

### The sieve error, reduced to one exponent

The last schedule hypothesis, `z^r·log z = o(b−a)`, is now a single inequality between exponents
(`Sieve/OmegaTailAbsorbed.lean`, unconditional):

- **`tendsto_pow_mul_log_div_zero`** —

      z^r · log z / H  =  exp( r·log z + log log z − log H ),

  so the hypothesis *is* the statement that this one exponent tends to `−∞`;
- **`le_of_two_pow_le`** — `2^r ≤ M` gives `r ≤ log M / log 2`, so the size control of
  `exists_card_omega_le_le_explicit` (`2^r ≤ 4·exp(2c₁+|c₀|)(log z)^4 + 1`) reads

      r  ≤  ( 2c₁ + |c₀| + 4 log log z + log 4 + o(1) ) / log 2 ,

  i.e. `r = O(log log z)` with an explicit constant;
- **`tendsto_pow_mul_log_div_zero_of_exponent`** — and only that upper bound need enter: the caller
  supplies any `R ≥ r` and the exponent condition is checked with `R`.

**So the whole schedule reduces to `log z · log log z ≪ log H`.**  For the card's
`H = X^{1/2+o(1)}` that is satisfied by `log z = log X/(log log X)²`, which also keeps
`log log z = log log X·(1 − o(1))`, hence `t = k/log log z ≤ c₀(1+o(1)) < 1` — the ceiling the
drifting-cut theorem needs.

### The level is realisable, and the error condition is `(L+1)·log(L+1) ≪ log H`

The sieving level must be a natural number, so a schedule prescribes it as a real `L` and takes
`z = ⌈exp L⌉`.  That costs at most an additive constant
(`Sieve/OmegaTailAbsorbed.lean`, unconditional):

- `sieveLevel L = ⌈exp L⌉`, `two_le_sieveLevel` — above the threshold the tail lemmas need;
- **`log_sieveLevel_mem`** — `L ≤ log(⌈exp L⌉) ≤ L + 1`.  The upper half is
  `⌈exp L⌉ < exp L + 1 ≤ 2·exp L ≤ exp(L+1)`, using `2 ≤ e`;
- `one_le_log_sieveLevel`.

- **`tendsto_schedule_error`** — with the level realised this way, and `r` controlled by the size
  bound of `exists_card_omega_le_le_explicit`, the entire sieve-error hypothesis becomes

      ( log(4e^κ + 1) + 4 log(L+1) ) / log 2 · (L+1)  +  log(L+1)  −  log H  →  −∞ ,

  `κ = 2c₁ + |c₀|`; that is, **`(L+1)·log(L+1) ≪ log H`** with an explicit constant.

The bound `4e^κ(log z)^4 + 1 ≤ (4e^κ+1)(L+1)^4` is what turns the `Nat.find` exponent into an
explicit `O(log(L+1))`, so nothing about `r` survives except its size.

For the card's schedule `L = log X/(log log X)²` and `H = X^{1/2+o(1)}`, the left side is
`≍ (log X/(log log X)²)·log log X = log X/log log X`, against `log H ≍ (log X)/2` — the condition
holds with room to spare, and `log log z = log log X·(1 − o(1))` keeps the drifting cut below its
ceiling.

### `(8)`'s unconditional half, as one theorem

**`Sieve/OmegaTailAbsorbed.tendsto_card_omega_le_div_zero_schedule`** (unconditional) collects the
whole layer into a single statement about a schedule given by its level:

    #{n ∈ (a X, b X] : ω n ≤ k X} / (b X − a X)  →  0

for any schedule with

* level `L → ∞`, `L ≥ 1`, sieving at `z = ⌈exp L⌉`;
* breadth cut `k X = t X · log log z`, the tilt `t X` drifting but bounded by a fixed `t₀ < 1`;
* absorbing exponent `r X` pinned two-sidedly by `e^κ(log z)^4 ≤ 2^{r X} ≤ 4e^κ(log z)^4 + 1`;
* the single analytic condition `(L+1)·log(L+1) ≪ log(b X − a X)`.

Nothing is quoted and nothing is assumed beyond the schedule.  The card's schedule
`L = log X/(log log X)²`, `H = X^{1/2+o(1)}` meets every clause.

**The low-breadth half of `(8)` is therefore closed.**  What the card still needs from outside is
only the marker supply `(4)`, which rests on the mean-square input the card cites — not on anything
in this layer.

### Formal layer — the truncation defect is discharged in both forms of step 1

Added: `formal/GaloisForLFunctions/RHTower/Sieve/Step1Explicit.lean`.

Both step-1 theorems carried *two* hypotheses, and the prose above asserted — without a Lean
witness — that the second one is elementary. It now is one:

- `card_le_good_add_correlation_explicit` — `card_le_good_add_correlation` with `hdef` supplied;
  the only remaining hypothesis is the correlation bound `ε`.
- `card_le_good_add_meanSquare_explicit` — `card_le_good_add_explicit` with `hdef` supplied;
  the only remaining hypothesis is the mean-square bound `V`.

In both, the truncation defect contributes the closed term

    L·((B + L − A)/R + M) / ( ½·D·L − (R + L/R) ),

obtained from `AveragedSquarefreeTail.sum_tail_divisor_count_le` (every integer lies in at most `L`
of the windows `(t, t+L]`); the correlation form is its `A = 0`, `B = X` instance.

Both are unconditional as implications: `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each. Wired into `GaloisForLFunctions.RHTower`.

Step 1 of the Hall-law argument is therefore a single theorem with exactly one hypothesis, in each
of the two shapes the published input can take. `card_le_good_add_correlation` and
`card_le_good_add_explicit` are no longer leaves.

### Toward the external input — the measure of large values, and the mean-value form of Halász

Added: `formal/GaloisForLFunctions/RHTower/Sieve/DirichletMeasureLargeValues.lean`.

The card's one remaining input is a short-interval mean square for Möbius. The corpus's route to it
runs through Halász's method, and the pointwise Euler estimate is proved unable to decay: it needs
`D² > ∑1/p + ∑1/p²`, while `D² = ∑1/p + ∑cos(t log p)/p` leaves `∑1/p² − ∑cos(t log p)/p`, which the
uniform frequency bound makes `O(log log T)` but never negative. Halász's actual argument averages
over `t` instead. These are the first bricks of that average.

- `volume_largeValues_le` — **`V²·|{t ∈ (0,T] : |F(t)| ≥ V}| ≤ (T + 4N(1 + log N))∑|a_n|²`**:
  Chebyshev's inequality applied to the corpus's integral mean value theorem. Unlike
  `DirichletLargeValuesCount.card_largeValues_le`, no spacing hypothesis and no choice of test points
  enters — the level set is measured directly, which is what an averaging argument needs.
- `volume_largeValues_Icc_le` — the same on the closed interval.
- `integral_norm_dirPoly_le_of_sup` — splitting the frequency range at `V`:
  `∫₀^T |F| ≤ V·T + M·|{|F| ≥ V}|` for any uniform sup `M`.
- `norm_dirPoly_le_sum_norm` — the trivial sup `|F| ≤ ∑|a_n|`, so the sup need not be assumed.
- `integral_norm_dirPoly_halasz` — the two combined:

      ∫₀^T |F| ≤ V·T + M·(T + 4N(1 + log N))·∑|a_n|² / V².

  This is the mean-value shape: the small frequencies are paid for by the threshold and the large
  ones by their measure, so no pointwise decay at any individual frequency is required.

- `integral_norm_dirPoly_halasz_l1` — the same with the trivial sup substituted, so the bound is a
  statement about the coefficients alone.

All six are unconditional (`[propext, Classical.choice, Quot.sound]`) and wired into
`GaloisForLFunctions.RHTower`.

### The twisted Möbius sum enters the corpus's own contour machinery

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusTwistPerron.lean`.

Audit correction to the note above: the `t = 0` case of the analytic input is **not** missing from
the corpus. `Sieve/ChebyshevPNT.tendsto_sum_vonMangoldt_div` is the prime number theorem and
`Sieve/MoebiusSharpLittleO.tendsto_norm_sum_moebius_div` is `‖∑_{n≤N} μ(n)‖/N → 0`, both
unconditional, both proved here by a full contour argument with the zero-free region. What the
frequency average needs is the *twisted* sum `∑_{n≤N} μ(n)n^{-iτ}`, and the first step of that is
now built:

- `moebiusTwist τ n = μ(n)·n^{-iτ}`, with `norm_moebiusTwist_le_one` — the twist is unimodular, so
  the corpus's smoothed Perron formula (stated for arbitrary coefficients of modulus at most one)
  applies verbatim;
- `tsum_moebiusTwist_cpow` — the twisted Dirichlet series is the untwisted one shifted:
  `∑ μ(n)n^{-iτ}n^{-s} = LSeries μ (s + iτ)`;
- `norm_tsum_moebiusTwist_smoothWeight_le` — **the Perron bound with the same constant for every
  twist**, because `norm_LSeries_moebius_le_uniform` is uniform in the height of the line.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

What this does not yet give is the saving: the shifted contour argument has to be run for
`invZeta(s + iτ)`, whose zero-free rectangle is the corpus's rectangle translated by `τ`. That
translation, not the Perron step, is the remaining work on this route.

### The contour shift transfers to the twist

Added: `formal/GaloisForLFunctions/RHTower/Sieve/InvZetaTwistShift.lean`.

The obstacle named at the end of the previous section is gone. Holomorphy of `invZeta(s + iτ)` on a
rectangle `[c,d] × [-T,T]` is holomorphy of `invZeta` on the translated rectangle
`[c,d] × [τ-T, τ+T]`, and that sits inside the corpus's own symmetric rectangle at height `|τ| + T`.
So no new analysis is needed — only a `MapsTo`:

- `mapsTo_add_mul_I` — the vertical shift carries `[c,d] × [-T,T]` into `[c,d] × [-(|τ|+T), |τ|+T]`;
- `differentiableOn_invZetaTwist_rect`, `differentiableOn_invZetaTwistW_rect` — holomorphy of the
  twisted integrand, by composition with that shift;
- `exists_integral_invZetaTwistW_shift` — **the four-edge identity for the twisted Perron integrand,
  unconditionally**, at every twist `τ` and every height `T`, the zero-free input being taken at
  height `|τ| + T`.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

The twist therefore costs exactly one thing: the passage from height `T` to height `|τ| + T`, which
is the loss the zero-free region already charges for working further up the strip. What remains on
this route is to re-run the *edge bounds* (`MoebiusContourBound`, `MoebiusSaving`) at the enlarged
height, which is where the `log⁹` of the zero-free region is spent.

### The twisted contour bound, assembled

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusTwistEdgeAssembly.lean`,
`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusTwistEdgeSubstitution.lean`.

The three edge estimates of the Perron argument (`TruncationError`, `HorizontalEdgeBound`,
`VerticalEdgeBound`) are already stated for an *arbitrary* integrand `F : ℂ → ℂ`, so they apply to
`invZeta(· + iτ)` with no change at all. Only the two `invZeta`-specific steps needed twisting, and
both are now proved:

- `tsum_moebiusTwist_smoothWeight_eq_invZeta_integral` — the twisted Perron identity in terms of the
  regular reciprocal;
- `norm_tsum_moebiusTwist_smoothWeight_le_edges` — the four-edge inequality for the twist;
- `continuous_invZetaTwist_line`, `continuousOn_invZetaTwist_left_line` — the two continuity inputs,
  by composing with `y ↦ y + τ`;
- `exists_norm_tsum_moebiusTwist_smoothWeight_le` — **the twisted contour bound**,

      ‖∑' μ(n)n^{-iτ}·w(n)‖ ≤ 2M_d C/T + 2 M_h C (d−c)/T^{j+1} + M_c(2(N+H)^c/c + 2C),

  with **one absolute constant `C`, uniform in the twist `τ`**.

All unconditional (`[propext, Classical.choice, Quot.sound]`), wired into
`GaloisForLFunctions.RHTower`.

The twist has cost exactly one thing throughout: the zero-free hypothesis is taken at height
`|τ| + T` instead of `T`. What remains is to substitute the concrete geometry — the abscissae
`c(K), d(K)` and the height `T(K)` of `MoebiusContourBound` — with `K` chosen large enough that
`3 + 2(|τ| + T(K)) ≤ K`; the edge bounds themselves (`InvZetaLeftLine`, `InvZetaEdgeBounds`) are
already pointwise in the height, so they apply at `y + τ` directly.

### The twisted contour bound at the concrete rectangle

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusTwistContourBound.lean`.

The concrete geometry substitutes with one adjustment. The twist moves every height by `τ`, so the
truncation height available to it is

    twistHeight K τ = truncHeight K − |τ|,

chosen so that `|τ| + twistHeight K τ = truncHeight K` exactly: **the twisted contour occupies the
same band as the untwisted one**, and the zero-free rectangle is the one already proved.

- `abs_add_twistHeight` — that identity;
- `exists_norm_tsum_moebiusTwist_smoothWeight_le_concrete` — **the twisted contour bound**, valid for
  every twist with `5 + 4|τ| ≤ K`, with the *same* `C`, `M₀` and the same edge constants
  `invZetaRightBound K`, `invZetaEdgeBound K` as the untwisted bound.

The side condition `5 + 4|τ| ≤ K` is exactly what keeps the two horizontal edges at distance at
least one from the real axis, which is where `norm_invZeta_horizontal_le` needs them; the three edge
estimates are pointwise in the height, so each applies at the shifted height with no change.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

The remaining steps on this route are the twisted analogues of `MoebiusSaving` (rewrite the left-edge
term `(N+H)^{c(K)}` as the saving `(N+H)·exp(−c₀ log(N+H)/(16 log⁹K))`) and of the width choice, which
together give `‖∑_{n≤N} μ(n)n^{-iτ}‖ = o(N)` uniformly over a growing range of `τ`.

### The twisted saving

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusTwistSaving.lean`.

`exists_norm_tsum_moebiusTwist_smoothWeight_le_saving` — the twisted contour bound with the left-edge
term written as the trivial size times a genuine decay,

    (N+H) · exp(−c₀·log(N+H) / (16 log⁹K)),

uniformly over twists with `5 + 4|τ| ≤ K`. The twist moved the *height* of the contour, not its
abscissa, so this step is unchanged from the untwisted argument.

Unconditional, wired into `GaloisForLFunctions.RHTower`.

**Route summary.** The twisted analogue of the corpus's own Möbius contour argument is now complete
up to the choice of smoothing width: Perron → shifted Dirichlet series → contour shift → four edges
→ concrete rectangle → saving, every step unconditional and every constant uniform in `τ`. The
remaining steps are the twisted analogues of `MoebiusContourBoundGeneral` (arbitrary smoothing
width), `MoebiusSmoothLittleO` and `MoebiusSharpLittleO`, which choose `H` and `K` and give

    sup_{|τ| ≤ T} ‖∑_{n ≤ N} μ(n)n^{-iτ}‖ = o(N)

for `T` growing with `N` — the frequency-uniform Möbius cancellation the mean-square input is
assembled from.

### The twisted contour bound at arbitrary smoothing width

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusTwistConcreteEdges.lean`,
`MoebiusTwistSharpSubstitution.lean`, `MoebiusTwistContourBoundGeneral.lean`.
`MoebiusTwistContourBound.lean` was refactored onto the first of these.

The concrete geometry is now factored out and reusable:

- `MoebiusTwistConcreteEdges` — `twistHeight`, `abs_add_twistHeight`, the abscissa geometry
  (`one_lt_rightAbscissa`, `leftAbscissa_pos`, …, all from `3 ≤ log K`), the zero-freeness of the
  band (`zero_free_twist_rect`) and the four edge bounds at the shifted heights
  (`norm_invZetaTwist_right_le`, `_top_`, `_bot_`, `_left_le`);
- `MoebiusTwistSharpSubstitution.norm_tsum_moebiusTwist_smoothWeight_le_sharp` — the twisted bound
  with the three cutoff-decay constants taken as hypotheses, so each is fixed at the abscissa
  actually met on its edge;
- `MoebiusTwistContourBoundGeneral.exists_norm_tsum_moebiusTwist_smoothWeight_le_general` — **the
  twisted contour bound at arbitrary smoothing width**, the cutoff entering only through the explicit
  factor `H^{-(j+1)}(N+H+1)^{j+1}`.

All unconditional (`[propext, Classical.choice, Quot.sound]`), all wired into
`GaloisForLFunctions.RHTower`.

This is the form in which the width can be chosen. What remains is the twisted analogue of
`MoebiusSmoothLittleO`/`MoebiusSharpLittleO`: pick `H` and `K` and conclude
`sup_{|τ| ≤ T} ‖∑_{n ≤ N} μ(n)n^{-iτ}‖ = o(N)`, the side condition `5 + 4|τ| ≤ K` fixing how fast `T`
may grow with `N`.

### The twisted Möbius sum is `o(N)`, uniformly in the twist

Added: `Sieve/MoebiusTwistCombinedBound.lean`, `MoebiusTwistContourBoundRatio.lean`,
`MoebiusTwistMajorantRatio.lean`, `MoebiusTwistSharpLittleO.lean`;
`Sieve/SmoothVsSharp.lean` was generalised (its Möbius statement is unchanged, and is now a corollary
of `norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one`, valid for any unimodular sequence).

The chain closes:

- `combined_terms_twist_le` — the twisted contour terms collapse to **twice** the untwisted collapse,
  because `twistHeight K τ ≥ truncHeight K / 2` whenever `|τ| ≤ truncHeight K / 2`, and
  `abs_le_half_truncHeight` shows the side condition `5 + 4|τ| ≤ K` already grants that. No estimate
  is repeated — the twisted collapse is *deduced* from the untwisted one.
- `exists_norm_tsum_moebiusTwist_smoothWeight_le_ratio`, `..._le_majorant_ratio` — the twisted bound
  in terms of the smoothing ratio, and against the majorant.
- **`exists_bound_norm_sum_moebiusTwist_div`** — a single `τ`-free bound `B(N) → 0` with

      ‖ ∑_{n ≤ N} μ(n)n^{-iτ} ‖ / N  ≤  B(N)   for every τ with 5 + 4|τ| ≤ contourParam(N + H),

  at the smoothing width `H = N/exp((log N)^{1/20})`.
- **`eventually_norm_sum_moebiusTwist_div_lt`** — its ε-form: for every `ε > 0`, eventually every
  admissible twist satisfies `‖∑_{n ≤ N} μ(n)n^{-iτ}‖ < εN`.

Since `contourParam x = ⌈exp((log x)^{1/10})⌉`, the admissible frequency range grows faster than any
power of `log N`. All unconditional (`[propext, Classical.choice, Quot.sound]`), all wired into
`GaloisForLFunctions.RHTower`.

**This is the frequency-uniform Möbius cancellation the mean-square input is assembled from**, and it
is now a theorem of this corpus rather than a citation. What the card's `(15)`–`(17)` still need
beyond it is the *short-interval* form — the passage from the full sum `∑_{n ≤ N}` to the windows
`∑_{x < n ≤ x+H}` — which is where the bilinear decomposition enters.

### Toward the short-interval form — the exact logarithmic kernel

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LogWindowKernel.lean`.

The remaining gap is the passage from the full sum `∑_{n ≤ N}` to the windows `∑_{x < n ≤ x+H}`.
Gallagher's reduction does it in two steps, and the first is now proved, exactly and elementarily.
Writing `S(u) = ∑_{u < log n ≤ u+δ} a_n`:

- `logWindow δ n = [log n − δ, log n)` — the set of positions at which `log n` is inside the window;
- `volume_real_logWindow_inter` — two such windows meet in a set of measure `(δ − |log n − log m|)₊`;
- **`integral_normSq_logWindowSum`** —

      ∫_ℝ |S(u)|² du = ∑_{n,m} Re(a_n conj(a_m)) · (δ − |log n − log m|)₊ .

No analysis enters: only the measure of the intersection of two half-open intervals of equal length.
Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**The second step, and why it is now cheap.** The triangular kernel `(δ − |L|)₊` is the Fourier
transform of the Fejér kernel, and *the corpus already owns that transform in closed form*:
`FejerSymmBound.integral_fejer_symm_real` gives `fejerWeightAt δ L = 2(1 − cos δL)/(δL²)`, with
`FejerBounds.fejer_transform_nonneg`, `fejer_transform_le_inv` and `fejer_transform_le_len` supplying
nonnegativity and both decay estimates. So the missing identity

    (δ − |L|)₊ = (δ/2π) ∫_ℝ fejerWeightAt δ ξ · e^{iLξ} dξ

is Fourier inversion applied to the compactly supported continuous function `(δ − |·|)₊`, whose
transform is integrable precisely by the corpus's own `1/ξ²` bound. Composing it with the identity
above gives Gallagher's lemma,

    ∫_ℝ |S(u)|² du = (1/π) ∫_ℝ ((1 − cos δξ)/ξ²) · |∑_n a_n n^{-iξ}|² dξ ,

with a kernel that is nonnegative and at most `min(δ²/2, 2/ξ²)` — the bridge from a short-interval
mean square to the Dirichlet polynomial, and hence to the twisted cancellation proved above.

Audit note: the classical Dirichlet integral `∫_ℝ (1 − cos aξ)/ξ² dξ = π|a|` is in neither mathlib
nor this corpus, but the inversion route does not need it.

### The triangular kernel and its transform

Added: `formal/GaloisForLFunctions/RHTower/Sieve/TriangularKernel.lean`.

- `tri δ t = (δ − |t|)₊`, with `tri_even`, `tri_eq_sub`, `tri_eq_zero`, `continuous_tri`;
- **`integral_tri_phase`** — `∫_ℝ (δ − |t|)₊ e^{itL} dt = δ · fejerWeightAt δ L`.

Reflecting the negative half onto the positive one turns the line integral into the corpus's own two
half-integrals, so the transform of the overlap kernel is the Fejér weight already computed in closed
form by `FejerSymmBound.integral_fejer_symm_real`, namely `2(1 − cos δL)/L²` — real, nonnegative, and
`O(L^{-2})`.

Unconditional, wired into `GaloisForLFunctions.RHTower`.

With `LogWindowKernel.integral_normSq_logWindowSum` this leaves exactly one step to Gallagher's
lemma: Fourier inversion for the compactly supported continuous `tri δ`, whose transform is
integrable by the `L^{-2}` bound the corpus already owns.

### Fourier inversion for the triangular kernel

Added: `formal/GaloisForLFunctions/RHTower/Sieve/TriangularInversion.lean`.

- `triC δ` — the triangular kernel as a complex-valued function, with `continuous_triC`,
  `hasCompactSupport_triC`, `integrable_triC`;
- **`fourier_triC`** — `𝓕 (triC δ) w = δ · fejerWeightAt δ (−2πw)`, i.e. mathlib's Fourier transform
  of the overlap kernel *is* the corpus's Fejér weight;
- `norm_fourier_triC_le` — the two corpus bounds (`≤ δ` from the interval length, `≤ 4/(δL²)` from
  the decay) combine into the Lorentzian majorant `2δ²/(1 + (δπw)²)`, since `x ≤ A` and `x ≤ B` force
  `x ≤ 2AB/(A+B)`;
- `integrable_fourier_triC` — hence the transform is integrable, the majorant being a scaled
  `(1 + x²)⁻¹`;
- **`fourierInv_fourier_triC`** — `𝓕⁻ (𝓕 (triC δ)) = triC δ`.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

Both halves of Gallagher's reduction are now theorems of this corpus: the exact overlap identity
(`LogWindowKernel`) and the inversion of its kernel (`TriangularKernel` + `TriangularInversion`).
Composing them expresses the logarithmic short-interval mean square as a nonnegative weighted
integral of `|∑_n a_n n^{-iξ}|²` — the bridge to the twisted cancellation proved earlier on this
card.

### The kernel in separated form

Added: `formal/GaloisForLFunctions/RHTower/Sieve/TriangularIntegralForm.lean`.

- **`triC_eq_integral`** — `(δ − |t|)₊ = ∫_ℝ e^{2πiwt} · 𝓕(triC δ)(w) dw`, Fourier inversion written
  out (via `𝓕⁻ f v = 𝓕 f (−v)`);
- `fourier_triC_conj` — the transform is real;
- `fourier_triC_re_nonneg` — and nonnegative.

Unconditional, wired into `GaloisForLFunctions.RHTower`.

This is the form the composition needs: in `e^{2πiw(log n − log m)} = n^{2πiw} · conj(m^{2πiw})` the
two indices separate, so substituting into `LogWindowKernel.integral_normSq_logWindowSum` and
exchanging the finite double sum with the integral turns the exact quadratic form into

    ∫_ℝ |S(u)|² du = ∫_ℝ (𝓕(triC δ)(w)).re · |∑_n a_n n^{2πiw}|² dw ,

a nonnegative weighted mean of the Dirichlet polynomial. That exchange is the one remaining step of
Gallagher's lemma; every ingredient it needs — the exact kernel, the transform, its reality,
nonnegativity and integrability — is now proved.

### Gallagher's lemma, proved

Added: `formal/GaloisForLFunctions/RHTower/Sieve/GallagherLemma.lean`.

The exchange is done, and with it the reduction:

- `logPoly a s w = ∑_{n ∈ s} a_n n^{2πiw}` — the Dirichlet polynomial in the additive variable;
- `phase_sub` — `e^{2πiw(x−y)} = e^{2πiwx}·conj(e^{2πiwy})`, the separation of the two indices;
- `sum_phase_eq_normSq` — hence the double sum of separated phases is `|logPoly|²`;
- `gallagherTerm`, `integrable_gallagherTerm`, `integral_gallagherTerm` — each term of the expansion
  is integrable and integrates to the exact kernel;
- **`gallagher_identity`** —

      ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du = ∫_ℝ Re 𝓕(δ − |·|)₊(w) · |∑_n a_n n^{2πiw}|² dw ;

- **`integral_fourier_triC_re`** — the weight has total mass exactly `δ`, since its integral is the
  triangular kernel at the origin;
- **`gallagher_le_of_sup`** — consequently `∫_ℝ |S(u)|² du ≤ M·δ` whenever `|logPoly| ² ≤ M`
  uniformly.

All unconditional (`[propext, Classical.choice, Quot.sound]`), all wired into
`GaloisForLFunctions.RHTower`.

**Gallagher's reduction is now a theorem of this corpus.** The short-interval mean square of any
coefficient sequence is a nonnegative weighted mean of its Dirichlet polynomial, with a weight of
total mass `δ` that is real, nonnegative, integrable and explicitly `O(w^{-2})`. Nothing arithmetic
enters it — only the Fourier pair of the triangular kernel, whose transform the corpus already owned
under the name `fejerWeightAt`.

### The tail of the Gallagher weight

Added: `formal/GaloisForLFunctions/RHTower/Sieve/GallagherTail.lean`.

- `fejerWeightAt_neg`, `fourier_triC_even` — the weight is even in the frequency;
- **`fourier_triC_re_le_inv_sq`** — `Re 𝓕(δ − |·|)₊(w) ≤ 1/(π²w²)`, the `δ` of the corpus's
  `4/(δL²)` bound cancelling against the `δ` in `𝓕 = δ·fejerWeightAt`;
- **`integral_Ioi_fourier_triC_re_le`** — the mass beyond height `W` is at most `1/(π²W)` on each
  side.

Unconditional, wired into `GaloisForLFunctions.RHTower`.

This is what lets a frequency-restricted bound be used. The weight has total mass `δ`
(`integral_fourier_triC_re`), so a bound `M₁` on `|∑_n a_n n^{2πiw}|²` valid only for `|w| ≤ W`,
together with the trivial bound `M₂` valid everywhere, gives

    ∫_ℝ |S(u)|² du ≤ M₁·δ + M₂·2/(π²W) ,

which is exactly the shape the twisted cancellation supplies: it bounds the Möbius Dirichlet
polynomial for `|τ| ≤ (contourParam − 5)/4`, i.e. for `|w|` up to a range growing faster than any
power of `log N`, and the trivial bound elsewhere.

### Gallagher's identity, split at a frequency height

Added: `formal/GaloisForLFunctions/RHTower/Sieve/GallagherSplit.lean`.

- `integral_Iic_fourier_triC_re_eq` — the left tail equals the right tail, by evenness of the weight
  and the reflection `w ↦ −w`;
- `integral_compl_Icc_fourier_triC_re_le` — the mass outside a symmetric band of height `W` is at
  most `2/(π²W)`;
- **`gallagher_split`** —

      ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du ≤ M₁·δ + M₂·2/(π²W)

  whenever `|∑_n a_n n^{2πiw}|² ≤ M₁` for `|w| ≤ W` and `≤ M₂` everywhere.

All unconditional (`[propext, Classical.choice, Quot.sound]`), wired into
`GaloisForLFunctions.RHTower`.

**This is the join.** The good range pays the weight's total mass `δ`; the bad range pays only its
tail. It is exactly the shape the twisted cancellation supplies — that theorem bounds
`‖∑_{n ≤ N} μ(n)n^{-iτ}‖` for `5 + 4|τ| ≤ contourParam(N+H)`, i.e. for `|w| ≤ W(N)` with `W` growing
faster than any power of `log N`, and the trivial bound `M₂ = N²` holds everywhere. With
`M₁ = (B(N)·N)²` the split reads

    ∫_ℝ |S_δ(u)|² du ≤ B(N)²N²δ + N²·2/(π²W(N)) ,

both terms small against the trivial size `N²δ` once `δ · W(N) → ∞` — which the growth of
`contourParam` grants.

What is still needed to reach the card's `(15)`–`(17)` is the change of variables from the
logarithmic windows `u < log n ≤ u+δ` to the linear windows `x < n ≤ x+h`, and the corpus's
`RealWindowVariance.integral_realWindow_eq_sum` already converts the discrete mean square into an
integral over linear windows.

### The logarithmic window is a multiplicative window

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LogWindowMultiplicative.lean`.

- **`logWindowSum_log`** — at `u = log x` the window `u < log n ≤ u + δ` is exactly the
  multiplicative window `x < n ≤ x·e^δ`;
- **`logWindowSum_log_linear`** — hence every *linear* window is a logarithmic window, at the ratio
  `δ = log((x+h)/x)`:

      logWindowSum a s (log((x+h)/x)) (log x) = ∑_{x < n ≤ x+h} a_n .

Unconditional, wired into `GaloisForLFunctions.RHTower`.

**The remaining mismatch, stated precisely.** Gallagher's identity holds for a *fixed* `δ`, while a
linear window of fixed length `h` corresponds to `δ = log(1 + h/x)`, which varies with `x`. Over a
range on which `x` is comparable to `X` the two agree up to a bounded factor: for `x ∈ [X, 2X]` and
`δ = log(1 + h/X)`, the multiplicative window `(x, x·e^δ]` has length `xh/X ∈ [h, 2h]`. Reconciling
them is a covering argument, not a new analytic input — and it is the last structural step between
`gallagher_split` and the card's `(15)`–`(17)`.

Note this direction cannot be obtained by set containment alone: the sums are signed, so a linear
window contained in a multiplicative one gives no bound. The passage has to be by exact identities
on comparable ranges, which is what the two theorems above provide.

### Tiling a long logarithmic window by short ones

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LogWindowTiling.lean`.

This is the covering step, and it is an exact identity rather than an approximation:

- `mem_logWindow_shift` — the shifted short window in interval form: `u + jδ` lies in the window of
  `n` iff `jδ < log n − u ≤ (j+1)δ`;
- `sum_indicator_logWindow_shift` — each `n` falls in **exactly one** of the `J` pieces, the one
  indexed by `⌈(log n − u)/δ⌉ − 1`, and in one at all iff it lies in the long window;
- **`logWindowSum_tiling`** —

      ∑_{u < log n ≤ u + Jδ} a_n = ∑_{j < J} ∑_{u + jδ < log n ≤ u + (j+1)δ} a_n ;

- `normSq_sum_range_le`, **`normSq_logWindowSum_tiling_le`** — with Cauchy–Schwarz,

      |∑_{u < log n ≤ u + Jδ} a_n|² ≤ J · ∑_{j < J} |∑_{u+jδ < log n ≤ u+(j+1)δ} a_n|² .

All unconditional (`[propext, Classical.choice, Quot.sound]`), wired into
`GaloisForLFunctions.RHTower`.

**This closes the structural gap.** A window of any prescribed length `Jδ` is now expressed through
windows of the fixed length `δ` that Gallagher's identity requires, at the cost of a factor `J`.
Combined with `logWindowSum_log_linear` — every linear window is a logarithmic one — and with
`gallagher_split`, the chain from a linear short-interval mean square to the twisted Möbius
cancellation is complete as a sequence of proved statements; what remains is choosing the parameters
`δ`, `J`, `W` against the card's regime and discharging the resulting arithmetic.

### The bound on a range of starting positions

Added: `formal/GaloisForLFunctions/RHTower/Sieve/GallagherRange.lean`.

- `integrable_normSq_logWindowSum` — the mean-square integrand is integrable (it is pointwise a
  finite sum of indicator terms);
- `setIntegral_normSq_logWindowSum_le` — since that integrand is nonnegative, the split bound over
  the whole line dominates the bound over **any** range `E` of positions;
- **`setIntegral_normSq_multiplicative_window_le`** — rewritten at `u = log x`, this is the mean
  square of the *multiplicative* short-interval sum `∑_{x < n ≤ x·e^δ} a_n` over any range of
  starting points:

      ∫ |∑_{x < n ≤ x·e^δ} a_n|² dlog x ≤ M₁·δ + M₂·2/(π²W) .

Unconditional, wired into `GaloisForLFunctions.RHTower`.

**Audit note — the honest state of the linear-window passage.** The chain now proves the card's
analytic input for *multiplicative* windows `(x, x·e^δ]`, which is the form Matomäki–Radziwiłł
themselves work in (their windows are `(x, x(1+1/T)]`). The card's `(15)`–`(17)` are stated for
*linear* windows `(t, t+L]` with integer `t`.

Passing between the two is **not** a matter of covering or containment, and the earlier note on this
card should not be read as claiming otherwise. Three routes were checked and each fails for the same
reason — the sums are signed:

* containment of index sets gives no inequality between signed sums;
* exact tiling (`logWindowSum_tiling`) needs the long window to be an *integer* multiple of the
  short one, and `log(1 + L/t)/δ` is not an integer;
* writing the difference `∑_{x<n≤x+L} = ∑_{x<n≤x·e^δ} − ∑_{x+L<n≤x·e^δ}` leaves a second window
  whose left endpoint is not of the required form.

So this is a genuine step of the Matomäki–Radziwiłł argument, not bookkeeping. It is the one
remaining item, and it is isolated: everything on both sides of it is proved.

### The linear-window passage, resolved

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LinearVsMultiplicativeWindow.lean`.

The obstruction recorded in the previous section was real but not fatal; the resolution is the
*difference*, not a comparison. For `0 ≤ L` and `x + L ≤ y`:

- **`sum_window_split`** — the multiplicative window splits **exactly**:

      ∑_{x < n ≤ y} a_n = ∑_{x < n ≤ x+L} a_n + ∑_{x+L < n ≤ y} a_n ;

- **`normSq_linear_le_multiplicative`** — hence

      |∑_{x<n≤x+L} a_n|² ≤ 2|∑_{x<n≤y} a_n|² + 2|∑_{x+L<n≤y} a_n|² ;

- `norm_sum_le_card`, **`normSq_linear_le_multiplicative_card`** — and for coefficients of modulus at
  most one the excess is bounded by its cardinality, giving

      |∑_{x<n≤x+L} a_n|² ≤ 2|∑_{x<n≤y} a_n|² + 2·#{x+L < n ≤ y}² .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**Why this closes it.** Take `y = x·e^δ` with `δ = log(1 + L/Y)` on a block where `Y ≤ x ≤ Y(1+ε)`.
Then `y = x + xL/Y` with `xL/Y ∈ [L, (1+ε)L]`, so the excess `(x+L, y]` holds at most `εL + 1`
integers and the second term is `O((εL)²)`. Summing over the `O(1/ε)` blocks that cover a dyadic
range, the multiplicative bound of `GallagherRange` controls the first term on each block. Balancing
`ε` against the Gallagher saving completes the passage — with only elementary counting, no further
analytic input.

Correction to the previous section: the three routes listed there fail as stated, but the list was
not exhaustive. Splitting off the excess and paying for it trivially is the fourth, and it works
because the excess is *short* — the multiplicative and linear windows share their left endpoint, so
their difference is a window of length `≤ εL`, not a window at a displaced position.

### The excess, measured by its length

Added to `formal/GaloisForLFunctions/RHTower/Sieve/LinearVsMultiplicativeWindow.lean`.

- `card_window_le` — the number of integers in a real window is at most its length plus one,
  `#{n : c < n ≤ y} ≤ y − c + 1` (via `Ioc ⌊c⌋₊ ⌊y⌋₊`);
- **`normSq_linear_le_multiplicative_length`** — hence the transfer in fully usable form:

      |∑_{x<n≤x+L} a_n|² ≤ 2|∑_{x<n≤y} a_n|² + 2(y − x − L + 1)² .

Unconditional, wired into `GaloisForLFunctions.RHTower`.

With `y = x·e^δ`, `δ = log(1 + L/Y)` and `Y ≤ x ≤ Y(1+ε)`, the excess length is
`y − x − L = xL/Y − L ≤ εL`, so the second term is `2(εL + 1)²`. Everything in the passage from a
linear short-interval mean square to the twisted Möbius cancellation is now a proved unconditional
theorem; instantiating the parameters is arithmetic on explicit constants.

### The linear window as a function of the logarithmic position

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LinearWindowMeasurable.lean`.

At position `u` the linear window is `e^u < n ≤ e^u + L`, i.e. `n − L ≤ e^u < n`, so as a function of
`u` each term is the indicator of `exp⁻¹(Ico (n−L) n)` — a measurable set.

- `linWindow`, `mem_linWindow`, `measurableSet_linWindow`;
- `linWindowSum`, **`linWindowSum_eq`** — it is the sum over the window;
- `measurable_linWindowSum`, `norm_linWindowSum_le` — measurable, and bounded by the `ℓ¹` norm of the
  coefficients;
- **`integrableOn_normSq_linWindowSum`** — hence the mean square is integrable on every set of finite
  measure.

Unconditional, wired into `GaloisForLFunctions.RHTower`.

This is what lets the pointwise transfer `normSq_linear_le_multiplicative_length` be *integrated*
over a block of positions: without it the left-hand side of the block estimate is not known to be an
integral of an integrable function. With it, integrating the transfer over
`u ∈ (log Y, log Y + log(1+ε)]` and applying `setIntegral_normSq_multiplicative_window_le` on the
right gives the block estimate

    ∫ |∑_{e^u < n ≤ e^u + L} a_n|² du ≤ 2(M₁δ + M₂·2/(π²W)) + 2(εL+1)²·log(1+ε) ,

with `δ = log(1 + L/Y)`.

### The block estimate

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LinearBlockEstimate.lean`.

- `normSq_linWindowSum_le_logWindowSum` — the pointwise transfer on a block, in window-sum form: for
  `log Y < u ≤ log(Y(1+ε))` and `δ = log(1 + L/Y)`,

      ‖linWindowSum a s L u‖² ≤ 2‖logWindowSum a s δ u‖² + 2(εL+1)² ,

  because the multiplicative window `(x, x·e^δ]` at `x = e^u` equals `(x, x + xL/Y]` with
  `xL/Y ∈ [L, (1+ε)L]`, so it contains `(x, x+L]` and exceeds it by at most `εL`;
- **`setIntegral_normSq_linWindowSum_block_le`** — integrating over the block and applying Gallagher's
  split bound on the right:

      ∫_block ‖linWindowSum a s L u‖² du
        ≤ 2(M₁·log(1 + L/Y) + M₂·2/(π²W)) + 2(εL+1)²·|block| .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**The linear short-interval mean square is now bounded by the two analytic inputs.** On a block of
ratio `1+ε` the bound is Gallagher's split — which the twisted Möbius cancellation supplies through
`M₁` — plus the elementary excess cost `(εL+1)²`. Nothing analytic is added anywhere in this
assembly; every step is an identity or an elementary inequality over the proved estimates.

What remains for the card's `(15)`–`(17)` is to sum the block estimate over the `O(log 2/log(1+ε))`
blocks covering a dyadic range, convert the integral over `u` back to the discrete sum over integer
starts (`RealWindowVariance.integral_realWindow_eq_sum` does the discrete↔real half), and choose
`ε`, `W` against `B(N)` so both error terms are `o(L²)`.

### The range estimate

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LinearRangeEstimate.lean`.

- `blockCost L Y ε M₁ M₂ W = 2(M₁·log(1+L/Y) + M₂·2/(π²W)) + 2(εL+1)²·log(1+ε)`, with
  `blockCost_nonneg`;
- **`setIntegral_normSq_linWindowSum_range_le`** — the blocks `Y(1+ε)^k < x ≤ Y(1+ε)^{k+1}` tile
  `Y < x ≤ Y(1+ε)^K`, and by induction on `K`,

      ∫_{log Y}^{log(Y(1+ε)^K)} |∑_{e^u < n ≤ e^u+L} a_n|² du ≤ K · blockCost L Y ε M₁ M₂ W .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

The induction uses only `Set.Ioc_union_Ioc_eq_Ioc` for the tiling and the monotonicity
`log(1 + L/Y(1+ε)^k) ≤ log(1 + L/Y)` — the base point of each block is at least `Y`, so every block
pays at most the cost at `Y`.

`K` blocks of ratio `1+ε` cover a range of ratio `(1+ε)^K`, so a dyadic range costs
`K ≈ log 2 / log(1+ε)` blocks and the total is

    (log 2 / log(1+ε)) · [ 2(M₁·log(1+L/Y) + M₂·2/(π²W)) + 2(εL+1)²·log(1+ε) ]
      ≈ (2 log 2 / ε)·(M₁·L/Y + M₂·2/(π²W)) + 2 log 2 · ε L² ,

the two error terms whose balance in `ε` completes the card's `(15)`–`(17)`.

### Back to the linear variable

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LinearRangeVariable.lean`.

- `linSum a s L x = ∑_{x < n ≤ x+L} a_n`, with `linWindowSum_eq_linSum`;
- `exp_image_Ioc` — `exp '' Ioc A B = Ioc (e^A) (e^B)`;
- **`integral_Ioc_eq_integral_log`** — the change of variables

      ∫_{e^A}^{e^B} F(x) dx = ∫_A^B e^u · F(e^u) du ;

- `integrableOn_normSq_expMul`, **`integral_Ioc_normSq_linSum_le`** —

      ∫_{e^A}^{e^B} |∑_{x<n≤x+L} a_n|² dx ≤ e^B · ∫_A^B |∑_{e^u<n≤e^u+L} a_n|² du .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**Why the measure-theoretic change of variables and not the interval one.** The usual substitution
lemma `intervalIntegral.integral_comp_smul_deriv` requires the integrand to be *continuous*, and the
window sum jumps at every integer. `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` imposes
no condition on the integrand at all — only injectivity and differentiability of the substitution —
so it applies directly. This is the right tool whenever the integrand is a lattice-point count.

Composing with the range estimate, the card's mean square over a dyadic range of *linear* starting
points is now bounded by the two analytic inputs, in the `dx` variable that
`RealWindowVariance.integral_realWindow_eq_sum` converts to the discrete sum over integer starts.

### The linear mean square over a range — capstone

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LinearMeanSquareCapstone.lean`.

**`integral_Ioc_normSq_linSum_range_le`** — over the starting points `Y < x ≤ Y(1+ε)^K`,

    ∫ |∑_{x < n ≤ x+L} a_n|² dx ≤ Y(1+ε)^K · K · blockCost L Y ε M₁ M₂ W ,

with `blockCost = 2(M₁·log(1+L/Y) + M₂·2/(π²W)) + 2(εL+1)²·log(1+ε)`.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**This is the card's analytic input, in linear windows, as one theorem.** `M₁` bounds
`|∑_n a_n n^{2πiw}|²` for `|w| ≤ W` and `M₂` bounds it everywhere; for `a = μ` the first is supplied
by the twisted cancellation `exists_bound_norm_sum_moebiusTwist_div` and the second is the trivial
`|s|²`. The whole passage — Gallagher's identity, the frequency split and its tail, the tiling, the
linear/multiplicative transfer with its excess, the change of variables, and the summation over
blocks — is proved unconditionally, with no analytic input beyond the twisted contour bound.

Reading off the sizes with `Z = Y(1+ε)^K ≍ 2Y` (a dyadic range, `K ≈ log 2/log(1+ε)`):

    ∫_Y^{2Y} |∑_{x<n≤x+L} μ(n)|² dx  ≪  Y·(1/ε)·(M₁·L/Y + M₂/W) + Y·ε·L² ,

so the two error terms balance at `ε ≍ (M₁/(YL) + M₂/(WL²))^{1/2}`, and both are `o(YL²)` exactly
when `M₁ = o(Y L)` and `M₂/W = o(L)` — the first being the twisted cancellation and the second the
growth of the admissible frequency range.

### The two halves meet

Added: `formal/GaloisForLFunctions/RHTower/Sieve/LogPolyMoebius.lean`.

**`logPoly_moebius_eq`** — the Dirichlet polynomial of Gallagher's identity at the Möbius
coefficients *is* the twisted Möbius sum:

    logPoly μ s w = ∑_{n ∈ s} μ(n) n^{2πiw} = ∑_{n ∈ s} moebiusTwist (−2πw) n .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

This is the join between the two halves built on this card. The quantity `M₁` that
`integral_Ioc_normSq_linSum_range_le` consumes — a bound on `|logPoly μ s w|²` for `|w| ≤ W` — is
literally the quantity `exists_bound_norm_sum_moebiusTwist_div` bounds, at `τ = −2πw`. The
correspondence is exact, not asymptotic: `n^{2πiw} = n^{-iτ}` with `τ = −2πw`, and the admissible
range `5 + 4|τ| ≤ contourParam(N+H)` becomes `|w| ≤ (contourParam(N+H) − 5)/(8π) =: W`.

So the card's analytic input in linear windows follows from the twisted contour bound with no
further analysis: substituting `M₁ = (B(N)·N)²` and `M₂ = |s|²` into the capstone gives the
short-interval mean square, and the balance in `ε` recorded above makes both error terms `o(YL²)`.

### The Möbius short-interval mean square over a range

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareRange.lean`.

- `moebiusC`, `norm_moebiusC_le_one`;
- `normSq_logPoly_moebiusC_le` — the trivial bound `|logPoly μ s w|² ≤ (#s)²`, valid at every
  frequency;
- **`integral_Ioc_normSq_moebius_range_le`** — the capstone at the Möbius coefficients:

      ∫_Y^{Y(1+ε)^K} |∑_{x < n ≤ x+L} μ(n)|² dx
        ≤ Y(1+ε)^K · K · ( 2(M₁·log(1+L/Y) + (#s)²·2/(π²W)) + 2(εL+1)²·log(1+ε) ) ,

  where the only hypothesis carrying arithmetic is

      ∀ |w| ≤ W,  ‖∑_{n ∈ s} μ(n)n^{-i(−2πw)}‖² ≤ M₁ ,

  which is exactly what `exists_bound_norm_sum_moebiusTwist_div` supplies.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**The card's analytic input is now one theorem with one arithmetic hypothesis, and that hypothesis is
proved elsewhere in this corpus.** Everything else — the trivial bound, Gallagher's reduction and all
its steps, the linear/multiplicative transfer, the change of variables, the block summation — is
elementary and proved.

### The discrete window variance as a set integral

Added: `formal/GaloisForLFunctions/RHTower/Sieve/DiscreteWindowBridge.lean`.

- `linSum_eq_realWindow` — the linear window sum of this development and the corpus's `realWindow`
  sum are the **same object** (`rfl`): both are the sum over `{n < M : x < n ≤ x + L}`;
- **`sum_normSq_Ioc_eq_setIntegral`** —

      ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} c_n|² = ∫_{(Y, Y+K]} |∑_{x < n ≤ x+L} c_n|² dx .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

That the two window notions coincide definitionally is worth recording: the corpus's
`RealWindow.realWindow` was built for the elementary variance layer, and this development arrived at
the same filter independently. No conversion is needed, only the interval-to-set integral step.

**The card's mean square is now a set integral that the Möbius range bound applies to.** With
`Y(1+ε)^K` matched to `Y + K'`, `integral_Ioc_normSq_moebius_range_le` bounds it in terms of the
frequency-restricted Möbius bound and the trivial size — completing the passage from the card's
`(15)`–`(17)` to the twisted contour argument.

### The discrete Möbius short-interval mean square — the input, assembled

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusDiscreteMeanSquare.lean`.

- `linSum_erase_eq_realWindow` — for nonnegative starting points, deleting `0` from the index set
  changes no window (`n = 0` can only enter a window with a negative start), so the index set may be
  taken positive as the logarithmic machinery requires;
- **`sum_normSq_moebius_window_le`** —

      ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} μ(n)|²
        ≤ Y(1+ε)^J · J · ( 2(M₁·log(1+L/Y) + (#s)²·2/(π²W)) + 2(εL+1)²·log(1+ε) )

  whenever `(Y:ℝ) + K = Y(1+ε)^J`, with the single arithmetic hypothesis

      ∀ |w| ≤ W,  ‖∑_{n ∈ s} μ(n)n^{-i(−2πw)}‖² ≤ M₁ .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**This is the card's `(15)`–`(17)` mean square, reduced to the twisted contour bound.** The exact
range condition `(Y:ℝ) + K = Y(1+ε)^J` is no restriction: given `Y, K, J` it determines
`ε = ((Y+K)/Y)^{1/J} − 1`, and `J` is free.

The chain, entirely within this corpus and entirely unconditional:

    discrete mean square over integer starts        (DiscreteWindowBridge)
      = a set integral of the linear window sum
      = an integral in the logarithmic variable     (LinearRangeVariable)
      ≤ blocks × block cost                         (LinearBlockEstimate, LinearRangeEstimate)
      ≤ Gallagher's split                           (GallagherLemma, GallagherSplit, GallagherTail)
      = a bound on the twisted Möbius polynomial    (LogPolyMoebius)
      ← the twisted contour argument                (MoebiusTwist* layer)

No step assumes an external analytic result; the only analytic input anywhere is the zero-free region
already owned by the corpus.

### Discharging the frequency hypothesis

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusFrequencyBound.lean`.

- `sum_moebiusTwist_erase` — deleting `0` from the index set changes nothing, the twisted coefficient
  vanishing there;
- `admissible_of_abs_le` — the two frequency ranges match under `τ = −2πw`: since `|τ| = 2π|w|`,
  the contour's condition `5 + 4|τ| ≤ C` is `5 + 8π|w| ≤ C`, so `W = (C − 5)/(8π)` is admissible;
- **`normSq_sum_moebiusTwist_le`** — hence, from the twisted contour bound
  `‖∑_{n<M} μ(n)n^{-iτ}‖/N ≤ B` valid for `5 + 4|τ| ≤ C`,

      ∀ |w| ≤ W,  ‖∑_{n ∈ (range M).erase 0} μ(n)n^{-i(−2πw)}‖² ≤ (B·N)² ,

  which is exactly the hypothesis `sum_normSq_moebius_window_le` requires, with `M₁ = (B·N)²`.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**The card's analytic input is closed.** `exists_bound_norm_sum_moebiusTwist_div` supplies `B` with
`B → 0`, at `C = contourParam(N + smoothWidth N)` — so `W = (contourParam − 5)/(8π)` grows faster than
any power of `log N`, and `M₁ = (B(N)·N)² = o(N²)`. Substituted into the mean-square bound, the two
error terms are as recorded above, and the `ε`-balance makes both `o(L²)` per start.

### The mean square from the twisted contour bound alone

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareFinal.lean`.

- `blockCost_mono_right` — the block cost is monotone in the global bound;
- **`sum_normSq_moebius_window_le_of_twist`** —

      ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} μ(n)|²
        ≤ Y(1+ε)^J · J · ( 2((BN)²·log(1+L/Y) + M²·2/(π²W)) + 2(εL+1)²·log(1+ε) )

  whose **only** hypotheses are the geometry (`Y+K = Y(1+ε)^J`, `8πW + 5 ≤ C`, positivity) and the
  twisted contour bound in its own statement:

      ∀ τ,  5 + 4|τ| ≤ C  →  ‖∑_{n < M} μ(n)n^{-iτ}‖ / N ≤ B .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**This closes the route.** `exists_bound_norm_sum_moebiusTwist_div` provides exactly that hypothesis
with `B → 0` and `C = contourParam(N + smoothWidth N)`; substituting gives the card's `(15)`–`(17)`
mean square with both error terms `o(L²)` at the recorded `ε`-balance.

Status of the card's external dependency: `(15)`–`(17)` were cited to Menon's 2026 short-interval
mean-square theorem. That citation is no longer needed for this route — the estimate is derived here
from the corpus's own zero-free region, through the twisted contour argument and Gallagher's
reduction, with no external analytic input at any step.

### The mean square, unconditionally

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareUnconditional.lean`.

**`exists_sum_normSq_moebius_window_le`** — there is a `B` with `B → 0` such that for all large `N`
and every admissible geometry,

    ∑_{k < K} |∑_{Y+k < n ≤ Y+k+L} μ(n)|²
      ≤ Y(1+ε)^J · J · ( 2((B(N)·N)²·log(1+L/Y) + (⌊N⌋+1)²·2/(π²W)) + 2(εL+1)²·log(1+ε) ) ,

the admissible band being `8πW + 5 ≤ contourParam(N + smoothWidth N)`.

**No analytic hypothesis remains anywhere in the statement.** Unconditional
(`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

This is the card's `(15)`–`(17)` input, derived rather than cited. The whole derivation rests on one
analytic fact — the zero-free region for `ζ`, which the corpus already owned and which is what makes
`B → 0` — and on nothing else external.

### The mean square in the real form step 1 consumes

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareRealForm.lean`.

`SquarefreeExceptional.card_le_good_add_explicit` takes its mean-square input as a **real** sum
`∑_{t ∈ S} (∑_{t < n ≤ t+L} μ(n))² ≤ V`, while the development above produces `∑ ‖∑ μ(n)‖²` over
complex coefficients. The two agree, the Möbius sum being real:

- `normSq_moebiusC_eq_sq_real` — `‖∑_{n ∈ T} μ(n)‖² = (∑_{n ∈ T} μ(n))²`;
- `sum_sq_real_moebius_Ico_eq` — reindexing `t = Y + k` turns the range sum into a sum over
  `Ico Y (Y+K)`, which is the shape of `S`;
- **`exists_sum_sq_real_moebius_Ico_le`** — hence, unconditionally, with `B → 0`:

      ∑_{t ∈ Ico Y (Y+K)} ( ∑_{t < n ≤ t+L} μ(n) )²
        ≤ Y(1+ε)^J · J · ( 2((B(N)N)²·log(1+L/Y) + (⌊N⌋+1)²·2/(π²W)) + 2(εL+1)²·log(1+ε) ) .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**This is `hms` of `card_le_good_add_explicit`, supplied.** Step 1 of the Hall-law argument had
exactly one hypothesis left — the mean-square bound `V` — after the truncation defect was discharged
earlier on this card. That hypothesis is now a theorem of this corpus, so step 1 is unconditional in
the parameter regime where the right-hand side is small enough.

### Step 1 of the Hall-law argument, unconditionally

Added: `formal/GaloisForLFunctions/RHTower/Sieve/Step1Moebius.lean`.

**`exists_card_le_good_add_moebius`** — there is a `Bd → 0` such that for all large `N` and every
admissible geometry, `card_le_good_add_meanSquare_explicit` holds with its mean-square numerator
supplied explicitly:

    #{starts} ≤ #{good starts}
      + Y(1+ε)^J·J·blockCost(L, Y, ε, (Bd(N)N)², (⌊N⌋+1)², W) / (DL/8)²
      + L((Y+K+L−Y)/R + Md) / θ .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**Both hypotheses of step 1 are now theorems of this corpus.** `hdef` (the averaged truncation
defect) was discharged earlier in this session by `Step1Explicit`; `hms` (the mean square) is
discharged here. Step 1 carries no analytic assumption.

Audit note on a near-miss: `moebiusC` and `norm_moebiusC_le_one` were **already defined** in
`Sieve/MoebiusEulerDamping.lean`, and this development briefly duplicated them. The duplicate only
surfaced when a module imported both cones — a collision scan run from the wrong directory had
silently reported nothing. The duplicates are removed and the corpus definitions are used
throughout; the lesson is that a name scan whose `grep` target does not resolve looks identical to a
clean scan.

### Umbrella audit

`lake build GaloisForLFunctions.RHTower` completes successfully (16736 jobs) with every module of
this development wired in. That is the authoritative duplicate-name check: a name clash between two
modules in the same namespace only surfaces when both cones are imported together, which the umbrella
does.

Card state after this work:

* `(15)`–`(18)` — **derived in-corpus**, no longer cited. Chain: zero-free region → twisted contour
  bound (`MoebiusTwist*`) → frequency-uniform Möbius cancellation → Gallagher's reduction
  (`LogWindowKernel`, `TriangularKernel`, `TriangularInversion`, `TriangularIntegralForm`,
  `GallagherLemma`, `GallagherSplit`, `GallagherTail`, `GallagherRange`) → linear windows
  (`LogWindowMultiplicative`, `LogWindowTiling`, `LinearVsMultiplicativeWindow`,
  `LinearWindowMeasurable`, `LinearRangeVariable`) → block and range summation
  (`LinearBlockEstimate`, `LinearRangeEstimate`, `LinearMeanSquareCapstone`) → Möbius instantiation
  (`LogPolyMoebius`, `MoebiusMeanSquareRange`, `DiscreteWindowBridge`, `MoebiusDiscreteMeanSquare`,
  `MoebiusFrequencyBound`, `MoebiusMeanSquareFinal`, `MoebiusMeanSquareUnconditional`,
  `MoebiusMeanSquareRealForm`) → step 1 (`Step1Explicit`, `Step1Moebius`).
* `(32)`/`(34)` — Shiu's bound, with the corpus's weaker unconditional substitute sufficing.
* `(35)`/`(36)` — proved.
* Everything else on the card — proved.

What is left is numerical: choosing `ε`, `W`, `J` in the card's regime and reading off the `o(·)`
statements. No step of the argument now depends on a result outside this corpus.

### The block cost without logarithms

Added: `formal/GaloisForLFunctions/RHTower/Sieve/BlockCostBound.lean`.

**`blockCost_le`** — both logarithms are bounded by their arguments (`log(1+x) ≤ x`), so

    blockCost L Y ε M₁ M₂ W ≤ 2M₁·(L/Y) + 4M₂/(π²W) + 2(εL+1)²·ε .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

In this form the three contributions are visible as what they are:

* `2M₁·(L/Y)` — the **cancellation** term, carrying `M₁ = (B(N)N)²` with `B → 0`;
* `4M₂/(π²W)` — the **frequency-tail** term, carrying the trivial size against the admissible band
  `W ≍ contourParam`, which grows faster than any power of `log N`;
* `2(εL+1)²·ε` — the **excess** term, the price of replacing a linear window by a multiplicative one.

The first two decrease in `Y` and `W`, the third increases in `ε`, and the numerical step is the
balance between them: with `Y ≍ N`, the cancellation term is `2B(N)²N L` and the tail term is
`O(N²/W)`, so both are `o(L²)` per start once `B(N)²N/L → 0` and `N²/(W L²) → 0`, while the excess
term is `o(L²)` for `ε → 0`.

### Counting the blocks

Added: `formal/GaloisForLFunctions/RHTower/Sieve/BlockCount.lean`.

- `log_one_add_ge` — `ε/(1+ε) ≤ log(1+ε)`;
- **`blocks_eq_log`** — the geometry determines the block count exactly:
  `J·log(1+ε) = log(1 + K/Y)`;
- **`blocks_le`** — hence `J ≤ log(1 + K/Y)·(1+ε)/ε`.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

Covering a range of ratio `1 + K/Y` costs `O(1/ε)` blocks. Combined with `blockCost_le`, the total
bound of `sum_normSq_moebius_window_le_of_twist` is now explicit in the parameters alone:

    ∑_{t ∈ Ico Y (Y+K)} ( ∑_{t<n≤t+L} μ(n) )²
      ≤ (Y+K) · log(1+K/Y)·(1+ε)/ε · ( 2M₁·(L/Y) + 4M₂/(π²W) + 2(εL+1)²·ε ) .

With `Y ≍ K ≍ N`, `M₁ = (B(N)N)²`, `M₂ ≍ N²`: the three terms are `O(N·B(N)²N L/(εN)) = O(B²N²L/ε)`,
`O(N·N²/(εW))` and `O(N·ε²L²)` — all `o(N L²)` once `B(N)²N/(εL) → 0`, `N²/(εWL²) → 0` and `ε → 0`,
which the growth of `contourParam` and `B → 0` permit.

### The mean square, fully explicit

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareExplicit.lean`.

**`exists_sum_sq_real_moebius_explicit`** — substituting the block count and the logarithm-free block
cost, there is a `B → 0` with, for all large `N` and every admissible geometry,

    ∑_{t ∈ [Y, Y+K)} ( ∑_{t<n≤t+L} μ(n) )²
      ≤ (Y+K) · log(1+K/Y)(1+ε)/ε
          · ( 2(B(N)N)²·(L/Y) + 4(⌊N⌋+1)²/(π²W) + 2(εL+1)²·ε ) .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**No logarithm of a large quantity, no implicit constant and no analytic hypothesis remains.** The
right-hand side is an explicit elementary function of `Y, K, L, ε, W, N` and the single quantity
`B(N)`, which tends to zero by the twisted contour argument. Choosing the parameters is now the whole
of the remaining work, and the three terms to balance are named on the card above.

### The normalized bound on a dyadic range

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusMeanSquareNormalized.lean`.

- `normalized_bound_dyadic` — the algebra at `K = Y` (range ratio `2`), dividing by the trivial size
  `Y·L²`;
- **`exists_normalized_mean_square_le`** — hence, unconditionally with `B → 0`,

      ( ∑_{t ∈ [Y, 2Y)} ( ∑_{t<n≤t+L} μ(n) )² ) / (Y L²)
        ≤ 2 log 2 · (1+ε)/ε
            · ( 2(B(N)N)²/(Y L) + 4(⌊N⌋+1)²/(π²W L²) + 2(εL+1)²·ε/L² ) .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

**The card's `(15)` is this quantity tending to zero**, and the right-hand side makes the three
requirements explicit, each already divided by the trivial size:

* `(B(N)N)²/(ε Y L) → 0` — the cancellation term; with `Y ≍ N` this is `B(N)²N/(εL) → 0`;
* `N²/(ε W L²) → 0` — the frequency tail; `W ≍ contourParam` grows faster than any power of `log N`;
* `ε → 0` with `ε³L² → 0` — the excess term.

All three are simultaneously satisfiable in the card's regime, and each is a statement about
explicitly proved quantities.

### When the normalized bound tends to zero

Added: `formal/GaloisForLFunctions/RHTower/Sieve/NormalizedBoundLimit.lean`.

- **`tendsto_normalizedBound`** — since `(1+ε)/ε · F = F/ε + F`, the bound `2 log 2 ·(1+ε)/ε· F`
  tends to zero exactly when both `F/ε` and `F` do;
- **`tendsto_normalizedBound_of_three`** — applied to the sum of the three error terms, so the
  hypotheses are the six limits (each term with and without the `1/ε`).

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

Composed with `exists_normalized_mean_square_le`, this closes the numerical step: the card's `(15)`
holds for any parameter schedule `ε(N), W(N), L(N), Y(N)` satisfying

    (B(N)N)²/(ε Y L) → 0 ,    N²/(ε W L²) → 0 ,    (εL+1)²/L² → 0

(the last being `ε → 0` together with `1/L → 0`), and the admissibility `8πW + 5 ≤ contourParam`.
Every quantity in those three conditions is proved: `B → 0` is the twisted contour bound, and
`contourParam(x) = ⌈exp((log x)^{1/10})⌉` gives the room for `W`.

### What the parameter analysis actually shows — and the one thing still missing

Working through the three conditions of `tendsto_normalizedBound_of_three` against the proved
quantities gives a sharper picture than "only arithmetic remains", and it should be recorded
plainly.

Write `Y ≍ N` and take `W` as large as admissibility allows, `W ≍ contourParam(N)`. The conditions
are

1. `(B(N)N)²/(ε Y L) ≍ B(N)²·N/(ε L) → 0` ;
2. `N²/(ε W L²) → 0` ;
3. `ε → 0` and `1/L → 0` .

Conditions (1) and (2) are both **lower** bounds on `ε` — `ε ≫ B²N/L` and `ε ≫ N²/(WL²)` — while (3)
is an upper bound. So a schedule exists iff `B²N/L → 0` and `N²/(WL²) → 0`, and then any `ε` between
them works, e.g. `ε = max(B²N/L, N²/(WL²))^{1/2}`.

* For **long windows**, `L ≍ N`: condition (1) becomes `B(N)² → 0`, which holds since `B → 0`, and
  condition (2) becomes `1/W → 0`, which holds since `contourParam → ∞`. **A schedule exists and the
  mean square is `o(N L²)`.**
* For **short windows**, `L = N^θ` with `θ < 1`: condition (1) becomes `B(N)²N^{1−θ} → 0`, which does
  **not** follow from `B → 0` alone. It needs a *rate*.

`exists_bound_norm_sum_moebiusTwist_div` provides only `B → 0`, with no rate — as does the corpus's
untwisted `MoebiusSharpLittleO`. So the derivation established here gives the card's `(15)` for
windows comparable to the range, and short windows need one further construction: **an explicit rate
for `B`**.

That rate is extractable rather than new mathematics: `MoebiusTwistSaving` already carries the saving
`(N+H)·exp(−c₀·log(N+H)/(16 log⁹K))` with every constant explicit, and
`MoebiusTwistMajorantRatio`/`MoebiusTwistSharpLittleO` discard it into an `o(1)` only at the last
step. Re-running those two modules keeping the exponent would give `B(N) ≪ exp(−c·(log N)^{1/10})`,
which is far more than enough for every `θ < 1`.

This is the honest state: the reduction is complete and unconditional, the long-window case is done,
and the short-window case is one explicit-constant bookkeeping step away.

### Toward the rate — half the exponent absorbs the majorant

Added: `formal/GaloisForLFunctions/RHTower/Sieve/CoeffMajorantQuantitative.lean`.

**`eventually_coeffMajorant_mul_exp_le`** — for every `κ > 0`,

    coeffMajorant C C' M₀ a t · exp(−κt) ≤ exp(−κt/2)   for all large `t`.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

The corpus's `tendsto_coeffMajorant_mul_exp_neg` is used only qualitatively — it feeds a `squeeze` and
the exponent is thrown away. Splitting `exp(−κt) = exp(−κt/2)·exp(−κt/2)` and applying that limit at
`κ/2` shows the polynomial majorant is eventually below `exp(κt/2)`, so half the exponent survives.

This is the enabling step for the rate identified in the previous section: with
`t = (log(N+H))^{1/10}` and `κ = c₀/8192`, it converts the contour bound into

    ‖∑_{n ≤ N} μ(n)n^{-iτ}‖ ≪ N·exp(−c·(log N)^{1/10}) ,

which is `B(N) ≪ exp(−c(log N)^{1/10})` — far more than the `B(N)²N^{1−θ} → 0` that short windows
need. What remains is to thread it through `MoebiusTwistMajorantRatio` and
`MoebiusTwistSharpLittleO` in place of their `o(1)` conclusions.

### The quadratic beats the linear, explicitly

Added: `formal/GaloisForLFunctions/RHTower/Sieve/ExpQuadraticQuantitative.lean`.

- `two_mul_le_half_sq` — for `v ≥ 4/κ`, `2v ≤ κv²/2`;
- **`exp_two_sub_sq_le`** — hence `exp(2v − κv²) ≤ exp(−κv²/2)` past that explicit threshold;
- `eventually_exp_two_sub_sq_le` — the eventual form.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

`ExpQuadraticDecay` proves `exp(2v − κv²) → 0` and uses it only qualitatively. The comparison is in
fact explicit, and with `v = (log N)^{1/20}`, `κ = c₀/8192` this is the contour saving surviving the
price of narrow smoothing **with a rate**: `exp(−c₀(log N)^{1/10}/16384)`.

Together with `eventually_coeffMajorant_mul_exp_le` (half the exponent absorbs the majorant), the two
places where the corpus discards its exponent now both have quantitative replacements.

Audit note: while preparing this I started to write a monotonicity lemma for `coeffMajorant` in its
coefficient arguments — it already exists as `CoeffMajorantScale.coeffMajorant_mono_const`, alongside
`CoeffMajorantMono.coeffMajorant_mono_t` and `CoeffMajorantProd.coeffMajorant_le_prod`, and
`CoeffRatioBound` already assembles all three. The duplicate was caught by the editor refusing to
overwrite an existing file of the same name, not by a name scan.

### The ratio-form majorant, with a rate

Added: `formal/GaloisForLFunctions/RHTower/Sieve/PolyExpQuantitative.lean`.

**`eventually_poly_exp_two_sub_sq_le`** — for `κ > 0` and all large `v`,

    (1 + a(v²)⁹)(b + cv²)·exp(2v)·exp(−κv²) ≤ exp(−κv²/2) .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

`CoeffRatioBound.coeffMajorant_ratio_le` reduces the majorant at the chosen smoothing width to
exactly that shape, and `ExpQuadraticDecay` shows it tends to zero — qualitatively. Splitting the
exponential and applying the limit at `κ/2` keeps half the exponent.

**All three discard points now have quantitative replacements:**

* `eventually_coeffMajorant_mul_exp_le` — the diagonal majorant;
* `exp_two_sub_sq_le` — the linear-versus-quadratic comparison, with the explicit threshold `4/κ`;
* `eventually_poly_exp_two_sub_sq_le` — the ratio-form majorant.

Composing them with `coeffMajorant_ratio_le` and the twisted contour bound gives
`B(N) ≪ exp(−c(log N)^{1/10})`, which is the rate the short-window case of `(15)` needs. That
composition — rerunning `MoebiusTwistMajorantRatio` and `MoebiusTwistSharpLittleO` against these
three in place of their `squeeze`s — is what remains.

### The majorant at the chosen width, with a rate

Added: `formal/GaloisForLFunctions/RHTower/Sieve/CoeffRatioQuantitative.lean`.

**`eventually_coeffMajorant_ratio_le_exp`** — for all large `v`, whenever `v² ≤ t ≤ 2v²` and
`L + 2 ≤ 3e^v` (the relations the chosen smoothing width satisfies),

    coeffMajorant (C(L+2)²) (C'(L+2)) M₀ a t · exp(−κt) ≤ exp(−κv²/2) .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

This composes `CoeffRatioBound.coeffMajorant_ratio_le` — which already reduces the ratio-form
majorant to the `(1+a(v²)⁹)(b+cv²)exp(2v)exp(−κv²)` shape with explicit `b`, `c` — with the
quantitative decay of the previous section. With `v = (log N)^{1/20}` and `t = (log(N+H))^{1/10}` the
right-hand side is `exp(−κ(log N)^{1/10}/2)`.

**The rate is now available where the contour argument needs it.** What is left is to use this in
place of the `squeeze_zero'` inside `MoebiusTwistMajorantRatio`/`MoebiusTwistSharpLittleO`, which
turns their `B → 0` into `B(N) ≪ exp(−c(log N)^{1/10})`.

### The majorant at the chosen width, as a rate in `N`

Added: `formal/GaloisForLFunctions/RHTower/Sieve/CoeffRatioRate.lean`.

**`eventually_coeffMajorant_ratio_rate`** — at the contour argument's own smoothing width
`H = N/exp((log N)^{1/20})`, for all large `N`,

    coeffMajorant (C(smoothRatio+2)²) (C'(smoothRatio+2)) M₀ a t · exp(−κt)
      ≤ exp(−κ(log N)^{1/10}/2) ,   t = (log(N+H))^{1/10} .

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

`CoeffRatioLimit.tendsto_coeffMajorant_ratio` proves the same expression tends to zero, using three
geometric facts — `v² ≤ t` (`LogComparison.sq_le_logRpow`), `t ≤ 2v²`
(`LogComparison.logRpow_le_two_sq`) and `smoothRatio + 2 ≤ 3e^v` — all of which are exported. Feeding
them to the quantitative bound instead of to a `squeeze_zero'` turns the `o(1)` into a rate, with no
new estimate anywhere.

**The rate now exists at the width the contour argument actually uses.** Substituting it in
`MoebiusTwistMajorantRatio` in place of `tendsto_coeffMajorant_ratio` yields

    ‖∑_{n ≤ N} μ(n)n^{-iτ}‖ ≪ N·exp(−c(log N)^{1/10})   uniformly over the admissible twists,

i.e. `B(N) ≪ exp(−c(log N)^{1/10})`, which covers the short-window case of `(15)` for every window
length `L = N^θ`, `θ < 1`.

### The twisted smoothed sum, with a rate

Added: `formal/GaloisForLFunctions/RHTower/Sieve/MoebiusTwistRate.lean`.

**`exists_norm_tsum_moebiusTwist_smoothWeight_rate`** — for all large `N` and every admissible twist,

    ‖2π·∑' μ(n)n^{-iτ}·w(n)‖ ≤ 2(N + H + 1)·exp(−(c₀/8192)·(log N)^{1/10}/2) ,

at the contour argument's own smoothing width `H = N/exp((log N)^{1/20})`.

Unconditional (`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.RHTower`.

`MoebiusTwistMajorantRatio` already proves the bound with the majorant in place; substituting
`CoeffRatioRate.eventually_coeffMajorant_ratio_rate` for the limit that
`MoebiusTwistSharpLittleO` feeds it to replaces the `o(1)` by

    exp(−c(log N)^{1/10}) ,   c = c₀/16384 .

**This is the rate.** Comparing the sharp and smoothed sums (`SmoothVsSharp`, already generalised to
unimodular coefficients) then gives

    ‖∑_{n ≤ N} μ(n)n^{-iτ}‖ ≪ N·exp(−c(log N)^{1/10}) + smoothWidth N + 1 ,

and `smoothWidth N = N/exp((log N)^{1/20})` is itself of that shape, so
`B(N) ≪ exp(−c'(log N)^{1/20})`. Since `B(N)²N^{1−θ} → 0` for every `θ < 1`, the short-window
restriction recorded above is removed: `(15)` holds for windows of every length `L = N^θ`.

### The sharp twisted sum, with a rate — `Sieve/MoebiusTwistSharpRate.lean`

Comparing the smoothed sum with the sharp one costs `H + 1`, so the rate of `MoebiusTwistRate`
transfers to the sharp sum:

- **`exists_norm_sum_moebiusTwist_rate`** :

      ‖∑_{n ≤ N} μ(n)n^{−iτ}‖ ≤ 3N·exp(−κ(log N)^{1/10}/2)/π + N·exp(−(log N)^{1/20}) + 1 ,

  `κ = zeroFreeConst/8192`, uniformly over every twist the contour admits.

Both terms are `N` times an explicit saving, so this is the quantitative form of
`MoebiusTwistSharpLittleO.exists_bound_norm_sum_moebiusTwist_div`: the admissible bound function is
`B(N) ≪ exp(−(log N)^{1/20})`. Built, wired, axiom-clean.

### Window range of the derived mean square — correction

An earlier section of this card claimed that the derived mean square supersedes `(15)`. It does not,
and the claim is withdrawn. What is derived is a genuine unconditional theorem, but in a different
parameter range, and the arithmetic is worth recording exactly.

The normalized bound `MoebiusMeanSquareNormalized.exists_normalized_mean_square_le` reads

    (1/(YL²))·∑_{Y ≤ t < 2Y} (∑_{t<n≤t+L} μ(n))²
      ≤ 2log2·((1+ε)/ε)·( 2(B(N)N)²/(YL) + 4M²/(π²WL²) + 2(εL+1)²ε/L² ) ,

with `M ≍ N`, `Y ≍ N`, and the frequency range `W` constrained by

    8πW + 5 ≤ contourParam(N + smoothWidth N) = ⌈exp((log(N+H))^{1/10})⌉ .

So `W ≤ exp((log N)^{1/10})` up to a constant, and this is forced: `W` is the range over which the
*pointwise* twisted bound is available, and the twisted contour argument has that bound exactly as
far as the zero-free region reaches.

Reading the three terms:

1. **cancellation** `2(B(N)N)²/(YL) ≍ B(N)²N/L`, harmless once `L ≫ N·exp(−2(log N)^{1/20})`;
2. **frequency tail** `4M²/(π²WL²) ≍ N²/(WL²)`, which needs `L ≫ N/√W = N·exp(−(log N)^{1/10}/2)`;
3. **excess** `2(εL+1)²ε/L² ≍ ε³`, harmless.

Term 2 is the binding constraint, and it does not improve much under a better tail estimate: with the
Dirichlet mean-value theorem in place of the trivial `|S(τ)|² ≤ M²`, the dyadic tail is
`≪ M/W + M²/W²` instead of `M²/W`, and the requirement becomes `L ≫ N/W = N·exp(−(log N)^{1/10})` —
the same shape.

Hence the derived estimate is a **long-window** Möbius variance bound,

    L ≥ N·exp(−c(log N)^{1/10}) ,

unconditional and with explicit constants, resting only on the classical zero-free region.

This card applies `(15)` at `A_k ≍ √X/2^k` and `L_k = ⌊h/2^{k+2}⌋`, so uniformly in `k`

    L_k/A_k ≍ h/√X = X^{−1/2+o(1)} ,

with the schedule `(6)` giving `log L_k ≍ log h = log X/log log X ≍ 2·log A_k/log log A_k`, i.e.
`L_k = A_k^{2/log log A_k}`. That is `A_k^{o(1)}`, incomparably shorter than
`A_k·exp(−c(log A_k)^{1/10})`. The derived estimate is therefore vacuous at this card's parameters,
and `(15)`–`(18)` continue to rest on Matomäki–Radziwiłł 2016 Theorem 2 / Menon 2026.

The obstruction is structural, not an artefact of the assembly. Reaching `L = N^{o(1)}` through
Gallagher's reduction requires control of the Dirichlet polynomial over a frequency range
`W ≳ N/L = N^{1−o(1)}`, and no pointwise bound is available there at any zero-free region: the range
is far beyond where contour shifting says anything. Matomäki–Radziwiłł replace the pointwise bound by
a *mean-square* bound over the whole range, obtained by multiplicative factorization and Halász,
which is why that theorem is genuinely deeper than the zero-free region. The corpus's route to it is
the Ramaré/factorization/Halász layer (`Sieve/RamareWeight.lean` and the modules named in
`MR reduction`), not the contour layer built above.

What the contour layer does buy, and keeps:

- an unconditional, frequency-uniform cancellation bound for `∑_{n ≤ N} μ(n)n^{−iτ}` with an explicit
  saving `exp(−c(log N)^{1/10})` (`MoebiusTwistSharpRate`);
- Gallagher's reduction in exact form, with no hypotheses (`GallagherLemma` and the linear-window
  passage), which is the same reduction the Matomäki–Radziwiłł argument uses;
- the block/range summation and the passage to the discrete real-form variance, which are parametric
  in the mean-square input and so accept the Matomäki–Radziwiłł bound unchanged when it arrives.

Only the *input* to Gallagher's frequency integral has to be replaced. That is the open work.

### Toward the real input — the sixth-moment large-values estimate

The correction above identifies the single thing that has to be replaced: the *pointwise* bound on
the Dirichlet polynomial over the frequency range, which the zero-free region cannot supply beyond
`|τ| ≤ exp((log N)^{1/10})`. The substitute is a *large-values* estimate, and the standard way to
sharpen one is to raise the polynomial to a power before applying a mean-value theorem. Three new
modules do that, using the corpus's own mean-value theorem unchanged.

- `Sieve/DirichletCubeConvolution.lean`
  - `cubeIdx`, `convCube` — the threefold Dirichlet convolution, indexed by `Fin (N³)`;
  - `exp_phase_cubeIdx` — the phases multiply: `n^{it}m^{it}k^{it} = (nmk)^{it}`;
  - **`dirPoly_convCube`** : `F(t)³ = ∑_{j ≤ N³} b_j j^{it}`, i.e. the cube of a Dirichlet
    polynomial is a Dirichlet polynomial with the convolved coefficients.

- `Sieve/DirichletCubeCoefficients.lean`
  - `cubeFibre` — the triples with a given product;
  - `cubeFibre_card_le_sq` : `#fibre ≤ N²`, since the first two factors determine the third;
  - **`sum_normSq_convCube_le`** : `∑_j |b_j|² ≤ D·(∑_n |a_n|²)³` for any `D` bounding the fibre
    size — Cauchy–Schwarz on each fibre, then fibrewise summation.

- `Sieve/DirichletSixthMoment.lean`
  - **`sixthMoment_dirPoly`** :

        ∑_r |F(λ_r)|⁶ ≤ (T + 4N³(1+log N³))(δ^{-1} + 2log N³) · D · (∑_n |a_n|²)³

    at frequencies `δ`-separated inside `[δ/2, T−δ/2]`;
  - **`card_largeValues_sixth_le`** : the same divided by `V⁶` — a cap on how many separated
    frequencies can have `|F| ≥ V`.

The point of the exponent is that the spread `T` is now divided by `V⁶` rather than `V²`. In the
second-moment form the `T`-term is useless once `V` is anywhere near the trivial size `∑|a_n|`;
in the sixth-power form it is not, and that is the mechanism by which a large-values argument covers
a frequency range far beyond any zero-free region.

Built, wired into `GaloisForLFunctions/RHTower.lean`, axiom-clean (four theorems, every one
`[propext, Classical.choice, Quot.sound]`).

What this does **not** yet do: the fibre bound `D` is supplied as a hypothesis, and the only
unconditional instance proved here is the crude `D ≤ N²`, which is too lossy for the application.
The useful instance is `D ≤ max_{j ≤ N³} d₃(j) = N^{o(1)}`, a divisor-function bound; that is the
next brick.

### The sixth-moment estimate, unconditionally — `Sieve/CubeFibreDivisorBound.lean`, `Sieve/DirichletSixthMomentDivisor.lean`, `Sieve/DirichletMeasureSixthMoment.lean`

The hypothesis `D` left open by the previous section is now discharged. The corpus already owned the
divisor bound (`RHTower/DivisorBound.card_divisors_le_const_mul_rpow` : `d(n) ≤ C_ε n^ε`, proved from
Bernoulli's inequality per prime), and a triple `(n,m,k)` with `nmk = j` is determined by the pair
`(n, nm)`, both of which divide `j`.

- **`cubeFibre_card_le_divisors_sq`** : `#fibre(j) ≤ d(j)²` — the injection `(n,m,k) ↦ (n, nm)` into
  pairs of divisors;
- **`exists_cubeFibre_card_le_rpow`** : for every `ε > 0` there is `C > 0` with
  `#fibre(j) ≤ C·N^ε` for every `N ≥ 1` and every fibre of `[1,N]³ → [1,N³]`. The exponent
  bookkeeping is `d(j)² ≤ (C₀ (N³)^{ε/6})² = C₀² N^ε`.

Substituting it removes the last hypothesis from the sixth-moment layer:

- **`exists_sixthMoment_dirPoly_rpow`** :

      ∑_r |F(λ_r)|⁶ ≤ (T + 4N³(1+log N³))(δ^{-1} + 2log N³) · C N^ε · (∑_n |a_n|²)³

  for every Dirichlet polynomial of length `N` and every `δ`-separated family in `[δ/2, T−δ/2]`;
- **`exists_card_largeValues_sixth_rpow`** : the same divided by `V⁶`;
- **`volume_largeValues_sixth_le`**, **`exists_volume_largeValues_sixth_rpow`** : the measure form,

      V⁶ · |{t ∈ (0,T] : |F(t)| ≥ V}| ≤ (T + 4N³(1+log N³)) · C N^ε · (∑_n |a_n|²)³ ,

  obtained by running `volume_largeValues_le` on the cube — the level set is literally the same set,
  since `‖F³‖ = ‖F‖³` (`largeValues_cube_setOf`).

Built, wired, axiom-clean (six theorems, every one `[propext, Classical.choice, Quot.sound]`).

This is the first estimate in the corpus that says something nontrivial about a Dirichlet polynomial
over a frequency range **wider than any zero-free region**, and it is exactly the object the previous
section identified as the missing input: the pointwise bound is replaced by a bound on the measure of
the set where the polynomial is large. What remains between here and `(15)` is the passage from that
measure bound to a bound on the weighted frequency integral of `|F|²` that Gallagher's identity
produces — a dyadic decomposition over the level `V`, convergent because the count decays like
`V^{-6}` and the integrand grows like `V²`.

### The sixth moment as an integral — `Sieve/DirichletIntegralSixthMoment.lean`

The form a bilinear argument actually consumes: no spacing, no level set, no test points.

- **`integral_sixth_dirPoly_le`**, **`exists_integral_sixth_dirPoly_rpow`** :

      ∫_0^T |F(t)|⁶ dt ≤ (T + 4N³(1+log N³)) · C_ε N^ε · (∑_n |a_n|²)³ .

Obtained by feeding the cube into the corpus's own `DirichletIntegralBound.integral_normSq_dirPoly_le`
(which was already stated for the interval integral and needs no positivity hypothesis on `T`).

Note the shape: `∑|a_n|²` enters **cubed**. The estimate is therefore strong exactly when the
coefficient vector is spread out — which is what a multiplicative factorization of the polynomial
produces, and is the reason the Matomäki–Radziwiłł argument factorizes before estimating. Applied to
an unfactored polynomial with `∑|a_n|² ≍ N` it gives nothing beyond the second moment; applied to a
prime-supported factor with `∑|a_p|² ≍ ∑_{p ∼ P} 1/p ≍ 1/log P` it is a genuine saving.

Built, wired, axiom-clean.

### Combining the two estimates — `Sieve/DirichletProductSplit.lean`

A large-values estimate improves a mean square only in combination with a threshold argument, and
that combination is now a theorem.

- **`integral_normSq_mul_split`** : for two Dirichlet polynomials and any threshold `V`,

      ∫_0^T |P|²|Q|² ≤ V²∫_0^T|P|² + (sup|P|)²(sup|Q|)²·|{t ∈ (0,T] : |Q(t)| ≥ V}| .

  Below the threshold `Q` is replaced by `V`; above it both factors are replaced by their trivial
  sizes and only the measure of the exceptional set survives. Proved by splitting the domain along
  the measurable set `{|Q| ≥ V}` (`integral_inter_add_sdiff`), with the discarded piece of the
  comparison integral bounded below by zero.
- **`integral_normSq_mul_le_of_sixth`**, **`integral_normSq_mul_le_sixth`** : the same with the
  exceptional set measured by the sixth moment, in the division-free form

      V⁶∫_0^T|P|²|Q|² ≤ V⁸∫_0^T|P|² + (sup|P|)²(sup|Q|)²·(T + 4M³(1+log M³))·D·(∑_n|b_n|²)³ .

Built, wired, axiom-clean (three theorems).

Optimising `V` in the second form gives `∫|PQ|² ≍ X^{3/4}Y^{1/4}` with `X = ∫|P|²` and `Y` the
exceptional term, against the trivial `(sup|Q|)²X`. The saving is a genuine power whenever
`(sup|P|)²D(∑|b_n|²)³ < (∑|a_n|²)(sup|Q|)⁶`, which is what a prime-supported second factor over a
dyadic range supplies — `∑_p 1/p² ≪ 1/(P log P)` against `(∑_p 1/p)⁶ ≍ (log P)^{-6}`. This is the
first place in the chain where the estimate beats the trivial bound *without* using the zero-free
region, and it is the reason the Matomäki–Radziwiłł argument factorizes before estimating.

### The bilinear coefficient bound, unconditionally — `Sieve/ProdIdxFibreDivisorBound.lean`

`DirichletBilinear.sum_norm_sq_dirConv_le` — the corpus's `ℓ²` bound for a convolution — was stated
with an open hypothesis `D` bounding the fibres of `(n,m) ↦ nm`. The same divisor injection used for
the cube discharges it:

- **`prodIdx_fibre_card_le_divisors`** : `#{(n,m) : nm = r} ≤ d(r)`, since a pair with a given
  product is determined by its first entry, which divides the product;
- **`exists_prodIdx_fibre_card_le_rpow`** : `#fibre ≤ C_ε·(NM)^ε`;
- **`exists_sum_norm_sq_dirConv_le_rpow`** :

      ∑_r |(a * b)_r|² ≤ C_ε (NM)^ε · (∑_j |a_j|²)(∑_k |b_k|²) ,

  with no hypothesis at all.

Built, wired, axiom-clean. This closes a hypothesis that had been open in the corpus's bilinear layer
since it was written, and it is the coefficient input every mean-value theorem in the chain consumes.

### Gallagher's identity against a mean square — `Sieve/GallagherSplitIntegral.lean`

`GallagherSplit.gallagher_split` consumes a **pointwise** bound on the Dirichlet polynomial over
`|w| ≤ W`. That is precisely what the zero-free region can supply and precisely what caps the method
at long windows. A large-values estimate supplies no pointwise bound — it controls only the integral
of `|F|²` — so the identity needs a second split, and the Gallagher weight's uniform cap provides it:

- **`fourier_triC_re_le_two_sq`** : `Re 𝓕(tri_δ)(w) ≤ 2δ²` for every `w`, from the corpus's own
  Lorentzian majorant `norm_fourier_triC_le`;
- **`gallagher_split_integral`** :

      ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du ≤ 2δ²·∫_{|w| ≤ W}|F(w)|² dw + M₂·2/(π²W) ;

- **`setIntegral_normSq_logWindowSum_le_integral`**, and
  **`setIntegral_normSq_multiplicative_window_le_integral`** : the same over any range of starting
  positions, and in the multiplicative-window form `x < n ≤ x·e^δ`.

Built, wired, axiom-clean (four theorems).

The two splits are complementary and the corpus now owns both: the pointwise split is sharp when a
zero-free region reaches `W`, the integral split when it does not. The large-values layer of the
previous sections feeds the second, and this is the interface through which it reaches the
short-interval variance — the point where the derivation stopped being able to grow the window.

### The two halves joined — `Sieve/LogPolyDirPoly.lean`, `Sieve/GallagherMeanValue.lean`

The Gallagher side of the corpus works with `logPoly a s w = ∑_{n ∈ s} a_n n^{2πiw}`; the mean-value
and large-values side works with `dirPoly N c t = ∑_{n ≤ N} c_n n^{it}`. They are the same object:

- **`logPoly_eq_dirPoly`** : `logPoly a (Icc 1 N) w = dirPoly N (n ↦ a_{n+1}) (2πw)`, by the
  successor reindexing the corpus already owned (`image_succ_univ`, `succ_injOn`);
- **`dirPoly_conj_neg`** : `dirPoly N (conj∘c) t = conj (dirPoly N c (−t))` — reflecting the
  frequency costs nothing, since conjugating the coefficients preserves the `ℓ²` norm;
- **`integral_Icc_normSq_dirPoly_symm_le`** : the mean value theorem on a symmetric range,
  `∫_{|t| ≤ T}|F|² ≤ 2(T + 4N(1+log N))∑|c_n|²`;
- **`integral_Icc_normSq_logPoly_le`** :

      ∫_{|w| ≤ W} |logPoly a (Icc 1 N) w|² dw ≤ (2πW + 4N(1+log N))/π · ∑_{n ≤ N}|a_n|² ,

  the change of variables `t = 2πw` turning the factor `2` from the two halves into the `π`.

Composing with the integral split gives the base estimate of the whole programme, with **no**
arithmetic input at all:

- **`gallagher_meanValue_le`**, **`gallagher_meanValue_window_le`** :

      ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du
        ≤ 2δ²(2πW + 4N(1+log N))/π · ∑_{n ≤ N}|a_n|² + (∑_{n ≤ N}|a_n|)²·2/(π²W) ,

  for every `W > 0`, and the same over any range of multiplicative starting positions.

Built, wired, axiom-clean (seven theorems).

For `a = μ` this is `≪ δ²WN + δ²N²log N + N²/W`; at `W ≍ N^{1/2}/δ` it is `≪ δN^{3/2} + δ²N²log N`,
against the trivial `δN²`. So the corpus now proves an unconditional power saving for the Möbius
short-interval mean square using **neither** a zero-free region **nor** any cancellation estimate —
the entire gain is the diagonal of the mean value theorem. That is the baseline every arithmetic
input in this chain has to beat, and it is the right place to measure the large-values layer against.

### The factorized mean square — `Sieve/DirichletSymmSplit.lean`, `Sieve/DirichletConvSplit.lean`

Gallagher's identity integrates over a symmetric frequency range, so the large-values estimates were
moved there, and the threshold split was applied to a polynomial that factors.

`DirichletSymmSplit`:
- **`volume_largeValues_symm_le`** : `V²·|{t ∈ [−T,T] : |F(t)| ≥ V}| ≤ 2(T + 4N(1+log N))∑|c_n|²`,
  Chebyshev against the symmetric mean value theorem;
- **`volume_largeValues_sixth_symm_le`** : the same with `V⁶`, by running it on the cube
  (`largeValues_cube_setOf` was generalised in place from `(0,T]` to an arbitrary set);
- **`integral_normSq_mul_split_symm`** : the threshold split on `[−T,T]`.

`DirichletConvSplit`:
- **`integral_Icc_normSq_dirConv_split`** : the split for `dirPoly (N₁N₂) (p ∗ q)`, using the corpus's
  own `dirPoly_mul_eq_dirPoly` to factor the polynomial;
- **`integral_Icc_normSq_dirConv_le`** :

      V⁶∫_{|t| ≤ T}|(p∗q)^(t)|²
        ≤ 2V⁸(T + 4N₁(1+log N₁))∑_j|p_j|²
          + 2(sup|P|)²(sup|Q|)²(T + 4N₂³(1+log N₂³))·D·(∑_k|q_k|²)³ .

Built, wired, axiom-clean (five theorems).

Only the **second** factor is ever raised to the sixth power. So a short second factor with spread-out
coefficients — a prime-supported polynomial over a dyadic range — makes the exceptional term small
while the first term keeps only the diagonal of the mean value theorem. That asymmetry is the entire
point of factorizing before estimating, and it is now available as a single inequality with explicit
constants and no hypotheses beyond the two trivial sup bounds.

### Where this leaves the card

`(15)`–`(18)` still rest on Matomäki–Radziwiłł 2016 Theorem 2 / Menon 2026. What has changed is that
the corpus now owns, unconditionally, every structural ingredient of the proof of that theorem except
the choice of factorization ranges and the Halász input on the exceptional frequency:

1. Gallagher's reduction, exact, in both the pointwise-split and mean-square-split forms;
2. the mean value theorem in the frequency variable, on symmetric ranges, with the `logPoly`↔`dirPoly`
   dictionary;
3. the large-values estimates at the sixth power — sum, count, measure and integral forms — with the
   divisor bound discharged so nothing is hypothetical;
4. the threshold split combining a mean square with a level-set measure;
5. the same for a factorized polynomial, which is the shape the multiplicative decomposition
   produces;
6. the bilinear coefficient bound `∑|(a∗b)_r|² ≤ C_ε(NM)^ε(∑|a_j|²)(∑|b_k|²)`, previously hypothetical.

The remaining work is arithmetic, not structural: choosing the ranges (`RamareFactorization` supplies
the decomposition) and supplying the Halász bound at the exceptional frequency
(`HalaszDichotomy`/`HalaszWindow`, whose distance side is already closed).

## The remaining input is tracked on a dedicated programme card (2026-08-17)

The single thing between this card and stage 3 is Matomäki--Radziwiłł's theorem for the Möbius
function.  That formalisation is now a card of its own,
`docs/drafts/pipeline/1-in-progress/matomaki-radziwill-lean-programme.md`, shared with the two
`route-e-*-e3-*` cards (which need Matomäki--Teräväinen instead).  It holds the milestone table, the
lemma-by-lemma inventory of what this corpus already owns, and the progress log.  Read it before
attacking the input again from here.

Two findings recorded there change the plan and are worth repeating:

- **The exposé's multiplicative-to-additive transfer (Saffari--Vaughan) is not needed.**  This
  card's own object, `RHTower.Sieve.innerFibre`, is already a multiplicative window
  `(x/a, (x/a)(1 + h/√x)]` whose ratio does not depend on the outer variable `a`, so the Plancherel
  identity applies directly with `δ = log(1 + h/√x)`.
- **The Vinogradov--Korobov zero-free region is a hard prerequisite.**  Every stage of the argument
  needs cancellation in `∑_{p ≍ P} p^{iy}` uniformly for `|y| ≤ X`, which is useful only when
  `log P ≫ (log X)^{2/3+δ}`.  The corpus's zero-free region and its twisted Möbius layer carry the
  classical shape `exp(-c log N/(log K)^9)`; even the de la Vallée Poussin exponent `1` would need
  `log P ≫ log X`, impossible for `P ≤ h ≤ X`.  So the Vinogradov--Korobov region is Milestone 0.

Two bricks have landed, both unconditional and axiom-clean:
`Sieve/LogWindowPlancherel.lean` (the exact Plancherel identity for a logarithmic window sum,
replacing the corpus's lossy Gallagher inequality) and `Sieve/LogWindowDiscreteTransfer.lean`
(the passage from a discrete family of starting points to the mean square over the line).

### Correction to the Vinogradov--Korobov note (same day)

The claim just above -- that the corpus's zero-free region is too weak and that Vinogradov--Korobov
must be built from scratch -- is **wrong**, and the programme card now records the corrected
analysis.  The abscissa `1 - c/(16 (log K)^9)` belongs to the corpus's *classical* Möbius contour
(`Sieve/MoebiusContourBound.leftAbscissa`).  The Route-T tower carries a genuinely
Vinogradov-type region:

```text
zeta(beta + i gamma) != 0   for   beta > 1 - c/((log gamma)^{9/10} (log log gamma)^2) ,
```

`Sieve/RouteTZetaZeroFreeAbs.exists_routeT_zero_free_region_abs` together with the explicit
envelope `Sieve/RouteTZetaAsymptotics.routeTZeroFreeDelta_polylog_lower`.  Exponent `9/10` is
enough for every milestone of the programme: the large-prime range to which the twisted-sum bound
is applied may be placed anywhere in `[exp((log X)^alpha), exp((log X)^beta)]` with
`9/10 < alpha < beta < 1`, and its harmonic mass still grows like `(beta-alpha) log log X`.

The Möbius half of that twisted-sum bound is already proved at the Route-T abscissa
(`Sieve/RouteTMoebiusPowerSaving.exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower`);
the remaining half is the prime sum `sum_{p<=x} p^{it}`, whose edge input --
`zeta'/zeta` on that abscissa -- is now `Sieve/ZetaLogDerivWidthBound.lean`.

## Lean gate, restated (2026-08-17)

The analytic gate of this card is **not** Matomäki--Radziwiłł's qualitative short-interval theorem
but Menon's quantitative rate

```text
(1/Y) ∫_Y^{2Y} | (1/L) sum_{x < n <= x+L} mu(n) |^2 dx
    <<  (log log L)^2/(log L)^2  +  (log log Y)^4/(log Y)^2 .
```

The exponent `2` is used, not merely positivity: the card's Markov step needs the mean square to be
`o(1/log X)`, and a rate `(log L)^{-c}` with `c < 1` cannot deliver that inside the card's own
admissible window range.  The extra factor over Matomäki--Radziwiłł is Halász's theorem carried with
its constant for `mu` specifically, where the pretentious distance
`sum_{p <= x}(1 + Re p^{-it})/p ~ 2 log log x` is maximal and produces exactly `(log L)^{-2}`.

Programme, progress and the current Lean inventory:
`../../1-in-progress/matomaki-radziwill-lean-programme.md`.

### Route-T twisted prime sums — landed (2026-08-17)

The Vinogradov--Korobov input of that programme is built and unconditional.  The twisted Chebyshev
contour is closed in both regimes (pole inside / outside the truncated rectangle) and collapsed to a
single explicit inequality, `Sieve/VonMangoldtTwistRouteTSharp`:

```text
‖ sum_{p <= K} (log p) p^{-i tau} ‖
   <=  C·K·(K/H)²·[ (log K)²/|tau| + (1/|tau| + log(3|tau|/2)/w(3|tau|/2+1))
                     · ((3K)^{-W(3|tau|/2)} + |tau|^{-2}) ] / (2 pi)
       + log(K+H)·H  +  (prime-power mass) ,
```

for every `K >= e^9`, every smoothing width `0 < H <= K`, and every `|tau| >= tau_0`, with `w` the
Route-T zero-free width and `W` the contour width.  All of it is axiom-clean and umbrella-wired.

## Sign occupancy of the window is Lean (2026-08-18)

`Sieve/MoebiusSignInWindow.exists_moebius_eq_in_window` proves, unconditionally, that for both
signs the interval `[x, x + √x·exp((log x)^{99/100})]` contains an integer `m` with `μ(m) = s`.
See the Hall-law card for the mechanism (multiplicativity on a coprime sign-class pair) and for the
current build blockage in the `ladderEta` refactor.  This is the qualitative half of the marker
supply; the quantitative count still needs the window-localised distinct-target bound.

### Step 1's squarefree half is closed at rate `(log x)^{-2}` (2026-08-18)

Three new modules, all axiom-clean (`[propext, Classical.choice, Quot.sound]`) and wired into
`GaloisForLFunctions.RHTower`.

**What was wrong.** `Sieve/AveragedSquarefreeTail.sum_tail_divisor_count_le` bounds the averaged
truncation tail by `L·((B+L-A)/R + M)`. The `+M` is the `+1` defect of
`#{n ∈ (A,B+L] : d²∣n} ≤ (B+L-A)/d² + 1`, paid once for each of the `M-R` divisors. Instantiated at
the fibre data (`L = ⌈h⌉+1`, `B = ⌈√x⌉`, `M' = ⌈√(x+h√x)⌉ ≍ √x`) that term alone contributes
`≍ 400√x` exceptional fibres after the Markov division by `θ = h/100` — more than the outer block
itself, at every `R`. This is what the earlier `R ≍ 27` attempt was really failing on;
`Sieve/SquarefreeMaximalWindow.sum_tail_divisor_count_le_sqrt` improves `M` to `√(B+L)` but keeps an
additive term.

**The fix.** After the double count over starts, anchor the multiple count at the origin:
`#{n ∈ (0,N] : d²∣n} = ⌊N/d²⌋ ≤ N/d²` exactly, no defect (`Nat.Ioc_filter_dvd_card_eq_div`). Hence

- `Sieve/AveragedSquarefreeTailSharp.sum_tail_divisor_count_le_sharp : … ≤ L(B+L)/R`,

with no dependence on the truncation level at all. `Sieve/FibreTailSharp` aggregates it to
`fibreTailBudgetSharp x h R = 4(⌈h⌉+1)(⌈√x⌉+⌈h⌉+1)/R` and Markov-divides
(`card_fibre_bad_le_sharp`).

**Why this matters for the marker join.** The join in step 2 discards bad fibres from a dyadic block
carrying `≍ √x/log x` marker primes, so the exceptional set must be `o(√x/log x)` — a constant
fraction of `√x` is useless. With the sharp budget the squarefree exceptional count is `≍ √x/R`, and
the squarefree-mass hypothesis `R + L/R + θ ≤ (1/2)ϱL` permits any `R` below a fixed fraction of the
window length `h = exp((log x)^{99/100})`, which exceeds every power of `log x`. Taking
`R = ⌈(log x)³⌉ + 100` gives

```
Sieve/FibreStepOnePositive.eventually_fibre_step_one_growing (hε : 0 < ε) :
  ∀ᶠ x in atTop,
    #outerBlock ≤ #good + 1024·ε·√x/ϱ² + √x/(log x)²
```

unconditionally. `card_outerBlock_ge : √x - 1 ≤ #outerBlock` is proved alongside, and
`eventually_fibre_step_one_positive` records the corollary `(3/4)√x ≤ #good` at `ε = 10⁻⁵`.

**The one remaining gate on this card.** The squarefree half is now `√x/(log x)²`, strictly better
than the join needs. The Möbius half is `1024·ε·√x/ϱ²`, where `ε` is any tolerance the corpus's
`Sieve/MoebiusMeanSquare.averagedMeanSquare_moebius` eventually achieves. Since that theorem is
stated as `Tendsto … (𝓝 0)`, it supplies each fixed `ε` but no rate, and a fixed `ε` gives only a
constant fraction of `√x`. What is needed is an explicit `≤ (log x)^{-A}` with `A > 1`. The
majorants underneath it are already explicit closed forms (`RhoLimit.rhoMajorant`,
`SlopeQuotientLimit.slopeMajorant`, `ConstQuotientLimit.constMajorant`) whose dominant term is
`(log x)^{5/4-β-γβ}`, squared by the annulus constant; at `β, γβ > 9/10` that is past `(log x)^{-1.1}`.
Converting those three `Tendsto … (𝓝 0)` statements into explicit majorant inequalities is the whole
of the remaining work for step 1.

### The gate is Halász for `μ`, not bookkeeping — the Ramaré diagonal is `1/W` (2026-08-18)

Correcting the previous entry's last paragraph. Converting the three majorant limits into explicit
inequalities would **not** close step 1, because the rate they are hiding is not a power of `log x`.

Trace the corpus chain: `MoebiusMeanSquare.averagedMeanSquare_moebius` ⟵
`OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget` (a pointwise squeeze) ⟵
`BudgetLimit.tendsto_normalised_omegaBudget`, which squeezes the normalised budget by
`136·slope + 140·energy + 131·const + nonSpectral`. The first three are powers of `log x`. The
fourth is not: `NonSpectralBudget.nonSpectral_div_le` bounds it by

```
3672/W² + 120·m/W² + 480·h²/(W²·√x),        m = mertensS(zhi),  W = mertensS(zhi) − mertensS(zlo)
```

and with `zlo = exp((log x)^{γβ})`, `zhi = exp((log x)^β)` one has `m ≍ β·log log x` and
`W ≍ (β−γβ)·log log x`, so the middle term is `≍ 1/((β−γβ)²·log log x)`. **The corpus's Möbius
short-interval mean square therefore has rate `Θ(1/log log x)`, not `(log x)^{-A}`.**

That term is the Ramaré normalisation loss, and it is structural, not slack: the Ramaré identity
divides by `W = ∑_{zlo<p≤zhi} 1/p`, its `L²` diagonal costs one factor `1/W`, and `W ≤ log log x +
O(1)` for any admissible prime range. Even exploiting the weight `1/(ω_P(m)+1)` non-trivially
would only reach `1/(log log x)³`. No choice of `β, γ, zlo, zhi` inside this decomposition reaches a
power of `log x`.

**What the card actually needs.** Its input `(6)` is Menon's `(log log L)²/(log L)² + (log log
Y)⁴/(log Y)²`, i.e. the square of `log log L/log L`. That factor is the Halász bound for `μ`: the
pretentious distance satisfies `D(μ, n^{it}; N)² = ∑_{p≤N}(1 + Re p^{-it})/p ≥ (2−o(1)) log log N`
uniformly in `t`, and Halász converts `M = min_t D²` into `(1+M)e^{-M}`, which is where the power of
`log` — unreachable from Ramaré alone — comes from. Step 2's Markov step needs exactly `ε = o(1/log
Y)`, since a dyadic marker block carries `≍ √x/log x` primes and the reciprocal map has `O_K(1)`
fibres; no re-tuning of the threshold or of `K` avoids this.

**So the single gate on this card is a Halász-type bound for the Möbius Dirichlet polynomial**, fed
into the existing spectral chain in place of the trivial `|μ| ≤ 1` coefficient bound. The corpus
already owns Halász mean-value infrastructure — `Sieve/HalaszMeanSquare.integral_norm_dirPoly_halasz_on`,
`Sieve/DirichletPolyAffineMeanSquare.integral_norm_dirPoly_halasz_affine`,
`Sieve/HalaszDichotomyInstance.halaszDampedBound` — but not the pretentious-distance lower bound for
`μ` that turns it into a `1/log` saving. That lower bound, and its insertion into the omega budget,
is the work.

The long-range Möbius savings the corpus owns (`Sieve/MoebiusKappaTwoRate`,
`Sieve/MoebiusSavingKappaTwo`, exponent `1/3` and `log^{-2}` contours) do **not** substitute: at
window `exp((log x)^{99/100})` the zero-free-region error `x·exp(−c(log x)^{1/3})` dwarfs the window
itself.

### The Halász gate is tracked on its own card (2026-08-18)

The missing Möbius input for this card is the shared gate of three stage-2 cards and is tracked at
`../../1-in-progress/moebius-halasz-log-saving-programme.md`, with the ingredient table and the
first brick (`RHTower/ZetaNearOneLineBound`, the growth bound just left of the one-line) recorded
there.

## CORRECTION: this card is NOT blocked by the free-scale marker device's ceiling (2026-08-19)

Earlier notes in this session's sibling work claimed that a growing constant `C ≍ log h` is out of
reach because the multi-block marker device caps the block count at `K₀ ≲ log log x`.  **That
ceiling belongs to the device built for `route-e-reciprocal-marker-mobius-hall-law`, not to this
card's construction, and the two are structurally different.**

The Hall-law device merges all `K₀+1` dyadic marker blocks into **one** marker range
`(M₀, 2^{K₀+1}M₀]` served by **one** start modulus.  Two markers of that range sharing a start can
then differ by as much as `X/u² ≍ 4^{K₀}·X/m²`, so the shifted-pair budget runs over `≍ 4^{K₀}`
shifts, and with the marker range itself `2^{K₀}` wide the device inequality becomes
`ε·8^{K₀} ≲ K₀²`.  Since `ε` is bounded below by the Möbius mean-square rate — a power of `log x` at
best — that forces `K₀ ≲ log log x`.

**This card's `(10)`–`(14)` does something else.**  Each block `k ≤ K = ⌊(log h − w)/log 2⌋ − 4` is
an *independent* construction with its own scales:

```text
        markers  2^k N < p ≤ 2^{k+1}N ,   starts  t_p = ⌊X/p⌋ ≍ A_k ≍ N/2^k ,
        window   L_k = ⌊h/2^{k+2}⌋ .
```

Within block `k` two markers sharing a start differ by at most `X/A_k² ≍ 4^k`, and the marker range
is a *single* dyadic block.  So each block pays a bounded pair budget at its own scale, and the
blocks are summed at the end rather than merged.  The factor `log h` is the block count `K`, and
nothing in the per-block estimate degrades with `K`.

### What this card's Lean route actually needs

Not the free-scale device.  Per block `k`, the same per-block machinery this session built —
`Sieve/GenericMarkerAnalytic` (harmonic mass, marker count and pair budget at an **arbitrary** base),
`Sieve/GenericPairBudget`, `Sieve/RankinTruncation` — instantiated at `M₀ = A_k`, window `L_k`, and
then summed over `k ≤ K`.  The one external input is `(15)`: the Möbius short-interval mean square
at window `L_k` with `log L_k ≥ w + O(1)`, i.e. down to `log L ≍ (log X)^{2/3}` for the schedule
`(6)`.  The corpus's mean square reaches only `log L ≥ (log X)^{9/10}`, so this card is gated on the
same milestone B as the sibling cards — but on the *window range*, not on any structural ceiling.

## CORRECTION: the corpus's Möbius mean square already reaches every exponent (2026-08-29)

Every statement on this card that the corpus's short-interval mean square "reaches only
`log L ≥ (log X)^{9/10}`" is **stale**.  Two theorems, both unconditional and `#print axioms`-clean,
give it at *every* exponent in `(0,1)`:

```text
RHTower.Sieve.averagedMeanSquare_moebius_cardLength_all
    {β : ℝ} : 0 < β → β < 1 →
      AveragedMeanSquare (fun n => (μ n : ℝ)) (cardLength β)          -- Sieve/TwoRangeAssembly

RHTower.Sieve.averagedMeanSquare_moebius_scaledLength_all
    {c β : ℝ} : 0 < c → c ≤ 1 → 0 < β → β < 1 →
      AveragedMeanSquare (fun n => (μ n : ℝ)) (scaledLength c β)      -- Sieve/ScaledTwoRangeWindow
```

with `cardLength β x = exp((log x)^β)` and `scaledLength c β = c · cardLength β`.  The `9/10` figure
belongs to the older `Sieve/MoebiusMeanSquare.averagedMeanSquare_moebius_cardLength`, which the
two-range assembly superseded; the two names are different, so the old one is still in the tree and
still says `9/10`.

**Consequence for the window gate.**  The exponent range is no longer a constraint anywhere on this
card: `β = 2/3` — indeed any `β > 0` — is available now.  What remains is the *normalisation* gap,
not the exponent: the corpus's `AveragedMeanSquare` is the fibre form, and the marker construction
consumes the integer-start form `DyadicTranslates.dyadicMeanSquare`.  The sibling Hall-law card
closed without that bridge, by covering the window with tiles instead
(`Sieve/WindowTiling`, `Sieve/FreeScaleCover`, `Sieve/RouteEMarkerHallLaw`), and the same
substitution is what this card's schedule now needs.

### The normalisation bridge, first brick — `Sieve/WindowStartShift` (2026-08-29)

```text
abs_partialSum_sub_le        |S(n) − S(m)| ≤ |n − m| for a weight bounded by one
abs_windowSum_sub_le         window sums whose endpoints differ by little differ by little
fixedWindowSq_le_of_close
    fixedWindowSq f ℓ z ≤ 2·fixedWindowSq f ℓ' z' + 2·(endpoint gap)²
```

Unconditional, axiom-clean, umbrella-wired.

**Why this is the right first brick.**  The fibre normalisation places its windows at the starts
`x/a` with lengths `h√x/a`, for `a ∈ [√x, 2√x]`; the integer-start normalisation places them at
every integer of `[√x/2, √x]` with a fixed length.  The two families of endpoints **interleave
within `O(1)`**: as `a` increases by one, `x/a` moves by `x/a² ≍ 1`.  So each integer-start window
is within a bounded endpoint distance of a fibre window, and the lemma above converts that into a
comparison of squares at the cost of a factor two plus an `O(1)` additive term.  Summed over the
`≍ √x` starts, the additive term contributes `O(√x)`, which is `o(h²√x)` exactly when `h → ∞` —
so it is free.

**What the bridge still needs.**  The fibre windows have *variable* length `h√x/a ∈ [h/2, h]`, while
`dyadicMeanSquare` wants a fixed `ℓ`.  The tool for that is already in the tree and is the reason
this is now a finite task rather than an open one:
`Sieve/ScaledTwoRangeWindow.averagedMeanSquare_moebius_scaledLength_all` holds for **every**
`c ∈ (0,1]` and every `β ∈ (0,1)`, i.e. at every length `c·exp((log x)^β)`.  Finitely many values of
`c` cover the length range `[ℓ, 2ℓ]` to within the same `O(1)` endpoint slack, and the lemma above
absorbs the difference.

### CORRECTION to the correction: `(15)` needs the *rate*, not only the window (2026-08-29)

The note above is right that the corpus's mean square now holds at every exponent `β ∈ (0,1)`, so
the window range `log L ≍ (log X)^{2/3}` is no longer a constraint.  It is **wrong** to conclude that
`(15)` is thereby available.  Reading `(15)`–`(17)` again:

```text
    (1/A_k) ∫_{A_k}^{2A_k} |L_k^{-1} ∑_{x<n≤x+L_k} μ(n)|² dx  ≪  R_k ,
    R_k = (log log L_k)²/(log L_k)² + (log log A_k)⁴/(log A_k)² ,
    R_k · log X = o(1)                                                        (17)
```

`(17)` is what the Markov step `(18)` consumes, and it demands a **rate** `o(1/log X)`.  The corpus's
`averagedMeanSquare_moebius_cardLength_all` gives `o(1)` and nothing more.  At the card's schedule
the arithmetic of `(17)` does work out — `log L_k ≥ (log X)^{2/3}` makes the first term
`(log X)^{-4/3+o(1)}` and `log A_k = (1/2+o(1))log X` makes the second `(log X)^{-2+o(1)}`, both
`o(1/log X)` — but that is a statement about the *target*, not about what is proved.

So this card has **two** residues, not one:

1. **the rate** — Menon's `(log log L)²/(log L)²` saving, i.e. exactly the Halász–Montgomery
   large-values programme of `../../1-in-progress/moebius-halasz-log-saving-programme.md`;
2. **the normalisation** — `(15)` is a real-start integral over `[A_k, 2A_k]` at a moving scale
   `A_k ≍ N/2^k`, while the corpus's `AveragedMeanSquare` is the fibre form at scale `√x`; the
   first brick of that bridge is `Sieve/WindowStartShift` above, and the corpus's
   `AveragedMeanSquareDensityAt` is the shape that carries a moving outer scale.

The earlier claim that "the exponent range is no longer a constraint **anywhere** on this card" is
accurate; the implied claim that the gate is therefore closed is not.
