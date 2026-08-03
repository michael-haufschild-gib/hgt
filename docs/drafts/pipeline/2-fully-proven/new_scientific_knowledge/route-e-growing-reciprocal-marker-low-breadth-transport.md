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
  fibre bound `(25)`-`(26)`, the short-interval squarefree count `(19)`-`(21)` with the density
  `6/pi^2`, and the averaged truncation tail `(22)`-`(23)` are now formalized unconditionally in
  `Sieve/PrimeWindow.lean`, `Sieve/ReciprocalFibre.lean`, `Sieve/InverseSquareTail.lean`,
  `Sieve/SquarefreeCount.lean`, `Sieve/AveragedSquarefreeTail.lean`; Menon's mean-square input
  `(15)` remains the cited published theorem

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

`(15)`–`(18)` rest on Menon's 2026 mean-square theorem for Möbius in short intervals, a cited
published analytic result; nothing in mathlib or the corpus approaches it, and `(18)` is its Markov
consequence.  `(32)`/`(34)` are Shiu's bound, for which the corpus now owns an unconditional
substitute (`Sieve/RateBridge.card_omega_le_le_rate`) that is weaker by `(log log X)^{Θ(1)}` — still
enough here, since `(34)` is used only as `o(H/log log X)` and `(log X)^{−I(c₀)}(log log X)^{I(c₀)+1}`
tends to zero.  `(35)`/`(36)` are `MobiusWoldBreadthGibbsCost.abs_gibbsEdge_le` and
`sum_abs_gibbsEdge_le`.
