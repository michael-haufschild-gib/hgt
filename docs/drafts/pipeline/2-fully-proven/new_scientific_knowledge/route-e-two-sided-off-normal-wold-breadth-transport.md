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
