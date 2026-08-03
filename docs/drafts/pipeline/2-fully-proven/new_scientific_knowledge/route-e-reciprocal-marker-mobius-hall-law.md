# Route E reciprocal-marker Möbius Hall law

- **ID:** `ROUTE-E-RECIPROCAL-MARKER-HALL-001`
- **Stage:** 2-fully-proven
- **Type:** NEW SYNTHESIS / ALL-INTERVAL DISTINCT-TARGET THEOREM
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** prime-anchor, window, sign and unique-decoding skeleton in
  `MobiusReciprocalMarkerPrimeCapacity.lean`; the distinct-target count, the Markov step `(10)`,
  the marker discard, the squarefree count `(7)`/`(11)` with density `6/pi^2`, the averaged tail
  `(12)`-`(13)`, the dyadic prime supply and the integer-start comparison are formalized
  unconditionally in `MobiusReciprocalMarkerBlockCount.lean`, `Sieve/SquarefreeCount.lean`,
  `Sieve/AveragedSquarefreeTail.lean`, `Sieve/PrimeWindow.lean`, `Sieve/StartShift.lean`;
  the sole remaining input is Menon's unconditional 2026 Moebius mean-square theorem `(6)`

## Statement

Fix
\[
 \frac12<\beta<1,\qquad
 h(X)=\exp\!\big((\log X)^\beta\big),\qquad
 H(X)=\sqrt X\,h(X).
\tag{1}
\]
For \(\sigma\in\{-1,+1\}\), write
\[
 T_\sigma(X)=\{n\in\mathbb N:X<n\le X+H(X),\ \mu(n)=\sigma\}.
\tag{2}
\]
Then for every fixed \(C>0\),
\[
 \#T_\sigma(X)\ge C\,\frac{H(X)}{\log X}
\tag{3}
\]
for both signs and all sufficiently large \(X\), with the threshold depending on
\(C,\beta\).

More precisely, for every fixed positive integer \(K\), `(3)` holds with
\(C=cK\), where \(c>0\) is absolute.  Every target counted by this construction has a
canonical factorization
\[
 n=ap,\qquad p>\sqrt X>a,\qquad \mu(a)=-\sigma,
\tag{4}
\]
and the marker prime \(p\) uniquely determines \(a\).  Thus the count is a count of
distinct physical integers, not of representations.

As a consequence, after increasing the fixed \(K\), every interval
\((X,X+H(X)]\) contains at least as many positive-Möbius targets as source primes.
Partitioning a dyadic shell into such intervals gives an injection from its source primes
to positive-Möbius integers at displacement at most \(H(X)=X^{1/2+o(1)}\).  Its normalized
first-order Gibbs cost is
\[
 \ll \frac{H(X)}{\log X}=X^{1/2+o(1)}.
\tag{5}
\]
This closes `MOBIUS-PRIME-ANCHOR-PHYSICAL-HALL`.  It does not by itself cover the
positive-density composite source sector or prove `OPEN-SOURCE-001`.

## Analytic inputs

Menon's Theorem 1.1, whose paper states that the Möbius analogue is identical, gives
uniformly for \(10\le L\le Y\)
\[
 \frac1Y\int_Y^{2Y}
 \left|
   \frac1L\sum_{x<n\le x+L}\mu(n)
 \right|^2dx
 \ll
 \frac{(\log\log L)^2}{(\log L)^2}
 +\frac{(\log\log Y)^4}{(\log Y)^2}.
\tag{6}
\]
We also use the prime number theorem on fixed dyadic intervals and
\[
 \mu^2(n)=\sum_{d^2\mid n}\mu(d),\qquad
 D:=\sum_{d\ge1}\frac{\mu(d)}{d^2}=\frac6{\pi^2}.
\tag{7}
\]

For \(L=\exp((\log Y)^\beta)/O_K(1)\), `(6)` has right-hand side
\[
 R(Y,L)
 \ll_K
 \frac{(\log\log Y)^2}{(\log Y)^{2\beta}}
 +\frac{(\log\log Y)^4}{(\log Y)^2}
 =o\!\left(\frac1{\log Y}\right),
\tag{8}
\]
because \(2\beta>1\).

## Proof

### 1. Almost every cofactor interval contains linearly many of both signs

For an integer start \(t\), put
\[
 M(t,L)=\sum_{t<n\le t+L}\mu(n),\qquad
 Q(t,L)=\sum_{t<n\le t+L}\mu^2(n).
\tag{9}
\]
If \(x\in[t,t+1)\), the continuous-start sum in `(6)` differs from \(M(t,L)\)
by at most two endpoint terms.  Markov's inequality and `(8)` therefore show that,
in any fixed dyadic interval of starts of scale \(Y\),
\[
 \#\{t:|M(t,L)|>\tfrac18DL\}=o(Y/\log Y).
\tag{10}
\]

The corresponding squarefree assertion is elementary and needs no short-interval
prime theorem.  Let \(R=\lfloor\sqrt L\rfloor\) and truncate `(7)`:
\[
 Q_R(t,L)
 :=\sum_{t<n\le t+L}\sum_{\substack{d^2\mid n\\d\le R}}\mu(d)
 =DL+O(\sqrt L)
\tag{11}
\]
uniformly in \(t\).  Indeed, each \(d\le R\) contributes \(L/d^2+O(1)\),
and both the truncation tail in \(\sum\mu(d)/d^2\) and the accumulated integer-part
error are \(O(\sqrt L)\).

For starts \(t\asymp Y\), the average absolute omitted tail is bounded by
\[
 \begin{aligned}
 \frac1Y\sum_{t\asymp Y}|Q(t,L)-Q_R(t,L)|
 &\le
 \frac{L}{Y}
 \sum_{n\asymp Y}
 \sum_{\substack{d>R\\d^2\mid n}}1\\
 &\ll
 \frac{L}{Y}
 \sum_{R<d\ll\sqrt Y}\left(\frac{Y}{d^2}+1\right)
 \ll \sqrt L+\frac{L}{\sqrt Y}.
 \end{aligned}
\tag{12}
\]
Hence another application of Markov gives
\[
 \#\{t:Q(t,L)<\tfrac12DL\}
 \ll \frac{Y}{\sqrt L}+\sqrt Y
 =o(Y/\log Y).
\tag{13}
\]

Outside the union of `(10)` and `(13)`,
\[
 \#\{t<n\le t+L:\mu(n)=\pm1\}
 =\frac{Q(t,L)\pm M(t,L)}2
 \ge \frac{3D}{16}L.
\tag{14}
\]
The constant \(3D/16\) is inessential; only a fixed positive constant matters.

### 2. Reciprocal marker blocks

Put \(N=\sqrt X\).  Fix \(K\), and for \(1\le k\le K\) take marker primes
\[
 2^kN<p\le2^{k+1}N.
\tag{15}
\]
Define
\[
 t_p=\left\lfloor\frac Xp\right\rfloor,\qquad
 L_k=\left\lfloor\frac{h(X)}{2^{k+2}}\right\rfloor.
\tag{16}
\]
Then \(t_p\) lies in a fixed dyadic cofactor range of scale \(2^{-k}N\), and
\(\log L_k\sim(\log N)^\beta\).

Call \(p\) good if `(14)` holds on \((t_p,t_p+L_k]\).  The reciprocal map has
bounded fibres depending only on \(K\): if \(\lfloor X/p\rfloor=t\), then
\[
 \frac X{t+1}<p\le\frac Xt,
\tag{17}
\]
so the number of possible integral \(p\) is at most
\[
 \frac{X}{t(t+1)}+1\ll_K1.
\tag{18}
\]
Equations `(10)` and `(13)` therefore discard only \(o(N/\log N)\) marker
primes from each fixed block.  The prime number theorem gives
\[
 \#\{p\text{ good}:2^kN<p\le2^{k+1}N\}
 \gg_K\frac{2^kN}{\log N}.
\tag{19}
\]

For each good \(p\), choose every \(a\) such that
\[
 t_p<a\le t_p+L_k,\qquad \mu(a)=-1.
\tag{20}
\]
There are at least \((3D/16)L_k\) choices.  They produce
\[
 X<ap
\le X+pL_k
\le X+\frac12Nh(X)
 <X+H(X).
\tag{21}
\]
For fixed \(K\) and large \(X\),
\[
 a\le 2^{-k}N+o(N)<N<p.
\tag{22}
\]
Thus \(p\nmid a\), \(ap\) is squarefree, and
\[
 \mu(ap)=\mu(a)\mu(p)=+1.
\tag{23}
\]

### 3. Physical products are uniquely decoded

Suppose two constructed products agree:
\[
 ap=a'p'.
\tag{24}
\]
All cofactors satisfy \(a,a'<N\), while all markers satisfy \(p,p'>N\).
If \(p\ne p'\), primality and `(24)` force \(p\mid a'\), impossible because
\(0<a'<p\).  Hence \(p=p'\), and cancellation gives \(a=a'\).
This works across all \(k\), not merely inside one block.  No divisor-multiplicity
normalization is present.

Combining `(19)` with \(L_k\asymp_K2^{-k}h(X)\), every marker block contributes
\[
 \gg \frac{2^kN}{\log N}\,2^{-k}h(X)
 \gg \frac{H(X)}{\log X}
\tag{25}
\]
distinct positive-Möbius targets, with an absolute lower constant after \(K\) is
fixed.  The \(K\) blocks are disjoint under the unique marker decoding, so their
contributions add.  This proves `(3)` for \(\sigma=+1\).

Using \(\mu(a)=+1\) in `(20)` instead gives \(\mu(ap)=-1\), and `(14)` supplies
the same count.  This proves `(3)` for both signs.

### 4. Prime-anchor Hall and cost

Brun--Titchmarsh gives, since \(H(X)<X\),
\[
 \pi(X+H(X))-\pi(X)
 \le \frac{2H(X)}{\log H(X)}
 =\left(4+o(1)\right)\frac{H(X)}{\log X}.
\tag{26}
\]
Choose \(K\) so that the positive-target lower constant in `(25)`, summed over
the \(K\) blocks, exceeds \(5\).  Then every physical \(H(X)\)-cell contains
at least as many positive-Möbius targets as source primes.  Matching inside
disjoint cells yields a literal injection with displacement at most \(H(X)\).

On a dyadic physical shell of size \(U\), the total source-prime displacement is
\[
 \ll \frac{U}{\log U}\,H(U).
\tag{27}
\]
Multiplication by the Gibbs scale \(x\asymp U^{-1}\) gives `(5)`.

## Hostile audit

1. **No polylogarithmic prime PNT is used.**  Maier's theorem forbids that shortcut.
   Marker primes are counted only on fixed dyadic intervals by the ordinary PNT.
   Menon's theorem is applied to the dense cofactor starts.
2. **The sampled starts cannot hide in the exceptional set.**  Menon's exceptional
   count is \(o(N/\log N)\), not merely \(o(N)\), because \(\beta>1/2\).
   The reciprocal map has \(O_K(1)\) fibres.
3. **Squarefree mass is not inferred from a small Möbius sum.**  Equations
   `(11)`--`(13)` prove it independently.
4. **Representations are not counted as targets.**  The marker \(p>N>a\) is uniquely
   recoverable, so `(25)` counts physical integers.
5. **Constants are not hidden in Hall.**  Arbitrarily many fixed dyadic marker blocks
   amplify the lower constant past the fixed Brun--Titchmarsh constant.
6. **No RH-equivalent input appears.**  Menon's theorem, squarefree divisor identity,
   PNT, and Brun--Titchmarsh are unconditional.
7. **Scope is exact.**  The theorem closes prime-anchor capacity only.  It does not
   control a positive-density composite exceptional set or the sectorwise co-moving
   flux.

## Novelty audit

Searches covered combinations of:

- Möbius signs in every short interval;
- reciprocal sampling \(\lfloor X/p\rfloor\);
- prime--Möbius product signs;
- distinct positive/negative Möbius values at square-root scale;
- multiplicative-function sign-pattern and short-interval papers.

Known ingredients found:

- Matomäki--Radziwiłł: almost-all short averages and global sign changes;
- Matomäki--Teräväinen: all-interval Möbius cancellation only above exponent \(0.55\);
- Menon: the sharpened almost-all mean-square estimate `(6)`;
- Matomäki--Radziwiłł--Tao: positive lower density of fixed global sign patterns.

No source found the reciprocal-marker transfer, the arbitrary-constant distinct-target
law `(3)`, or its largest-prime Hall injection.  The defensible claim is a new synthesis
and extraction from Menon's theorem; external priority remains unverified.

## Route E effect

- **Closed:** `MOBIUS-PRIME-ANCHOR-PHYSICAL-HALL`.
- **New invariant:** reciprocal marker primes turn logarithmically small exceptional
  cofactor sets into collision-free physical Möbius targets.
- **Still open:** positive-density composite cube capacity and
  `MOBIUS-EXCEPTIONAL-CARLESON`, including co-moving seam flux.

## Log

- 2026-08-01 — theorem discovered, hostile-audited, and proved on paper.

## Lean completion programme (opened 2026-08-03)

This card shares its arithmetic skeleton with
`route-e-growing-reciprocal-marker-low-breadth-transport.md`, and the layer built for that card
covers almost all of it.  Corpus audit before starting, with the matching card equation:

| card equation | Lean declaration |
|-|-|
| `(4)` canonical factorization, unique decoding | `MobiusReciprocalMarkerPrimeCapacity.largePrimeMarker_product_injective`, `reciprocalMarker_target_sign_flip` |
| `(7)` `μ² = ∑_{d²∣n} μ(d)`, `D = 6/π²` | `Sieve/SquarefreeCount.sum_truncated_moebius_eq`, `squarefreeDensity_eq` |
| `(10)` Markov on the mean square | `MobiusReciprocalMarkerBlockCount.card_large_le_of_sum_sq_le` |
| `(11)` truncated squarefree count, uniform in `t` | `Sieve/SquarefreeCount.abs_truncated_squarefree_sub_le` |
| `(12)`–`(13)` averaged omitted tail | `Sieve/AveragedSquarefreeTail.sum_tail_divisor_count_le` |
| distinct-target count | `MobiusReciprocalMarkerBlockCount.card_markerBlockTargets` |
| window membership | `markerBlockTargets_mem_window` |
| target sign | `markerBlockTargets_sign` |
| marker discard by bad starts | `card_markers_start_mem_le` |
| prime supply on a dyadic block | `Sieve/PrimeWindow.card_bigPrimeSet_ratio_ge` |
| `(5)` first-order Gibbs cost | `MobiusWoldBreadthGibbsCost.abs_gibbsEdge_le`, `sum_abs_gibbsEdge_le` |

### The one missing elementary step landed — `Sieve/StartShift.lean`

The card's `(10)` passes from the continuous start of `(6)` to an integer start, "up to two endpoint
terms".  That comparison is now exact:

- `sum_Ioc_succ_self` : a one-step window is a singleton;
- **`sum_Ioc_succ_sub`** :
  `∑_{t+1 < n ≤ t+1+L} f(n) − ∑_{t < n ≤ t+L} f(n) = f(t+1+L) − f(t+1)` — an identity, valid for
  every `L` including `L = 0`;
- **`abs_sum_Ioc_succ_sub_le`**, `abs_sum_Ioc_moebius_succ_sub_le` : for a coefficient bounded by
  one — the Möbius function in particular — consecutive integer starts differ by at most two.

Built, wired, axiom-clean.

### What remains

`(6)` alone: Menon's 2026 mean-square theorem for Möbius in short intervals, the same cited
published input as the sibling card.  Mathlib has neither it nor the Matomäki–Radziwiłł theorem it
refines, and the corpus has no substitute — a mean-square bound of size `o(1/log Y)` at
`L = exp((log Y)^β)` is exactly the content of that theorem, so no weaker unconditional estimate
can stand in.  Every other step of this card is now an unconditional Lean theorem, and `(8)` is
pure arithmetic on the exponents once `(6)` is available.
