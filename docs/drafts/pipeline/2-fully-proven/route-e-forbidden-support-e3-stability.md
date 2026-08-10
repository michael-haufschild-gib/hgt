# Forbidden-support stability of the all-interval \(E_3\) theorem

- **ID:** route-e-forbidden-support-e3-stability
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Statement:** Matomäki--Teräväinen's all-interval \(E_3\) lower bound remains valid, with
  the same order, after excluding every prime divisor of an arbitrary \(A\le x^B\).

## Goal

Close Route E's simultaneous-coprimality admission gate for finitely many factor blocks.  The
result must be uniform in a dynamically supplied spectator/replacement support, not merely avoid
a fixed finite set.

## Gates

- [x] 0 → 1 in-progress: source-pure quantitative avoidance target
- [x] 1 → 2 fully-proven: complete perturbative proof below, using the published all-interval
  theorem and estimates already proved in its source
- [ ] 2 → 3 formalized: the elementary perturbative layer is formalized (see "Lean progress");
      the all-interval theorem it perturbs is a deep external input, not present in Mathlib
- [ ] 3 → 4 publication-ready: external priority audit and standalone exposition

## Lean progress

`formal/GaloisForLFunctions/RHTower/RouteEForbiddenSupportStability.lean` formalizes the
elementary layer of the perturbation, unconditionally and in the card's own parameter regime
(`fsExponent = 11/10`, `fsSmallScale`, `fsLargeScale`, `fsWindow` are `a`, `P₁`, `R`, `h` of
`(FS1)`):

- `card_mul_log_le_log` and `card_le_log_div_log` are the support-size bound: the prime divisors of
  `A` above a threshold `T` have a product dividing `A`, so their number is at most `log A / log T`.
  This is the single arithmetic fact behind both `#S₁ log P₁ ≤ log A` and `(FS11)`.
- `norm_cpow_le`, `norm_supportSum_le_card_div` and `norm_supportSum_le_log` are `(FS5)`: the
  deleted Dirichlet polynomial satisfies `|D₁(s)| ≤ #S₁/T ≤ log A/(T log T)` uniformly on the
  closed half-plane `Re s ≥ 1`, since each term has modulus `p^{-Re s} ≤ p^{-1} ≤ 1/T`.
- `sum_inv_le_log` is `(FS10)`: the harmonic mass carried away by the deleted support obeys the
  same bound, so the long-interval main term keeps `1 - o_B(1)` of its size.
- `norm_sq_sub_mul_le` and `integral_norm_sq_sub_mul_le` are `(FS6)`: the perturbed mixed mean
  square is at most twice the unperturbed one plus twice the sup-norm square times the second
  factor's mean square.
- `fsWindow_div_eq` is the exact form of `(FS12)`: at the lower endpoints of the two prime ranges
  the window carries exactly `4 log x` scaled units, `card_scaledWindow_le` bounds the integers in
  a scaled window by `h/c + 1`, and `card_window_le` combines them into the `4 log x + 1` bound on
  the remaining variable.
- `tendsto_fsNegligible` is `(FS13)`: the polylogarithmic triple count through one fixed large
  prime, weighted against the main term's `(log x)^{-0.45}` normalisation, tends to zero.
- `eventually_smallScale_lt_largeScale` is the range disjointness that makes the surviving triples
  squarefree, and `card_diagonalWindow_le` is the diagonal case `p₂ = p₃`: the square constraint
  `p₁p₂² ∈ (x, x+h]` leaves at most `log x / 2 + 1` integers, because the square root increases by
  at most `h/(2√x)` over the window (`sqrt_add_sub_sqrt_le`).  So the diagonal carries the same
  polylogarithmic bound as `(FS13)` and its removal leaves three distinct primes.
- `mobiusComplexCoefficient_prime_mul_threePrime`, `mul_sqrt_div_eq_sqrt_mul` and
  `abs_amplified_gap_le` are the block-admission corollary `(FS14)`: a prime cofactor times an
  exact-three-prime token has Möbius `+1`, and amplifying a near-square-root token at the reduced
  centre `u/ℓ` by `ℓ` keeps it within `√(uℓ)` times the same polylogarithmic factor of `u`.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

Not formalized: the all-interval count `(FS4)` itself, and the mean-value estimate `(FS7)` and the
two-dimensional upper-bound sieve it rests on.  These are Matomäki--Teräväinen's published inputs,
quoted rather than proved on this card; they are stated nowhere in the Lean tree, so nothing above
is conditional on them.  Every step this card *proves* is now in Lean.

The corpus Dirichlet mean-value theorem (`RHTower.Sieve.dirichlet_meanValue_theorem`) carries the
error `O(N log N)`, not the Montgomery--Vaughan `O(N)`; even the sharp form only gives `O(1/log R)`
for the second term of `(FS7)`, so that estimate genuinely needs the source's Section 5 sieve and
is not reachable from the card text alone.

## Theorem

Fix \(B>0\).  Put

\[
P_1=(\log x)^{a},\qquad a=1.1,\qquad
R={1\over2}\sqrt{x/P_1},\qquad
h=\sqrt{x}(\log x)^{1+a/2}.
\tag{FS1}
\]

Uniformly for all sufficiently large \(x\) and all integers \(1\le A\le x^B\), the interval
\((x,x+h]\) contains

\[
\gg_B {h\over(\log P_1)(\log x)^2}
\tag{FS2}
\]

products \(p_1p_2p_3\), counted with the same minorant multiplicity as in
Matomäki--Teräväinen's Section 7, such that

\[
p_1\asymp P_1,\qquad p_2\asymp R,\qquad p_3\asymp R,
\qquad (p_1p_2p_3,A)=1.                                  \tag{FS3}
\]

After removing the diagonal \(p_2=p_3\), the same order of lower bound remains for products of
three distinct primes.  In particular there is a squarefree \(E_3\) number coprime to \(A\) in
every such interval.

## Proof

Write \({\cal S}\) for the prime divisors of \(A\).  The proof of
[Matomäki--Teräväinen, Theorem 1.2](https://arxiv.org/abs/2207.05038) establishes

\[
\#\{p_1p_2p_3\in(x,x+h]:p_1\asymp P_1,\ p_2\asymp R\}
\gg {h\over(\log P_1)(\log x)^2}.                         \tag{FS4}
\]

It is enough to show that deleting \({\cal S}\) from each of the three prime variables changes
neither their short/long comparison nor its positive long-interval main term by more than
\(o_B(1)\) relatively.

### 1. The small prime variable

Let

\[
{\cal S}_1={\cal S}\cap(P_1,2P_1],\qquad
D_1(s)=\sum_{p\in{\cal S}_1}p^{-s}.
\]

The product constraint on \(A\) gives

\[
\#{\cal S}_1\log P_1\le\log A\le B\log x,
\]

and hence, uniformly on \(\Re s=1\),

\[
|D_1(s)|
\le {\#{\cal S}_1\over P_1}
\ll_B {(\log x)^{1-a}\over\log\log x}
=O_B\!\left({(\log x)^{-0.1}\over\log\log x}\right).
\tag{FS5}
\]

In the notation of Section 7 of the cited paper, replace
\(P_1(s)=\sum_{p\asymp P_1}p^{-s}\) by \(P_1(s)-D_1(s)\).  Every Dirichlet-polynomial estimate
except the mixed \(P_1P\) mean square is immediately monotone or follows by the triangle
inequality.  For the mixed term,

\[
\int |(P_1-D_1)P|^2
\le 2\int|P_1P|^2+2\|D_1\|_\infty^2\int|P|^2.             \tag{FS6}
\]

The first integral is the proved estimate used in their equation (7.6).  The improved mean-value
theorem and the same two-dimensional upper-bound sieve used in their equations (5.2)--(5.3) give,
for \(T\ge x/h\),

\[
\int_{T_0}^{T}|P(1+it)|^2dt
\ll {T\over R\log x}+{1\over(\log x)^2}.                 \tag{FS7}
\]

Combining `(FS5)` and `(FS7)`, the perturbation in `(FS6)` is

\[
\ll_B
 {T\over\sqrt{x}(\log x)^{0.65}(\log\log x)^2}
 +{1\over(\log x)^{2.2}(\log\log x)^2}.                  \tag{FS8}
\]

This is smaller than the required Section 7 bound

\[
{T\over x/h}{1\over(\log x)^{2+2\varepsilon}}
= {T\over\sqrt{x}(\log x)^{0.45+2\varepsilon}}
\tag{FS9}
\]

for any fixed \(0<\varepsilon<0.1\); at the lower endpoint \(T=x/h\), the second term in
`(FS8)` is also \(o((\log x)^{-2-2\varepsilon})\).  Thus the Perron short/long comparison survives
the deletion.

For the long interval, Mertens' prime estimate gives

\[
\sum_{p\asymp P_1}{1\over p}\asymp {1\over\log P_1},
\qquad
\sum_{p\in{\cal S}_1}{1\over p}
\ll_B {(\log x)^{-0.1}\over\log\log x}.                  \tag{FS10}
\]

The deleted harmonic mass is only \(O_B((\log x)^{-0.1})\) of the full one.  The positive
minorant main term and its upper-bound-sieve majorant are linear in this \(p_1\)-weight, so the
long main term retains \(1-o_B(1)\) of `(FS4)`.

### 2. The two large prime variables

Every \(q\in{\cal S}\) in either large-factor range satisfies
\(\log q=(1/2+o(1))\log x\).  Therefore

\[
\#({\cal S}\cap[R/2,4R])=O_B(1).                         \tag{FS11}
\]

Fix such a \(q\).  For every \(p_1\asymp P_1\), the remaining large prime is constrained to an
interval of integer length

\[
\ll {h\over p_1q}+1\ll(\log x)^{1+a/2-a+a/2}+1
\ll\log x.                                               \tag{FS12}
\]

Consequently the total number of short-interval triples containing \(q\) is

\[
\ll {P_1\over\log P_1}\log x
\ll {(\log x)^{2.1}\over\log\log x}
=o\!\left({\sqrt{x}\over
  (\log x)^{0.45}\log\log x}\right),                     \tag{FS13}
\]

which is negligible compared with `(FS4)`.  The identical argument applies to either large
prime variable.  In the long interval, a one-dimensional upper-bound sieve gives a relative
loss \(O_B((\log x)^2/R)=o_B(1)\).

### 3. Squarefreeness

The \(p_1\)-range and the two large-factor ranges are disjoint.  On the diagonal \(p_2=p_3\),
for each \(p_1\) the product constraint permits only \(O(\log x)\) integer values by `(FS12)`.
Thus the diagonal has the same polylogarithmic bound `(FS13)` and is negligible.  Removing it
proves `(FS2)`--`(FS3)` for three distinct primes.

## Corollary: simultaneous block admission

Fix \(\delta>0\).  Let \(u_1,\ldots,u_r\) be factor blocks with
\(\prod_i u_i\le N^{O(1)}\), \(u_i\ge N^\delta\), and \(r=O_\delta(1)\).  Process them
sequentially.  At stage \(i\), the product of every original prime support and every previously
chosen replacement support is at most \(u_i^{O_\delta(1)}\).  The theorem supplies an \(E_3\)
replacement coprime to all of them.

If \(\mu(u_i)=+1\), use that \(E_3\) token.  If \(\mu(u_i)=-1\), choose a fresh prime
\(\ell_i\ll_\delta\log N\) outside the accumulated support and apply the theorem at
\(u_i/\ell_i\), also forbidding \(\ell_i\).  Then

\[
Q_i=\ell_i E_3(u_i/\ell_i),\qquad
\mu(Q_i)=+1=-\mu(u_i),
\]

is squarefree and

\[
|Q_i-u_i|
\ll \sqrt{u_i\ell_i}\,(\log u_i)^{1.55}
=u_i^{1/2}N^{o(1)}.                                      \tag{FS14}
\]

The resulting block pairs are jointly coprime.  For \(u_i\le z^2\), the factor ranges in the
all-interval proof keep every replacement prime at most \(z\).  Hence every corner of the
associated block cube remains in the zero/one-large-prime boundary.

This closes simultaneous pointwise coprime **admission** for any fixed number of polynomial-scale
blocks.  It does not prove fractional vertex capacity, incoming-corner co-degree, or co-moving
cutoff flux.

## Novelty audit

The underlying all-interval \(E_3\) theorem and all mean-value/sieve estimates are published.
The uniform deletion of an adversarial support \(A\le x^B\), its \(L^\infty\)-small-prime
Dirichlet perturbation `(FS5)`--`(FS9)`, and the simultaneous block-admission corollary were not
found in the source or collision search.  This is a stability extraction from the published
proof, not a new Type-II estimate.

## Log

- 2026-08-01 — extracted and proved polynomial-forbidden-support stability; closed Route E's
  finite-block simultaneous coprimality gate on paper.  Remaining source core is capacity and
  co-moving seam flux.
