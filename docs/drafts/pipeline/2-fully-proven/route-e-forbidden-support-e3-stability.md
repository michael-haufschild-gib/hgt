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
- [ ] 2 → 3 formalized: the deep Type-II input is not present in Mathlib; no axiom is introduced
- [ ] 3 → 4 publication-ready: external priority audit and standalone exposition

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
