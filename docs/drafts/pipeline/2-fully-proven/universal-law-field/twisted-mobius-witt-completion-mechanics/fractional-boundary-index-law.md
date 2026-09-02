# Twisted Möbius--Witt fractional boundary-index law

- **ID:** ULF-TMW-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** exact integer Möbius inversion + existing Suzuki/Wold activation factor
- **Statement:** A positive horizontal twist changes exact Möbius--Lambert cancellation into a
  nonintegral boundary index \(1/\zeta(1+a)\), so its normalized Witt formation has no meromorphic
  continuation through the cofinal point \(z=1\); at \(a=0\) it is \(e^{-z}\).

## Definitions

For \(a\ge 0\), \(m\ge1\), and \(|z|<1\), put
\[
 K_a(m)=\sum_{d\mid m}\mu(d)d^{-a},\qquad
 M_a(z)=\sum_{n\ge1}\mu(n)n^{-a}\frac{z^n}{1-z^n},
\]
and define the normalized Witt formation
\[
 W_a(z)=\exp\!\left(\sum_{n\ge1}
       \frac{\mu(n)}{n^{a+1}}\log(1-z^n)\right),
 \qquad W_a(0)=1 .
\]
The logarithm is its canonical power-series branch on the unit disc.

## Theorem [PROVED HERE]

1. Both defining series converge normally on compact subsets of the unit disc and
   \[
   M_a(z)=\sum_{m\ge1}K_a(m)z^m=-z\frac{W_a'(z)}{W_a(z)}.
   \]
2. \(K_0(m)=[m=1]\), hence \(M_0(z)=z\) and \(W_0(z)=e^{-z}\) on the disc; in particular
   \(W_0\) extends to a nonvanishing entire function.
3. If \(a>0\), then
   \[
   K_a(m)=\prod_{p\mid m}(1-p^{-a})>0,\qquad
   \lim_{r\uparrow1}(1-r)M_a(r)=\frac1{\zeta(1+a)}\in(0,1).
   \]
4. Consequently \(W_a\) has no single-valued meromorphic continuation to any neighbourhood of
   \(z=1\).

## Proof

Fix \(0<r<1\). Since \(|\mu(n)|n^{-a}\le1\),
\[
 \sum_{n\ge1}|\mu(n)|n^{-a}\frac{r^n}{1-r^n}
 \le \frac1{1-r}\sum_{n\ge1}r^n<\infty .
\]
Thus the Lambert double series is absolutely and locally normally convergent. Expanding
\(z^n/(1-z^n)=\sum_{k\ge1}z^{nk}\) and regrouping by \(m=nk\) gives
\[
 M_a(z)=\sum_{m\ge1}\left(\sum_{d\mid m}\mu(d)d^{-a}\right)z^m.
\]
The logarithmic series for \(W_a\) is normally convergent by the same majorant. Termwise
differentiation gives \(-zW_a'/W_a=M_a\).

At \(a=0\), ordinary Möbius inversion gives
\(\sum_{d\mid m}\mu(d)=[m=1]\). Hence \(M_0=z\); the differential equation and \(W_0(0)=1\)
give \(W_0=e^{-z}\).

For \(a>0\), multiplicativity and squarefree support of \(\mu\) give
\[
 K_a(m)=\prod_{p\mid m}(1-p^{-a})>0.
\]
Moreover,
\[
 \frac1N\sum_{m\le N}K_a(m)
 =\sum_{d\le N}\mu(d)d^{-a}\frac{\lfloor N/d\rfloor}{N}.
\]
The summand converges pointwise to \(\mu(d)d^{-(a+1)}\) and is dominated by
\(d^{-(a+1)}\), which is summable. Dominated convergence therefore gives
\[
 \lim_{N\to\infty}\frac1N\sum_{m\le N}K_a(m)
 =\sum_{d\ge1}\frac{\mu(d)}{d^{a+1}}
 =\frac1{\zeta(1+a)}=:c_a.
\]
Since \(\zeta(1+a)>1\), \(0<c_a<1\). Elementary Abel convergence for a sequence with Cesàro mean
\(c_a\) yields
\[
 \lim_{r\uparrow1}(1-r)\sum_{m\ge1}K_a(m)r^m=c_a.
\]

Suppose \(W_a\) had a meromorphic continuation through \(1\). Write locally
\(W_a(z)=(z-1)^k g(z)\), with \(k\in\mathbb Z\) and \(g(1)\ne0\). Then
\[
 \lim_{r\uparrow1}(1-r)\left(-r\frac{W_a'(r)}{W_a(r)}\right)=k.
\]
The left side is \(c_a\in(0,1)\), impossible because \(k\) is integral. Therefore no such
meromorphic continuation exists.

## Meaning and scope

Neutral grade is the unique twist for which this particular multiplicative Möbius recovery
commutes with meromorphic additive/cyclotomic completion. This is a classification of that
completion, not an RH selector. The coefficient stream is exactly the already formalized
Suzuki/Wold activation factor, valid for every positive grade, with Dirichlet series
\(\zeta(s)/\zeta(s+a)\). Its fractional Abel density obstructs only a further single-valued
meromorphic Witt germ. No corpus theorem requires genuine Xi occurrence to admit that germ.

## Lean status

Arithmetic and meromorphic-quantization core is formalized in
`HTGeometry/TwistedMobiusWittCompletion.lean`: neutral collapse, positive Euler-product fibres,
the identity with reciprocal zeta, strict fractional range, integer-order quantization, and the
closed incompatibility theorem all pass with no project axioms. The normal-convergence,
coefficient-Cesàro, Abel-limit, and explicit `W_a` logarithmic-derivative clauses above remain
paper-only. Therefore full four-part theorem does not yet count as Lean-certified.

## Gates

- [x] 0 → 1: source-pure statement and hostile countermodel scope fixed
- [x] 1 → 2: dependency-closed paper proof above
- [ ] 2 → 3: formalize remaining analytic clauses; arithmetic/quantization core wired
- [ ] 3 → 4: publication-ready extraction

## Producer audit

**FAILED AS RH PRODUCER.** Promoting the reciprocal-zeta density to local divisor order is not
source-forced. The valid theorem remains here because its arithmetic/quantization boundary is
proved, but the candidate programme is retired in `5-failed`.
