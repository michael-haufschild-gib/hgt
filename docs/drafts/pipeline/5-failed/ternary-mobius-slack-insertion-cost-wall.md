# Ternary Möbius slack insertion has an unavoidable divisor-mass cost

- **ID:** `MOBIUS-TERNARY-INSERTION-NOGO-001`
- **Status:** `[PAPER-PROVED] [FAILED ROUTE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Date:** 2026-07-22
- **Parent:** `../1-in-progress/mobius-additive-frontier-research-ledger.md`
- **Open source:** `OPEN-SOURCE-001`

## Question attacked

Can a ternary Möbius estimate be applied to the two unweighted slack variables in

\[
 U(N)=\sum_{a+b=N}M(a)M(b)
     =\sum_{r+s\leq N}\mu(r)\mu(s)(N+1-r-s)
\]

by inserting an additional Möbius factor through Dirichlet inversion?  If the insertion preserved
the size of the slack weight, the 2025 Banks--Shparlinski ternary machinery would become relevant
to the signed Mertens antidiagonal.

## Exact inversion-cost theorem

Write `*` for Dirichlet convolution, `1(n)=1`, and `id(n)=n`.

**Theorem.** For arithmetic functions `h_0,h_1`,

\[
 1=\mu*h_0 \quad\Longleftrightarrow\quad h_0=\tau,
 \qquad
 \operatorname{id}=\mu*h_1 \quad\Longleftrightarrow\quad h_1=\sigma_1.
\tag{1}
\]

Consequently both exact inverse weights are nonnegative and

\[
 \sum_{n\le X}h_0(n)\ge X,
 \qquad
 \sum_{n\le X}h_1(n)
   =\sum_{n\le X}\sigma_1(n)
   \ge \frac{X(X+1)}2.
\tag{2}
\]

**Proof.** The constant function `1` is the Dirichlet inverse of `mu`, because
`mu * 1 = epsilon`.  Convolving either proposed identity with `1` makes the solution unique:

\[
 h_0=1*1=\tau,
 \qquad
 h_1=1*\operatorname{id}=\sigma_1.
\]

Nonnegativity is immediate.  The second lower bound follows termwise from
`sigma_1(n) >= n`.  This proves (1)--(2).

Applied to the linear slack weight, (1) gives the exact identity

\[
 t=\sum_{de=t}\mu(d)\sigma_1(e),
\tag{3}
\]

and hence

\[
 U(N)=\sum_{r+s+de=N+1}
       \mu(r)\mu(s)\mu(d)\sigma_1(e).
\tag{4}
\]

Equation (4) does create a third Möbius factor, but the unique companion weight has quadratic
summatory mass.  There is no alternate signed inverse with lower `l1` cost: uniqueness in (1)
rules it out.

## Why the best located ternary theorem does not cross the wall

Banks--Shparlinski bound sums of `mu(n1 n2 n3)` on broad three-variable equations by the trivial
scale times an arbitrary logarithmic saving.  Their paper explicitly states that binary analogues
remain out of reach.  In (4), summing a uniform fixed-`e` ternary bound against `sigma_1(e)` pays
at least the quadratic mass in (2).  A logarithmic saving cannot recover the full power of `N`
between the cubic unsigned antidiagonal scale and `OPEN-SOURCE-001`'s quadratic scale.

There is a second mismatch: their cancellation is carried by the Möbius weight of the third
variable.  Multiplying that variable by the extra Möbius factor needed to make the slack
unweighted removes the very cancellation their theorem exploits.

## 2026 direct-convolution collision

Cantarini--Gambini--Zaccagnini study

\[
 S^*(n)=\sum_{r+s=n}\mu(r)\mu(s)
\]

and the continuous second-Cesàro convolution

\[
 C_\mu(x)=\sum_{n\le x}S^*(n)(x-n)
          =\int_0^x M(y)M(x-y)\,dy.
\]

Their explicit zero-pair formula for `C_mu` assumes RH and simple zeros.  Its leading zero-pair
terms have exponent `rho_1+rho_2+1`, exactly matching the corpus zero-abscissa law and the
quadratic critical exponent on RH.  It therefore confirms sharpness and literature proximity; it
does not provide an unconditional upper source.

## Verdict

`FAILED`.  Exact Dirichlet insertion of an unweighted or linearly weighted slack variable has a
unique positive divisor weight whose mass erases the required power saving.  This is a classical
Dirichlet-convolution fact, not publication-level novelty and not progress toward RH by itself.

## Positive survivor

The useful survivor is a precise routing rule:

> Any viable ternary lift must create its extra signed variable geometrically or through a
> cancellation-preserving identity; Dirichlet inversion of the tent slack cannot do so.

The remaining route is cutoff-dependent, all-prime cancellation in the odd-seed tent sum.  Known
entropy-decrement results give logarithmically averaged two-point decorrelation, while the source
requires a pointwise power-scale bias of order `N^-1` relative to unsigned tent mass.  No transfer
between these scales has been proved.

## Primary literature

- W. D. Banks and I. E. Shparlinski, *Multiple sums with the Möbius function*, arXiv:2506.08787.
- M. Cantarini, A. Gambini, and A. Zaccagnini, *On the discrete convolution of the Liouville and
  Möbius functions*, arXiv:2603.10241.
- T. Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
  correlations*, arXiv:1509.05422.

## Re-entry condition

Reopen only with one of:

1. a third-variable theorem allowing an arbitrary compensating weight with a power saving that
   survives the `sigma_1` mass;
2. a non-Dirichlet exact insertion whose total variation is `O(X^(1+epsilon))` for linear slack;
3. a cutoff-pointwise entropy decrement yielding a polynomial, rather than logarithmic, parity
   bias for the actual Möbius source.

