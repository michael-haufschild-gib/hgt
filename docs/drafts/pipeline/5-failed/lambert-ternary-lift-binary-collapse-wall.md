# Lambert ternary lift collapses to the binary Möbius source

- **ID:** `mobius-lambert-ternary-collapse-wall`
- **Stage:** 5-failed
- **Type:** FALSIFIED SOURCE MECHANISM; exact bridge/no-go
- **Source:** `OPEN-SOURCE-001` in `../1-in-progress/mobius-additive-frontier-research-ledger.md`
- **Statement:** The Lambert identity inserts a third Möbius factor into the signed Mertens
  antidiagonal with no analytic multiplier cost, but the dilation fibre is exactly Möbius inversion:
  treating it jointly returns the original binary source, while treating it separately makes
  current ternary estimates polynomially too weak.

## Goal

Let

```text
F(z)=sum_(n>=1) mu(n) z^n,
M(a)=sum_(n<=a) mu(n),
U(N)=sum_(a+b=N) M(a)M(b).
```

The attempted escape from the binary frontier was to use the exact Lambert identity

```text
sum_(k>=1) F(z^k)=z                                      (L1)
```

to introduce a third Möbius variable, then apply the ternary estimates of Banks--Shparlinski.

## Exact lift `[PROVED HERE]`

Coefficientwise Möbius inversion proves `(L1)`, because the coefficient of `z^ell` on its left is

```text
sum_(r|ell) mu(r) = 1 if ell=1, and 0 otherwise.         (L2)
```

Also

```text
sum_(a>=0) M(a)z^a = F(z)/(1-z),
U(N)=[z^N] F(z)^2/(1-z)^2.                              (L3)
```

Multiplying `(L3)` by `(L1)` and extracting degree `N+1` gives the exact six-variable law

```text
U(N)=sum_(m+n+kr+i+j=N+1)
       mu(m)mu(n)mu(r),                                 (L4)
```

where `m,n,r,k>=1` and `i,j>=0`.  Before the two slack integrations, the same calculation gives

```text
sum_(m+n=N) mu(m)mu(n)
  = sum_(m+n+kr=N+1) mu(m)mu(n)mu(r).                   (L5)
```

These are formal power-series identities; no convergence or hypothesis is used.

## Exact collapse wall

The new variables `(k,r)` do not create an independent cancellation channel.  On every product
fibre `ell=kr`, their signed weight is exactly `(L2)`.  Therefore any argument that retains the
joint divisor-fibre cancellation reduces `(L4)` back to `(L3)`, coefficient by coefficient.  It
has merely rewritten the binary source.

Conversely, applying a ternary estimate after fixing `k` destroys `(L2)`.  For an equation

```text
m+n+kr=L,
```

the long-interval theorem of Banks--Shparlinski has natural scale

```text
(A+B)R (log R)^(-C),
```

with `A,B` the first two ranges and `R` the third.  In the balanced range this is
`L^2 (log L)^(-C)` before summing the dilation `k`.  Summing `k` costs at least another logarithmic
factor in this direct use, and the two slack variables in `(L4)` add two discrete integrations.
The resulting direct bound has polynomial scale `N^4`, whereas `OPEN-SOURCE-001` requires
`N^(2+epsilon)` for every `epsilon>0`.  Arbitrarily strong fixed logarithmic savings cannot bridge
two missing powers.

There is a second hypothesis mismatch.  Banks--Shparlinski estimate `mu(mnr)` with arbitrary
weights on the first two variables.  Taking squarefree-support weights recovers
`mu(m)mu(n)mu(r)` only on pairwise-coprime triples.  Shared-prime triples are not lower-dimensional:
they require an additional gcd decomposition.  Repairing this costs divisor sums but does not
repair the two-power exponent gap.  Even granting the stronger separate-product version therefore
does not close `(L4)`.

## Hostile audit

1. `(L4)` is not an unconditional estimate for `U`; it is an exact reindexing.
2. Summing `(k,r)` first is circular because `(L2)` restores the binary coefficient exactly.
3. Fixing `k` is noncircular but loses the cancellation that makes the lift useful.
4. Letting the logarithmic exponent `C` depend on `N` is invalid; theorem constants depend on the
   fixed `C`.
5. GRH-strength improvements in the cited ternary theorem still do not create the two missing
   powers, and invoking GRH would defeat the purpose.

## No-go closure

- **Exact killing theorem/mechanism:** fibre identity `(L2)` gives a dichotomy: preserve the
  dilation cancellation and recover the original binary source, or separate the fibres and fall
  two polynomial powers short with current ternary technology.
- **Strongest positive survivor:** exact Lambert ternary-lift laws `(L4)`--`(L5)` and the sharp
  routing rule that a viable third variable must not be a divisor-fibre resolution of the identity.
- **New insight:** the earlier Dirichlet-insertion wall and this dilation-insertion wall exhaust the
  two canonical Möbius inversions of the slack.  The former pays quadratic `sigma_1` mass; the
  latter has zero multiplier cost but collapses coefficientwise to the binary problem.
- **Status:** dependency-closed classical formal-power-series consequence; new to corpus but not
  claimed new to literature.  Lean-ineligible under the admission rule because it does not provide
  a new source theorem or strengthen the RH connector.

## Literature boundary

- W. D. Banks and I. E. Shparlinski, *Multiple sums with the Möbius function*,
  arXiv:2506.08787, especially Theorem 1 and the explicit statement that binary analogues remain
  out of reach.
- Lambert identity `(L1)` is classical Möbius inversion; no novelty claim is made for it.

## Log

- 2026-07-22 — exact lift proved; direct Banks--Shparlinski application audited; route retired.
