# PA9 Turan Ratio Has A Universal Newton Floor

- **ID:** pa9-turan-newton-floor
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), proof-route normalization correction
- **Source:** random formula-graph node 34/100, `PA9` in `docs/consolidated/revision01/formulas-graph.md`
- **Statement:** For any Laguerre-Polya / elementary-symmetric coefficient sequence coming from positive divisor atoms, the Turan ratio

```text
g_n = a_n^2/(a_{n-1}a_{n+1})
```

has the universal Newton floor

```text
g_n >= (n+1)/n.
```

Therefore the PA9 observation `g_n - 1 ~ c/n` contains a forced `1/n` contribution before any xi-specific positivity information appears. The source-specific PA9 margin is the de-biased residual

```text
g_n / ((n+1)/n) - 1,
```

or, to first order, `n(g_n-1)-1`.

## Goal

Correct the interpretation of PA9. The raw normalized Turan margin is scale-free, but it is not yet source-specific. A unit amount of the observed `1/n` decay is forced by Newton's inequalities for any positive elementary-symmetric coefficient sequence. The proof-route should not treat the raw constant in `n(g_n-1)` as a completed-divisor margin.

## Gates

- [x] 0 -> 1 in-progress: random formula selected and checked against existing Turan/no-margin corpus
- [x] 1 -> 2 fully-proven: Newton-floor proof complete
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: fold into the Jensen/Turan normalization notes

## Proof

[PROVED HERE]

Let `x_1,...,x_N >= 0`, and let `e_n` be the elementary symmetric polynomials in these variables. Newton's inequalities in normalized form give

```text
(e_n / binom(N,n))^2
  >= (e_{n-1} / binom(N,n-1)) (e_{n+1} / binom(N,n+1)).
```

Rearranging,

```text
e_n^2/(e_{n-1}e_{n+1})
  >= binom(N,n)^2 / (binom(N,n-1)binom(N,n+1))
  = ((n+1)/n) ((N-n+1)/(N-n)).
```

Now let an infinite positive divisor atom sequence have finite elementary symmetric coefficients `a_n=e_n(x_1,x_2,...)`. Apply the finite inequality to the first `N` atoms and let `N -> infinity`. The coefficients `e_j^{(N)}` converge to `a_j` for each fixed `j`, and

```text
((n+1)/n) ((N-n+1)/(N-n)) -> (n+1)/n.
```

Thus

```text
g_n = a_n^2/(a_{n-1}a_{n+1}) >= (n+1)/n.
```

This applies to the Laguerre-Polya / RH-side reading of `Xi` coefficients, where the coefficients are elementary symmetric functions of positive reciprocal zero-square atoms.

## Route Consequence

PA9's raw no-margin display

```text
g_n - 1 ~ c/n
```

should be split into

```text
g_n - 1
  = 1/n + source_residual_n + lower-order terms.
```

The first term is universal Newton/binomial geometry. The residual

```text
g_n / ((n+1)/n) - 1
```

is the part that can carry xi-specific information. A Turan/Jensen experiment that reports only `g_n-1` or `n(g_n-1)` overstates the available source-built positivity margin by including the universal floor.

This does not weaken the PA9 no-margin message. It sharpens it: after removing the floor, the residual margin is smaller and still decays, so the uniform Jensen/Turan apex has even less spare margin than the raw PA9 line suggests.

## Computation

The script recomputes the first Xi Maclaurin coefficients and prints both the raw and floor-divided margins:

- `computations/2026-06-21-conway-pa9-newton-floor.py`
- `computations/2026-06-21-conway-pa9-newton-floor.txt`

For the tested range, `n(g_n-1)-1` is positive and slowly rising from about `0.15` to `0.36`, while the floor-divided residual is only a few percent by `n=15`.

## Log

- 2026-06-21 -- Conway: created from random formula-graph node 34/100 (`PA9`). Prior work already had the raw Turan no-margin trend; this card isolates the universal Newton component that must be divided out before treating PA9 as source-specific evidence.
