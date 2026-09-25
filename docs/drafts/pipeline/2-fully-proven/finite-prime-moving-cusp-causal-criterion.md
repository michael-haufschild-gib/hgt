# Finite-prime moving-cusp form of the causal theta criterion

- **ID:** L-PSRC-SQB-MOVING-CUSP
- **Stage:** 2-fully-proven (paper theorem; Lean formalization open)
- **Type:** THEOREM (paper; an RH-equivalent finite-source criterion, not an RH proof)
- **Routes:** L, PSRC, SQB
- **Statement:** The causal Möbius–theta boundary observation can be read, to superpolynomial accuracy, from the canonical atom split of one finite prime-deleted theta source at a cusp point moving with the observation scale.

## The finite source and its directed cusp port

Let `k=thetaCuspFullSource`, and let `P_Y` be the product of all primes
`p<=Y`. The finite Euler-deleted source is

```text
k_Y(x) = product_(p<=Y) (1-p^(-1/2) T_(log p)) k(x)
       = sum_(d|P_Y) mu(d)/sqrt(d) * k(x+log d).
```

The **directed positive-ray atom port** at `x=-log N` retains the terms
whose shifted arguments are positive:

```text
B_Y(N) = sum_(d|P_Y, d>N) mu(d)/sqrt(d) * k(log(d/N)).       (1)
```

The direction and the arithmetic atom labels are part of this
observation. The unsplit scalar value `k_Y(-log N)` also includes the
terms `d<=N` and is not (1).

Set `Y_N=N log N` for integers `N>=3`. Then, for every `A>0`,

```text
B_Y_N(N) = B(N) + O_A(N^(-A)),
B(t) = sum_(n>t) mu(n)/sqrt(n) * k(log(n/t)).                (2)
```

Consequently the [causal Möbius--theta criterion](causal-mobius-theta-boundary-criterion.md)
has the entirely finite moving-cusp form

```text
RH  <->  for every epsilon>0, B_Y_N(N)=O_epsilon(N^epsilon). (3)
```

The observation in (3) uses a finite prime set for each `N`; the
prime horizon and cusp position move together. No limit of finite
Green operators or prime-deleted source transforms is assumed.

## Proof

The finite product expansion is the squarefree Möbius identity.
Every integer missing from (1) but present in `B(N)` has a prime
factor larger than `Y_N`, hence is larger than `Y_N`. The explicit
Gaussian theta atom formula used in the causal criterion gives, for
`u>=1`, constants `C,c>0` with

```text
|k(log u)| + |k'(log u)| <= C (1+u)^C exp(-c u^2).          (4)
```

For example, insert
`k(log u)=sqrt(u)*sum_(m>=1) g(m*u)`, where
`g(v)=(4*pi^2*v^4-6*pi*v^2)exp(-pi*v^2)`, and differentiate the
absolutely convergent series. A Gaussian-tail integral bounds the
missing integers by

```text
|B(N)-B_Y_N(N)|
 <= sum_(n>Y_N) n^(-1/2)|k(log(n/N))|
 <= C sqrt(N) (1+log N)^C exp(-c' (log N)^2),              (5)
```

after adjusting positive constants. The last expression is
`O_A(N^(-A))` for every fixed `A`.

The criterion quoted above is stated for all real `t>=1`. It suffices
to check integers. For `N<=t<N+1`, the defining sum has the same
indices as `B(N)`. Differentiating each summand and using (4) shows

```text
|dB(t)/dt| <= (1/t) sum_(n>t) n^(-1/2)
                         |k'(log(n/t))| = O(N^(-1/2)).      (6)
```

The estimate follows by comparison with the integrable Gaussian
profile after `n=t u`. At `t=N+1`, the excluded single term has size
at most `k(0)/sqrt(N+1)`. Thus

```text
sup_(N<=t<=N+1) |B(t)-B(N)| = O(N^(-1/2)).                  (7)
```

Equations (2) and (7) transfer the subpower condition in the causal
criterion to (3), in both directions.

## Quantitative off-line witness

Suppose `rho` is a zeta zero with `1/2<Re rho<1`, and set
`v=Re rho-1/2>0`. The causal criterion proves that the Mellin
transform of `B` has a pole at `w=rho-1/2`, with order equal to the
zero multiplicity. Hence for every `0<delta<v`,

```text
limsup_(N->infinity) N^(-v+delta) * |B_Y_N(N)| = infinity. (8)
```

Indeed, a bound `B_Y_N(N)=O(N^(v-delta))` would give the same bound
for `B(t)` by (2) and (7). Its Mellin integral would then be
holomorphic on `Re w>v-delta`, contradicting that pole. This identifies
the horizontal distance of a hypothetical off-line zero as a forced
power-growth exponent of a finite, source-labelled moving-cusp port.
It does not bound that port from above.

## What this changes

The [prime-deletion mode theorem](sqb-prime-deletion-causal-mode-escape.md)
shows that fixed-cusp local convergence loses a nonzero negative-cusp
radiation trace. Equations (1)--(3) and (8) identify an RH-sensitive
**moving** boundary port of the same finite deletion family. Any
proposed SQB or L source estimate can now be tested on the finite,
labelled port (1).
The mathematical producer still missing is a bound on its signed
cross-prime sum. The Gaussian truncation in (5) pays only for primes
beyond the moving horizon; it gives no cancellation among retained
Möbius coefficients. No computations or Lean builds were used.
