# Gamma--Jacobi artanh positive-log incidence

- **ID:** `gamma-jacobi-artanh-positive-log-incidence`
- **Stage:** 1 — in progress
- **Parent:** `SR-33`, `SR-38`, `SR-41`
- **Type:** explicit source incidence / hostile proof audit
- **Scientific status:** `[CONJECTURE UNDER PROOF] [NOVELTY UNVERIFIED] [NOT RH]`
- **RH used:** no
- **Computation used:** no

## Frontier test

Current source ledger asks for an infinite-rank, off-diagonal incidence from the common
Gamma--Jacobi coordinate to positive prime-log jets.  Corpus already proves separately:

1. the Gamma--Jacobi Fourier feature

   ```text
   a_k(t)=(-1)^k c_(2k+1) phi(t) tanh(t)^(2k+1),
   c_n^2=binom(2n,n)/4^n,
   phi(t)=cosh(t)^(-1/2);
   ```

2. the odd artanh series

   ```text
   artanh(y)=sum_(k>=0) y^(2k+1)/(2k+1),  |y|<1;
   ```

3. `artanh(tanh t)=t`;
4. the successor principal-relative positive-log current.

No corpus theorem composes these data.  Define the first incidence row

```text
B_1(k)=(-1)^k / ((2k+1)c_(2k+1)).                       (1)
```

Then the candidate exact source law is

```text
sum_(k>=0) B_1(k)a_k(t)=phi(t)t.                         (2)
```

The non-formal content is boundedness of this row:

```text
sum_(k>=0) |B_1(k)|^2 < infinity.                        (3)
```

Since `sqrt(n)c_n^2 -> 1/sqrt(pi)`, `(1)` has squared size `O(k^(-3/2))`, so `(3)` should follow
without numerical estimates.  Thus the first positive-log jet is a bounded functional on the
actual common odd Gamma--Jacobi mode Hilbert space, not a fitted finite transform.

At a prime `p`, exact normalization

```text
phi(log p)^2=2p/(p^2+1),
d_p=sqrt((p^2+1)/(2p^2)),
d_p phi(log p)=p^(-1/2)                                 (4)
```

turns `(2)` into `p^(-1/2) log p`; `d_p` is uniformly bounded above and below.  This is the first
row of the source-defined Jacobi-to-positive-log incidence required by `SR-33`.

## Stronger paper target

For every `m>=0`, let `d_(m,n)` be the Taylor coefficient of `artanh(y)^m`.  Same mechanism predicts

```text
B_m(n)=phase(n)^(-1) d_(m,n)/c_n,
sum_n |B_m(n)|^2 < infinity,
sum_n B_m(n) A_n(t)=phi(t)t^m.                           (5)
```

Parity forces `d_(m,n)=0` unless `m=n mod 2`.  A convolution estimate

```text
|d_(m,n)| <= C_m log(n+1)^(m-1)/(n+1)
```

combined with `c_n^2 asymp n^(-1/2)` gives square summability.  Prove `(1)`--`(4)` first; extend to
`(5)` only after direct Lean closure and another collision audit.

## Why this is not yet RH

The full Jacobi row recovers uncensored positive-log jets, whose all-prime norm diverges.  A route
advance requires composing `(5)` with source principal subtraction so head-minus-tail at
`log(n+1),log n` becomes the already proved `SR-40` current in the same Jacobi coordinates, and
then retaining the adaptive odd residual and completed Euler reader.  Equation `(2)` alone closes
one source-incidence row; it does not produce a positive cofinal completion or fibre orientation.

## Collision boundary

- Artanh series, central-binomial asymptotic, Gamma--Jacobi Fourier formula, generic bounded
  `ell2` functional, and positive-log jets are parent/corpus-known.
- Targeted corpus search found no `artanh`/Jacobi/log-jet composition.
- DLMF Meixner--Pollaczek generating functions and standard coefficient asymptotics contain parent
  ingredients, not the source-specific prime-log incidence or `SR-40` head-minus-tail use.
- Novelty claim remains withheld pending proof and broader expert audit.

## Falsifiers

1. row `(1)` is not square summable;
2. Gamma--Jacobi phase or normalization leaves a nonconstant factor in `(2)`;
3. prime correction `(4)` is unbounded;
4. same-source head-minus-tail cannot be expressed before reading target moments;
5. construction merely recovers an existing named incidence after synonym search.

## Gates

- [x] exact formulas selected before divisor or target moment
- [x] whole-corpus synonym collision search
- [x] primary parent-literature calibration
- [ ] paper proof of `(2)`
- [ ] paper proof of `(3)`
- [ ] paper proof of `(4)`
- [ ] unconditional Lean formalization and umbrella wiring
- [ ] source principal-relative composition
- [ ] arbitrary-order extension `(5)`

