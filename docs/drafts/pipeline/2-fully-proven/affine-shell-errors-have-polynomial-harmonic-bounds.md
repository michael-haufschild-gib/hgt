# Affine shell errors have polynomial harmonic bounds

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement

For each positive conductor and smooth unit-supported profile of positive
mass, there is `K>0` and one horizon such that, simultaneously for every
`c≥1` and every shell-shift family,

`Σ_(n≤N) shiftedReciprocalUpwardRowError(c,N,n)² / log N
 ≤ K c⁶ / √(log N)`.

## Proof

Put `L=log N`, `Y=exp(√L)` and `T=2cY`. The source rate with exponent
two bounds the shell numerator by `A=Cc³/L` when `N/n≥T`.
The global polynomial source bound gives `B=Dc²` everywhere.
The harmonic cutoff estimate bounds the squared row sum by

`A²(1+L)+B²(1+log(2T))`.

For `L≥1`, the first term is at most `2C²c⁶√L`.
Since `1+log(4c)≤4c`, the second is at most
`D²c⁴(4c+√L)≤5D²c⁶√L`. Divide by `L`.
The base source horizon depends only on the fixed conductor and profile;
all overlap and shift choices remain simultaneous.

## Lean status

Formalization follows directly. Supporting actual norm estimate; no
separate contribution count.
