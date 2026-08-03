# Finite prime aperture leaves an infinite radial divisor tail

- **ID:** `ccm-prime-shift-radial-index-separation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** the exact CCM dilation identity, the logarithmic-aperture shift cutoff, and
  the von Mangoldt divisor identity
- **Statement:** Cutting prime shifts at `q<=lambda^2` does not cut radial indices at
  `k<=lambda^2`. After exact divisor reindexing, every radial index remains and carries the
  truncated divisor weight `a_lambda(k)=sum_(q|k,q<=lambda^2)Lambda(q)`.

## Exact decomposition

Let

```text
B_lambda(s)=sum_(n>=1)H_(lambda,n)(s),
G_lambda(j,k)=inner(H_(lambda,j),H_(lambda,k)),                   (1)
```

with the exact dilation law

```text
H_(lambda,n)(s+log q)=sqrt(q)H_(lambda,q*n)(s).                  (2)
```

The positive-prime-shift part of the finite-aperture radial form is

```text
P_lambda^rad
 =-2 sum_(2<=q<=lambda^2)Lambda(q)q^(-1/2)
    inner(B_lambda,B_lambda(.+log q)).                           (3)
```

Insert `(1)`--`(2)`:

```text
P_lambda^rad
 =-2 sum_(2<=q<=lambda^2)Lambda(q)
    sum_(j>=1)sum_(n>=1)G_lambda(j,q*n).                         (4)
```

For `k>=2`, define

```text
a_lambda(k)=sum_(q|k; 2<=q<=lambda^2)Lambda(q).                  (5)
```

Reindexing `k=q*n` gives the exact law

```text
P_lambda^rad
 =-2 sum_(k>=2)a_lambda(k)sum_(j>=1)G_lambda(j,k).               (6)
```

Thus the prime cutoff truncates the divisor weight, not the radial index.

## Cofinal properties of the weight

The classical divisor identity gives

```text
0<=a_lambda(k)<=sum_(q|k)Lambda(q)=log k.                        (7)
```

Moreover,

```text
k<=lambda^2  ->  a_lambda(k)=log k,                              (8)

for fixed k,  a_lambda(k)=log k for all sufficiently large lambda. (9)
```

But `a_lambda(k)` need not vanish for `k>lambda^2`: every multiple `k=q*n` of a visible prime power
`q<=lambda^2` remains present for arbitrarily large `n`.

## Sectors already controlled

The diagonal contribution is

```text
-2 sum_(k>=2)a_lambda(k)G_lambda(k,k).                           (10)
```

The uniform estimate `G_lambda(k,k)/d_1<=C/k^2`, equations `(7)`--`(9)`, and dominated convergence
show that `(10)/d_1` tends to

```text
-16/(11*pi)sum_(k>=2)log(k)/k*arcsin(1/k).                      (11)
```

Likewise, for the nonstationary sector `j,k>=2`, `j!=k`, the exact bound

```text
|G_lambda(j,k)|<=C*d_1/(c*j*k*|j-k|)                            (12)
```

and `(7)` give a total `O(d_1/c)` contribution.

## Exact surviving gate

The only unclosed radial prime term is

```text
E_lambda^tail
 =-2 sum_(k>=2)a_lambda(k)G_lambda(1,k).                         (13)
```

The finite-index theorem
`ccm-exact-finite-aperture-first-row-vanishing.md` controls the subseries `k<=lambda^2`, where
`a_lambda(k)=log k`. It does not control

```text
-2 sum_(k>lambda^2)a_lambda(k)G_lambda(1,k).                     (14)
```

because the radial multiplier `n` in `k=q*n` is unbounded. A complete CCM prime theorem must prove
the positive tail statement

```text
sum_(k>lambda^2)a_lambda(k)G_lambda(1,k)=o(d_1(lambda)),         (15)
```

with the signed or absolute mode of convergence specified in the closed form domain.

`ccm-exact-high-radial-first-row-bv-bound.md` proves the stronger absolute estimate `(15)` by
placing the second factor in Dunster's exterior phase and integrating by parts against a weighted
bounded-variation norm of the pole factor.

## Route correction

The Lean aperture theorem remains exact and useful: it removes prime shifts `q>lambda^2`.
What it cannot do is replace the infinite radial Poisson vector by its first `lambda^2` harmonics.
Consequently, any claimed cofinal radial prime constant or exterior Weil law must retain `(14)`
until `(15)` is proved.

This is a positive structural requirement:

```text
finite prime aperture + infinite radial divisor tail
  -> truncated-divisor weighted first-row theorem.               (16)
```

## Novelty and significance verdict

After removing CCM notation, `(5)`--`(9)` are elementary divisor reindexing. The result is a route
correction, not new scientific knowledge. Its significance is operational: it invalidates the
identification of a prime-shift cutoff with a radial-index cutoff.

## Lean decision

`ApertureShiftCutoff.lean` already formalizes the prime-shift cutoff. The truncated-divisor
reindexing would require finite/infinite summation infrastructure but adds no new mathematical
content. No Lean file is added.

## Gates

- [x] prime-shift and radial indices separated
- [x] exact truncated-divisor weight derived
- [x] diagonal cofinal constant preserved
- [x] nonstationary sector preserved
- [x] high radial first-row tail isolated
- [x] prove the truncated-divisor weighted tail `(15)`
