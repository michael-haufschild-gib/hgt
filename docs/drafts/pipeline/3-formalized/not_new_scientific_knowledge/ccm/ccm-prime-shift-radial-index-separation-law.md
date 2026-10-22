# Finite prime aperture leaves an infinite radial divisor tail

- **ID:** `ccm-prime-shift-radial-index-separation-law`
- **Stage:** 3 — formalized in Lean 4
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

## Lean status

**Superseded, 2026-08-03.**  Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCM/CCMTruncatedDivisorReindex.lean`.  `ApertureShiftCutoff.lean`
covers the prime-shift cutoff and is untouched; nothing is duplicated.

The previous decision judged the reindexing to "add no new mathematical content".  That is true of the
mathematics and irrelevant to the gate: the reindexing is the load-bearing step of the card's
correction, and formalizing it is what certifies that a prime-shift cutoff is *not* a radial-index
cutoff.

- `truncatedDivisorWeight X k` — definition `(5)`, `a_X k = ∑_{q ∣ k, 2 ≤ q ≤ X} Λ q`.
- `truncatedDivisorWeight_eq_filter_le` — the lower restriction `2 ≤ q` is vacuous, since the only
  divisor below `2` is `1` and `Λ 1 = 0`.
- **`sum_shift_eq_sum_truncatedDivisorWeight`** — equations `(4)`--`(6)`, the exact reindexing.  The
  bijection `(q, n) ↦ (q * n, q)` matches visible shift/multiplier pairs with index/divisor pairs;
  this is where the card's `2 ≤ q` restriction earns its keep, since `q = 1` would break injectivity.
- **`truncatedDivisorWeight_nonneg`** and **`truncatedDivisorWeight_le_log`** — equation `(7)`, using
  mathlib's divisor identity `∑_{q ∣ k} Λ q = log k`.
- **`truncatedDivisorWeight_eq_log_of_le`** — equation `(8)`.
- **`truncatedDivisorWeight_eventually_eq_log`** — equation `(9)`.
- `truncatedDivisorWeight_mono` — the weight is monotone in the cutoff, which is the precise sense in
  which raising the prime cutoff only *adds* divisor mass and never removes a radial index.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and not this card's own proofs: the analytic Gram estimates
`G_lambda(k,k)/d_1 ≤ C/k²` and `(12)`, the dominated-convergence evaluation `(11)`, and the tail
bound `(15)`, which the card imports from
`ccm-exact-high-radial-first-row-bv-bound.md`.

## Gates

- [x] prime-shift and radial indices separated
- [x] exact truncated-divisor weight derived
- [x] diagonal cofinal constant preserved
- [x] nonstationary sector preserved
- [x] high radial first-row tail isolated
- [x] prove the truncated-divisor weighted tail `(15)`
- [x] Lean: truncated divisor weight `(5)` and the exact reindexing `(4)`--`(6)` unconditional
- [x] Lean: weight bounds `(7)`, saturation `(8)`--`(9)`, and cutoff monotonicity
