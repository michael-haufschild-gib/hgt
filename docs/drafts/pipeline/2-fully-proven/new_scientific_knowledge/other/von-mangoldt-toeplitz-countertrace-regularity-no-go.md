# Von Mangoldt Toeplitz countertrace has no regular Hilbert realization

- **ID:** `von-mangoldt-toeplitz-countertrace-regularity-no-go`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-SPECIFIC FAILED CLASS
- **Source:** `../../1-in-progress/von-mangoldt-weighted-density-boundary-anomaly.md`
- **Statement:** The canonical Toeplitz countertrace coefficients for the cofinal von Mangoldt
  successor current are unbounded. Hence their Toeplitz kernel defines neither a bounded operator
  on `ell2(N)` nor an operator whose domain contains the finite-support core.
- **RH used:** no
- **Computation used:** no

## Goal

The parent theorem constructs the unique normalized symmetric Toeplitz density

```text
D(i,j)=d_|i-j|
```

whose finite-section pairing with the source Hankel current

```text
H_N(i,j)=m_(i+j+2)
```

is independent of `N`. This is the first source-fixed reader that absorbs the exact positive
jet-opening flux. The unresolved regularity question is whether `D` is an actual bounded or
closable density operator on the standard jet Hilbert space.

The theorem below answers both standard realizations negatively. The finite countertrace remains
an exact algebraic boundary anomaly, but its cofinal limit is necessarily singular.

## The source moments

Write

```text
m_q
 =sum_(n>=2) Lambda(n)/n *
    (log(n+1)^q-log(n)^q),                 q>=1.          (1)
```

These are exactly `vonMangoldtSuccessorRelativeMoment q`. Every term is nonnegative and the sum is
finite.

### Lemma 1: factorial two-sided growth

There are constants `0<c<C<infinity` and `q_0` such that

```text
c q! <= m_q <= C q!                       for q>=q_0.    (2)
```

#### Proof

Use

```text
log(n+1)^q-log(n)^q
 =integral_n^(n+1) q log(x)^(q-1) dx/x.                 (3)
```

Partition the integers into exponential blocks

```text
I_k={n : exp(k)<=n<exp(k+1)}.
```

The prime number theorem in von Mangoldt form gives constants `c_0,C_0>0` and `k_0` such that

```text
c_0 exp(k)
 <=sum_(n in I_k) Lambda(n)
 <=C_0 exp(k)                              for k>=k_0.  (4)
```

On `I_k`, equations `(1)` and `(3)` give absolute constants `c_1,C_1>0` with

```text
c_1 q k^(q-1) exp(-k)
 <=sum_(n in I_k) Lambda(n)/n *
     (log(n+1)^q-log(n)^q)
 <=C_1 q (k+2)^(q-1) exp(-k).                           (5)
```

Indeed, on the lower side use

```text
1/[n(n+1)] >= (1/2) exp(-2(k+1)),   log(x)>=k,
```

and on the upper side use

```text
1/(nx) <= exp(-2k),   log(x)<=k+2.
```

For every integer `r>=0`,

```text
sum_(k>=1) k^r exp(-k) asymp Gamma(r+1)                 (6)
```

with constants independent of `r`. One direct proof compares the `k`th summand with the integral
of `x^r exp(-x)` over `[k,k+1]`; the two comparisons lose at most a factor `exp(1)`. Removing the
fixed initial set `k<k_0` changes the lower estimate by `o(Gamma(r+1))`, and replacing `k` by
`k+2` changes the upper estimate by only an absolute exponential factor. Summing `(5)` and taking
`r=q-1` yields

```text
m_q asymp q Gamma(q)=q!,
```

which is `(2)`. The finitely many initial blocks are bounded by another constant times `q!`.
This proves the lemma. `square`

### Corollary 2: uniform reverse-moment tail

There is `K>0` such that, for all sufficiently large `N`,

```text
sum_(k=1)^N m_(2N+2-k)/m_(2N+2) <= K/(N+2).            (7)
```

Indeed, `(2)` gives, with `q=2N+2` and `1<=k<=N`,

```text
m_(q-k)/m_q
 <=K_0 (q-k)!/q!
 <=K_0/(N+3)^k.
```

Summing the geometric majorant proves `(7)`.

## Theorem: counterweight unboundedness

Let `d_0=1` and let `d_N` be the unique Toeplitz counterweights from the parent recurrence. Then

```text
sup_N |d_N|=infinity.                                  (8)
```

### Proof

The exact opening-cancellation identity, reindexed at stage `N`, is

```text
m_(2N+2)+2 sum_(k=1)^N d_k m_(2N+2-k)=0.               (9)
```

Suppose `|d_k|<=B` for every `k`. Positivity of the moments, `(9)`, and `(7)` imply

```text
1
 <=2B sum_(k=1)^N m_(2N+2-k)/m_(2N+2)
 <=2BK/(N+2).
```

The right side tends to zero, a contradiction. This proves `(8)`. `square`

## Operator consequences

Let

```text
D(i,j)=d_|i-j|.                                        (10)
```

1. **No bounded Toeplitz density.** If the finite sections `D_N` were uniformly bounded in
   operator norm, then every entry would satisfy

   ```text
   |d_k|<=sup_N ||D_N||,
   ```

   contradicting `(8)`. Equivalently, no bounded operator on `ell2(N)` has matrix `(10)`.

2. **No finite-support operator core.** Suppose an operator `T` on `ell2(N)` had every finitely
   supported vector in its domain and matrix coefficients

   ```text
   <e_i,T e_j>=d_|i-j|.
   ```

   The coordinates of `T e_0` would be `(d_i)_i`. Since `T e_0` must belong to `ell2`, this would
   imply `(d_i) in ell2`, hence bounded, again contradicting `(8)`. Therefore the literal Toeplitz
   matrix has no operator realization on the standard finite-support core; in particular it has
   no closable extension originating from that core.

3. **Exact finite anomaly survives.** Every finite density section and its constant source
   pairing remain valid. The no-go concerns cofinal Hilbert regularity, not the algebraic
   countertrace identity.

## No-go closure

- **Exact killing theorem/mechanism:** Factorial source-moment growth makes all lower moments
  negligible in the opening equation if the Toeplitz coefficients are bounded. Exact cancellation
  therefore forces unbounded coefficients.
- **Strongest positive survivor:** The unique Toeplitz countertrace is a canonical singular
  boundary functional on the directed algebra of finite jet sections. Its exact finite and
  pointwise-cofinal laws remain intact.
- **New insight:** The `SR-41` survivor cannot be a bounded weighted marginal, an unbounded
  Toeplitz operator with the ordinary finite-support core, or a regular density on standard jet
  `ell2`. Any joint Gamma--Jacobi coupling must place the countertrace in a rigged/distributional
  boundary space and prove its Euler covariance there.
- **Status:** Dependency-closed paper proof. Prime number theorem and elementary
  sum-integral comparison are parent mathematics. Corpus searches found the recurrence and its
  finite/cofinal coefficientwise laws, but no regularity theorem. Targeted arXiv and broader
  literature searches found general Toeplitz--Hankel operator and moment theory, not this
  von-Mangoldt countertrace no-go. External novelty remains provisional.

## Gates

- [x] 0 -> 1 in-progress: source-pure question and exact falsifier
- [x] 1 -> 2 fully-proven: factorial moment bounds, recurrence contradiction, operator no-go
- [ ] 2 -> 3 formalized: formalize source-moment growth and counterweight unboundedness
- [ ] 3 -> 4 publication-ready: independent PNT/asymptotic audit and specialist priority review

## Log

- 2026-07-27 — proved `m_q asymp q!` from exponential-block PNT bounds and used the exact opening
  recurrence to exclude every bounded counterweight sequence.
- 2026-07-27 — extracted the stronger standard-core no-go: the Toeplitz matrix cannot act on
  `ell2(N)` with `c00` in its domain.
