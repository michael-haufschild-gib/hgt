# Suzuki parity-Hankel infinite-negative-index classification

- **ID:** `suzuki-parity-hankel-infinite-negative-index`
- **Stage:** 2-fully-proven; finite Gram core formalized unconditionally in Lean
- **Type:** THEOREM (paper) / THEOREM (Lean) / FAILED MECHANISM CLASS
- **Scientific status:** `[PROVED HERE] [UNCONDITIONAL] [NO COMPUTATION]`
  `[INDEFINITE-KERNEL ANCESTRY CLASSICAL] [CANDIDATE NEW SUZUKI APPLICATION]`
  `[NOT A SUZUKI NO-GO] [NOT AN RH PROOF]`
- **Statement:** On every positive prime-free corner, Suzuki's regular parity-Hankel kernel has
  infinitely many negative squares and at most one positive square. Consequently every aperture
  gives the literal parity difference infinite negative index, not merely infinite rank.

## Goal

The infinite-rank theorem excludes rank-one and finite-rank transfer from boundary-angle
interlacing to Suzuki's literal parity blocks. It leaves a stronger possibility: perhaps the
infinite-rank difference has only finitely many negative directions and can still be controlled in
a finite-index Pontryagin space or by a finite-negative-square comparison theorem.

The exact archimedean profile rules this out.

## Signed Gram expansion

On positive lags below the first prime-power seam,

```text
h(t)=exp(t/2)-exp(-5t/2)/(1-exp(-2t)).
```

For `x,y>0`, the geometric series is absolutely convergent and gives

```text
h(x+y)
 =p(x)p(y)-sum_(k>=0) q_k(x)q_k(y),                    (1)

p(x)=exp(x/2),
q_k(x)=exp(-(5/2+2k)x).
```

Thus every finite real Gram quadratic form has the exact decomposition

```text
sum_(i,j) c_i c_j h(x_i+x_j)
 =|P(c)|^2-sum_(k>=0)|Q_k(c)|^2,                       (2)

P(c)=sum_i c_i p(x_i),
Q_k(c)=sum_i c_i q_k(x_i).
```

No limiting spectral assumption enters `(1)` or `(2)`.

## Infinite negative squares

Fix `m>=0` and choose `m+1` distinct positive nodes `x_0,...,x_m` in an arbitrary nonempty
positive interval. The finite negative-moment matrix factors as

```text
[q_k(x_j)]_(0<=k,j<=m)
 = [r_j^k]_(k,j) diag(exp(-5x_j/2)),

r_j=exp(-2x_j).                                         (3)
```

The `r_j` are distinct, so the Vandermonde matrix in `(3)` is invertible.

Let

```text
W_m=ker P subset R^(m+1).
```

Since `P` is one scalar functional,

```text
dim W_m >= m.                                           (4)
```

If `0!=c in W_m`, invertibility of `(3)` implies that at least one of
`Q_0(c),...,Q_m(c)` is nonzero. Equation `(2)` then yields

```text
sum_(i,j) c_i c_j h(x_i+x_j)
 =-sum_(k>=0)|Q_k(c)|^2 < 0.                            (5)
```

Therefore the kernel has at least `m` negative squares on every nonempty positive interval.
Because `m` is arbitrary, its negative index is infinite.

## At most one positive square

Let `W` be any coefficient subspace on which the Gram form is strictly positive. If `P|_W` had a
nonzero kernel vector, `(2)` would make the form nonpositive on that vector. Hence

```text
P|_W is injective,
dim W <= dim R = 1.                                     (6)
```

Combining `(5)` and `(6)`, the exact finite-Gram signature is

```text
positive index <= 1,
negative index = infinity.                              (7)
```

The first inequality need not be equality on every sufficiently small corner.

## Integral-form transfer

Fix an aperture `a>0`. Choose `b` with

```text
0<b<a,       2b<log 2.
```

Every finite set of nodes used above lies a positive distance from zero. Around those nodes choose
pairwise disjoint compact intervals contained in `(0,b)` and smooth unit-mass bumps supported
there. The kernel is uniformly continuous on the resulting compact product.

For a fixed `m`, the Gram form in `(5)` has a strictly negative maximum on the unit sphere of
`W_m`. Shrinking the bump supports makes the integral-form matrix uniformly as close as desired to
the point Gram matrix. Its restriction to the bump image of `W_m` therefore remains strictly
negative. Disjoint supports make the bump map injective. Hence the compression of the Hankel form
to `(0,b)` has negative index at least `m`; `m` is arbitrary.

On every compact subinterval away from zero, `(1)` converges uniformly. Fubini gives the integral
analogue of `(2)`, so the positive-moment functional is injective on every strictly positive
subspace. Its positive index is at most one there.

There is no prime-power Hankel atom on `(0,b)^2`, because `0<x+y<2b<log 2`. Therefore

```text
ind_-(H_a)=infinity,
ind_-(Q_even-Q_odd)=ind_-(2H_a)=infinity.                (8)
```

## Route-G consequence

Equation `(8)` kills more than finite-rank parity transfer. The literal parity difference cannot
be modeled by:

- a finite-rank or finite-codimensional correction;
- a perturbation with finitely many negative squares;
- a finite-index Pontryagin correction carrying the boundary-angle interlacing law.

This is a failed mechanism class, not a no-go for Suzuki's producer. It does not exclude:

- a comparison theorem with genuinely infinite negative index;
- total positivity or variation-diminishing structure after a different source transform;
- direct proof of the parity credit/debt budget;
- the surviving two-angle meromorphic Livšic/Hermite--Biehler limit.

Route G remains open.

## Arithmetic-seam strengthening

The positive-index bound in `(7)` belongs only to a prime-free regular corner. It does not survive
the full arithmetic kernel. Once `a>log(2)/2`, the first-prime atom is a negative weighted
reflection across `x+y=log 2`. Narrow reflected-even and reflected-odd bump packets have opposite
signs, while their regular-kernel error tends to zero. Hence the full cofinal parity difference
has both infinite positive and infinite negative index. See
`suzuki-prime-seam-parity-hankel-strong-indefiniteness.md` and
`SuzukiPrimeSeamParityHankelStrongIndefiniteness.lean`.

## Novelty audit

Classical content:

- geometric-series Gram decompositions;
- Vandermonde independence of distinct exponentials;
- negative-square and Pontryagin-space language;
- localization of continuous kernel Gram matrices by approximate identities;
- generic Hankel sign-function and inertia theory.

Yafaev's sign-function theory already relates positive and negative spectral multiplicities of
general Hankel operators and gives finite-rank inertia formulae. Generalized Nevanlinna theory
already treats kernels with finitely many negative squares. No new abstract theorem in either
theory is claimed.

Targeted primary-source audit:

- Suzuki 2026 constructs the finite self-adjoint-extension framework and leaves the arithmetic
  finite-to-global limit conjectural. It does not state the prime-free parity signature `(7)` or
  `(8)`.
- Yafaev 2013 gives general Hankel sign/inertia machinery but does not apply it to Suzuki's exact
  restricted-Weil profile.
- Targeted searches found no exact statement combining the Suzuki parity reduction, first
  prime-free corner, geometric negative-mode tower, Vandermonde witness, and infinite negative
  index.

Candidate novelty is restricted to this exact synthesis:

```text
Suzuki regular parity profile
  -> one positive exponential square minus full odd half-integer tower
  -> Vandermonde-independent negative moments on every positive interval
  -> signature (<=1,infinity)
  -> finite-index parity-interlacing transfer is impossible.
```

External priority remains unverified.

## Formalization

File:

```text
formal/GaloisForLFunctions/RHTower/
  SuzukiArchimedeanParityHankelInfiniteNegativeIndex.lean
```

Main declarations:

```text
realArchHankelProfile
archPositiveMode
archNegativeMode
hasSum_archNegativeMode_product
realArchHankelProfile_eq_mode_tsum
archKernelGramQuadratic_eq_moments
coeff_eq_zero_of_archNegativeMoment_zero
ArchHankelHasAtLeastNegativeSquaresOn
realArchHankelProfile_hasAtLeastNegativeSquaresOn
archHankel_positive_subspace_finrank_le_one
```

Verification:

```text
lake env lean \
  GaloisForLFunctions/RHTower/SuzukiArchimedeanParityHankelInfiniteNegativeIndex.lean
```

passed with no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or computation.

## Status

`[FAILED-CLASS: FINITE-INDEX PARITY INTERLACING]`

Positive survivor: every viable literal parity comparison must accept an infinite negative-mode
tower. Any successful source theorem must control that full tower arithmetically or transform it
before invoking Hermite--Biehler geometry.
