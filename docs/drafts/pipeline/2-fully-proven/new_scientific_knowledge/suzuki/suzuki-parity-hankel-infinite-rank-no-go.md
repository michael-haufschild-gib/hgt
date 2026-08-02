# Suzuki parity-Hankel infinite-rank no-go

- **ID:** `suzuki-parity-hankel-infinite-rank-no-go`
- **Stage:** 2-fully-proven; analytic core formalized unconditionally in Lean
- **Type:** THEOREM (paper) / THEOREM (Lean) / FAILED MECHANISM CLASS
- **Scientific status:** `[PROVED HERE] [UNCONDITIONAL] [NO COMPUTATION]`
  `[GENERIC HANKEL ANCESTRY CLASSICAL] [CANDIDATE NEW SUZUKI APPLICATION]`
  `[NOT A SUZUKI NO-GO] [NOT AN RH PROOF]`
- **Statement:** At every positive aperture, Suzuki's literal even and odd restricted-Weil parity
  blocks differ by an infinite-rank Hankel form. In particular, they are never rank-one or
  finite-rank perturbations of one another.

## Goal

Test whether Donoghue/Livšic interlacing for two self-adjoint boundary extensions can be transferred
to the actual parity blocks

```text
Q_even=T_a+H_a,       Q_odd=T_a-H_a
```

by treating their difference `2H_a` as a rank-one or finite-rank perturbation. This identification
would be a powerful source theorem if true. It is false at every aperture.

## Literal parity difference

Parity reduction of Suzuki's even convolution kernel gives

```text
Q_even-Q_odd=2H_a,

H_a(phi,psi)
 =double_integral_(0,a)^2 K(x+y)phi(y)conj(psi(x))dy dx.   (1)
```

For positive lag away from prime-power atoms,

```text
K_reg(t)
 =exp(t/2)-exp(-5t/2)/(1-exp(-2t)).                       (2)
```

Fix any `a>0`. Choose

```text
0<b<a,       2b<log 2.
```

Then `(0,b)^2` contains no prime-power Hankel seam because

```text
0<x+y<2b<log 2.
```

On this entire corner, the compressed parity difference has smooth kernel

```text
2 K_reg(x+y).                                             (3)
```

Thus prime atoms cannot hide or cancel the local rank of the archimedean block.

## Translate-independence theorem

Write

```text
h(z)=exp(z/2)-exp(-5z/2)/(1-exp(-2z)).
```

### Theorem

For every nonempty positive interval `(0,b)`, every finite set of distinct nonnegative real
translates `y_1,...,y_n`, and complex coefficients `c_j`,

```text
sum_j c_j h(x+y_j)=0 for every 0<x<b
    implies
c_1=...=c_n=0.                                           (4)
```

### Proof

Clear the translate denominators with

```text
D(z)=product_k [1-exp(-2(z+y_k))].
```

The relation `(4)` becomes the restriction to `(0,b)` of the entire function

```text
F(z)
 =D(z) sum_j c_j exp((z+y_j)/2)
  -sum_j c_j exp(-5(z+y_j)/2)
      product_(k!=j)[1-exp(-2(z+y_k))].                  (5)
```

The identity theorem gives `F=0` on `C`. Evaluate `(5)` at `z=-y_j`. The first term vanishes
because `D(-y_j)=0`. Every summand in the second term with index different from `j` also contains
the zero factor belonging to `j`. Therefore

```text
0=-c_j product_(k!=j)[1-exp(-2(y_k-y_j))].               (6)
```

Distinct real translates make every factor in `(6)` nonzero, hence `c_j=0`. This holds for every
`j`, proving `(4)`.

## Infinite separation rank

Suppose on `(0,b)^2` that

```text
h(x+y)=sum_(k=1)^r f_k(x)g_k(y).                         (7)
```

Choose `r+1` distinct `y_j` in `(0,b)`. The `r+1` column vectors

```text
(g_1(y_j),...,g_r(y_j))
```

are linearly dependent. A nonzero coefficient vector `c` annihilating them turns `(7)` into a
nontrivial relation

```text
sum_j c_j h(x+y_j)=0,
```

contradicting `(4)`. Therefore `h(x+y)` has no finite separation rank on any nonempty positive
square.

The same conclusion holds for the integral operator. If its range had finite dimension `r`, smooth
columns `h(.-y)` would belong to that closed range: apply the operator to approximate identities
concentrating at `y` and pass to the uniform, hence `L2`, limit. Any `r+1` columns would then be
dependent, again contradicting `(4)`.

By `(3)`, every prime-free corner compression of `H_a` has infinite rank. A compression of a
finite-rank form is finite rank. Hence

```text
rank(H_a)=infinity,
rank(Q_even-Q_odd)=infinity                              (8)
```

for every `a>0`.

## Route-G consequence

The interlacing of spectra for two self-adjoint extensions of one deficiency-one symmetric
operator remains valid parent theory. Equation `(8)` proves that this theorem cannot be transferred
to Suzuki's literal parity restrictions by identifying

```text
T_a+H_a  and  T_a-H_a
```

as rank-one, finite-rank, or finite-codimensional perturbations. They are different objects:
boundary-angle extensions versus infinite-rank parity compressions.

This kills only that proof mechanism. It does not exclude:

- accidental interlacing of the two infinite-rank parity spectra;
- total positivity or variation-diminishing structure of the full restricted-Weil kernel;
- an infinite-rank comparison theorem;
- direct proof of the parity credit/debt budget;
- two-angle meromorphic Livšic/Hermite--Biehler convergence.

Route G remains open.

## Stronger exposed survivor

The exact geometric expansion of the same regular profile proves more than `(8)`: every positive
prime-free corner has infinitely many negative squares and at most one positive square. Thus the
literal parity difference has infinite negative index, excluding finite-index Pontryagin transfer
as well as finite-rank transfer. Paper proof and unconditional finite-Gram Lean are in
`suzuki-parity-hankel-infinite-negative-index.md` and
`SuzukiArchimedeanParityHankelInfiniteNegativeIndex.lean`.

## Novelty audit

Classical content:

- parity decomposition of an even convolution operator into Toeplitz plus/minus Hankel blocks;
- finite-rank Hankel kernels are polynomial-exponential, by Kronecker-type theorems;
- finite-rank operator columns lie in a finite-dimensional range;
- identity theorem for holomorphic functions.

The translate-clearing proof above is an elementary direct specialization of that classical finite
Hankel-rank boundary. It is not claimed as new abstract operator theory.

Primary-source and targeted literature audit:

- Suzuki 2026 proves the finite self-adjoint-extension construction and identifies arithmetic
  control as the missing limit input. It does not identify the literal parity blocks as finite-rank
  perturbations or state their infinite-rank separation.
- Kronecker-type literature classifies generic finite-rank Hankel symbols but does not apply the
  classification to Suzuki's exact regular profile and prime-free aperture corners.
- Targeted searches found no statement of `(8)` or its consequence for the attempted transfer of
  extension-angle interlacing to Suzuki parity spectra.

Candidate novelty is restricted to the exact Suzuki synthesis:

```text
prime-free corner
  + explicit restricted-Weil archimedean profile
  + translate independence
  -> literal parity blocks differ by infinite rank at every aperture
  -> rank-one-extension interlacing is not a parity source theorem.
```

External priority remains unverified.

## Formalization

File:

```text
formal/GaloisForLFunctions/RHTower/
  SuzukiArchimedeanParityHankelInfiniteRank.lean
```

Main declarations:

```text
archHankelProfile
clearedArchRelation
fullDenominator_mul_archTranslatePacket
coeff_zero_real_nodes
clearedArchRelation_eq_zero_of_posReal_lt
archTranslatePacket_coeff_zero_of_posReal_lt
linearIndependent_archHankelKernel_translates_on_posReal_lt
HasPositiveOpenSquareSeparationRankAtMost
archHankelKernel_not_hasPositiveOpenSquareSeparationRankAtMost
```

Verification:

```text
lake env lean \
  GaloisForLFunctions/RHTower/SuzukiArchimedeanParityHankelInfiniteRank.lean
```

passed with no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or computation.

## Status

`[FAILED-CLASS: FINITE-RANK PARITY INTERLACING]`

Positive survivor: any literal parity comparison must be genuinely infinite rank and exploit the
full arithmetic/archimedean Hankel carrier.
