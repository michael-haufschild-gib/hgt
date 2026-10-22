# Simplex Bernstein purity orthogonal-gauge classification

- **ID:** `simplex-bernstein-purity-orthogonal-gauge-classification`
- **Stage:** 1-in-progress
- **Type:** THEOREM / UNIVERSAL CLASSIFICATION LAW
- **Scientific status:** `[NEW SCIENTIFIC KNOWLEDGE — TARGETED PRIORITY SEARCH PASSED]`
- **Statement:** In every dimension and degree, the simplex Bernstein basis is characterized up to
  one orthogonal gauge by a universal nonlinear property: every coefficient-filtered Euclidean
  purity becomes one square under the multi-index signed divided-power transform.  In the natural
  order-triangular positive-diagonal gauge, the Bernstein basis is the unique frame with this
  property.

## Why this is the new main theorem

The previous confocal fixed-point theorem is exact but belongs close to classical focal/support
geometry.  It is retained as an application lemma and is not the paper headline.  The present
theorem is a converse classification of a classical polynomial basis by a nonlinear positive
observation law.  It applies in every simplex dimension and every degree, identifies the complete
moduli space of solutions, and proves uniqueness after the canonical triangular orientation is
fixed.

## Setup

Fix `d,N in N` and put

```text
Lambda_(d,N) = {alpha in N^d : |alpha| <= N},
alpha! = product_j alpha_j!,
x^alpha = product_j x_j^alpha_j,
binom(N,alpha) = N!/[alpha!(N-|alpha|)!].
```

The degree-`N` simplex Bernstein basis is

```text
B_alpha^(N)(x)
  = binom(N,alpha) x^alpha (1-sum_j x_j)^(N-|alpha|),
alpha in Lambda_(d,N).                                  (1)
```

Let `A=(A_(alpha,r))` be the monomial coefficient matrix of an arbitrary full real polynomial
frame `p_alpha`, indexed by the same set:

```text
p_alpha(x)=sum_(r in Lambda_(d,N)) A_(alpha,r) x^r.     (2)
```

For a real coefficient field `m=(m_r)`, filter the monomial coefficient of order `r` by `m_r`:

```text
T_m p_alpha(x)=sum_r A_(alpha,r)m_r x^r,
P_(A,m)(x)=sum_alpha (T_m p_alpha(x))^2.                (3)
```

For a polynomial `q(x)=sum_n q_n x^n` of total degree at most `2N`, define the signed
multi-index divided-power transform

```text
Dq(t)=sum_n (-1)^|n| q_n t^n/n!.                       (4)
```

Finally put

```text
F_(N,m)(t)=sum_(r in Lambda_(d,N)) binom(N,r)m_r t^r/r!. (5)
```

## Master theorem

Let `B` denote the monomial coefficient matrix of the simplex Bernstein basis `(1)`.  For every
real square frame matrix `A` indexed by `Lambda_(d,N)`, the following are equivalent:

1. **Universal purity linearization.**  For every real coefficient field `m`,

   ```text
   D(P_(A,m)) = F_(N,m)^2.                              (UP)
   ```

2. **Bernstein Gram law.**

   ```text
   A^T A = B^T B.                                       (BG)
   ```

3. **Orthogonal Bernstein gauge.**  There is a unique orthogonal matrix `O` such that

   ```text
   A=O B.                                               (OG)
   ```

The Bernstein matrix is invertible.  Therefore the orthogonal gauge is explicitly

```text
O=A B^(-1).                                             (6)
```

If, in addition, `A` is upper triangular with positive diagonal in any linear extension of the
coordinatewise partial order on `Lambda_(d,N)`, then

```text
A=B.                                                    (CG)
```

Thus the simplex Bernstein basis is the unique canonically oriented polynomial frame satisfying
the universal purity law.  Without the orientation, its complete ambiguity is exactly the compact
group `O(#Lambda_(d,N))`; there are no further frames.

The result is affine-simplex invariant: after transport by barycentric coordinates, the same
classification holds on every nondegenerate real `d`-simplex.

## Proof

### 1. Multivariate coefficient formula

For `alpha,r in Lambda_(d,N)`, expansion of the last factor in `(1)` gives

```text
[x^r]B_alpha^(N)
 = 0,                                                   alpha not <= r,
 = (-1)^(|r|-|alpha|) binom(N,r)
     product_j binom(r_j,alpha_j),                      alpha <= r.       (7)
```

Indeed the coefficient of `x^(r-alpha)` in
`(1-sum_j x_j)^(N-|alpha|)` is

```text
(-1)^(|r|-|alpha|)
 (N-|alpha|)!/[(r-alpha)!(N-|r|)!],
```

and multiplication by `N!/[alpha!(N-|alpha|)!]` gives `(7)`.

### 2. The simplex Bernstein Gram kernel

Taking the Euclidean inner product of columns `r,s` of `B`, the signs in `(7)` combine to
`(-1)^(|r|+|s|)`.  The remaining finite sum factors coordinatewise.  Vandermonde's identity in
each coordinate gives

```text
(B^T B)_(r,s)
 = (-1)^(|r|+|s|) binom(N,r)binom(N,s)
     product_j binom(r_j+s_j,r_j).                     (8)
```

The restriction `|alpha|<=N` is automatic in the sum because `alpha<=r` and `|r|<=N`.

Since

```text
product_j binom(r_j+s_j,r_j)=(r+s)!/(r!s!),             (9)
```

the divided-power multiplier in `(4)` turns `(8)` into the rank-one kernel

```text
(-1)^|r+s| (B^T B)_(r,s)/(r+s)!
 = [binom(N,r)/r!][binom(N,s)/s!].                     (10)
```

Expanding `(3)` and grouping the monomial of order `r+s`, equation `(10)` proves

```text
D(P_(B,m))=F_(N,m)^2                                   (11)
```

for every `m`.

### 3. The converse is Gram rigidity

Assume `(UP)`.  Polarize the equality in the coefficient variables `m`, or equivalently compare
the coefficient of `m_r m_s t^(r+s)`.  For all `r,s`, this gives

```text
(-1)^|r+s| (A^T A)_(r,s)/(r+s)!
 = [binom(N,r)/r!][binom(N,s)/s!].                     (12)
```

The right side is the Bernstein value `(10)`, so `(12)` is exactly `(BG)`.  Conversely `(BG)`
makes every quadratic coefficient in `(3)` equal to its Bernstein value, and `(11)` proves
`(UP)`.

### 4. Orthogonal gauge classification

Choose a linear extension of coordinatewise order.  Formula `(7)` makes `B` upper triangular,
with diagonal

```text
B_(r,r)=binom(N,r)>0.                                  (13)
```

Thus `B` is invertible.  Under `(BG)` define `O=AB^(-1)`.  Then

```text
O^T O
 = B^(-T)A^T A B^(-1)
 = B^(-T)B^T B B^(-1)
 = I.                                                   (14)
```

Hence `O` is orthogonal and `A=OB`.  Since `B` is invertible, `(6)` proves uniqueness.  Conversely
every orthogonal `O` preserves `A^T A`, so every orthogonal gauge satisfies `(UP)`.

If `A` is also upper triangular with positive diagonal, `(BG)` says that `A` and `B` are two
positive-diagonal upper Cholesky factors of the same positive-definite Gram matrix.  Cholesky
uniqueness gives `A=B`.  This proves `(CG)`.

An affine change from the standard simplex to an arbitrary nondegenerate simplex transports the
monomial coefficient filter through barycentric coordinates and does not alter the row-space
Euclidean purity.  The classification therefore holds on every affine simplex.

## Exact novelty boundary

The following are parents and are not claimed as new:

- the simplex Bernstein basis and its multinomial expansion;
- coordinatewise Vandermonde identities;
- equality of full-rank real Gram matrices up to an orthogonal transformation;
- uniqueness of the positive triangular Cholesky factor;
- pointwise orthogonality identities for multivariate Bernstein polynomials due to
  Jetter--Stoeckler and their descendants.

The new theorem is the converse conjunction `(UP) <-> (BG) <-> (OG)`, for every simplex dimension
and degree, and the resulting canonical-gauge characterization `(CG)`.  Targeted searches through
July 2026 found work on Bernstein mass matrices, pointwise derivative orthogonality, dual bases,
Bernstein frames, total positivity, and multivariate Bernstein--Vandermonde factorizations, but no
classification of polynomial frames by universal coefficient-filtered purity linearization and no
orthogonal moduli theorem of the form above.

## Formalization plan

1. Build the general finite Gram/orthogonal-gauge equivalence once in `HTGeometry`.
2. Define the finite simplex multi-index type and its coordinatewise order.
3. Prove the coefficient formula `(7)` and product Vandermonde identity `(8)`.
4. Formalize the divided-power purity identity `(11)`.
5. Formalize the converse by basis-vector polarization, then the orthogonal gauge and canonical
   triangular uniqueness.
6. Audit axioms and run one focused module build only after the complete theorem batch is ready.

## Literature checked

- K. Jetter and J. Stoeckler, *An identity for multivariate Bernstein polynomials*, Computer
  Aided Geometric Design 20 (2003), 563--577.
- T. D. Do and S. Waldron, *Multivariate Bernstein operators and redundant systems*, Journal of
  Approximation Theory 192 (2015), 215--233.
- L. Lu, *Gram matrix of Bernstein basis: Properties and applications*, Journal of Computational
  and Applied Mathematics 280 (2015), 37--41.
- L. Allen and R. C. Kirby, *Structured inversion of the Bernstein--Vandermonde matrix*, 2020.
- E. Mainar, J. M. Pena, and B. Rubio, *Total positivity and accurate computations with Gram
  matrices of Bernstein bases*, Numerical Algorithms 91 (2022), 841--859.

