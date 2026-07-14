# The semilocal Euler kernel is an exact analytic chart of the archimedean Sonin space

- **ID:** `semilocal-euler-kernel-chart-differentiability`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN INTERFACE DISCHARGE]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Connes--Consani, *Quasi-inner functions and local factors*;
  Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*;
  `sonin-place-transition-cutoff-dichotomy.md`;
  `sonin-prime-seam-exterior-factorization.md`

## Setup

Let `H_+` and `H_-` be the Hardy spaces on the right and left of the critical line.  Put

```text
S(u)={f in H_+ : u f in H_-}.                              (1)
```

For the archimedean local-factor ratio `u_infinity=rho_infinity`, this is the Hardy realization
of the classical Sonin space.  Fix a finite set `F` of primes and real parameters `t_p` satisfying

```text
|t_p|<sqrt(p).                                             (2)
```

Define

```text
D_t(z)=product_(p in F)(1-t_p p^(-z)),
N_t(z)=product_(p in F)(1-t_p p^(z-1)),
u_t(z)=u_infinity(z) N_t(z)/D_t(z).                       (3)
```

The usual finite semilocal product is the point `t_p=1` for every `p`.

## Exact kernel chart

`[PROVED]` One has the equality of closed subspaces

```text
S(u_t)=D_t S(u_infinity).                                  (4)
```

Moreover multiplication by `D_t` is a bounded topological isomorphism from
`S(u_infinity)` onto `S(u_t)`.

### Proof

If `Re z>=1/2`, then

```text
|t_p p^(-z)|<=|t_p|/sqrt(p)<1.                             (5)
```

Hence `D_t` and `D_t^(-1)` belong to `H^infinity` of the right half-plane.  Similarly, on
`Re z<=1/2`, both `N_t` and `N_t^(-1)` belong to `H^infinity` of the left half-plane.

If `f in S(u_infinity)`, then `D_t f in H_+` and

```text
u_t D_t f=N_t u_infinity f in H_-,                         (6)
```

so `D_t f in S(u_t)`.  Conversely, if `h in S(u_t)`, put `f=D_t^(-1)h`.  Then

```text
u_infinity f=N_t^(-1)u_t h in H_-,                         (7)
```

so `f in S(u_infinity)` and `h=D_t f`.  This proves `(4)` and bounded invertibility. `QED`

Connes--Consani prove the forward inclusion at the undeformed Euler point.  Their argument already
contains `(6)`.  The inverse Hardy multipliers in `(5)` give the converse.  The later semilocal
theorem of Connes--Consani--Moscovici proves the corresponding Hilbertian isomorphism on the actual
adelic Sonin spaces and computes the same multiplier `D_t` at `t_p=1`.

## Norm-analytic orthogonal projection

Let `Q` be the orthogonal projection of `H_+` onto `S(u_infinity)`, let `M_t` be multiplication by
`D_t`, and let `P_t` be the orthogonal projection onto `S(u_t)`.  Since `M_t` is bounded below on
`S(u_infinity)`, the standard closed-range projection formula gives

```text
A_t=Q M_t^* M_t Q+(1-Q),
P_t=M_t Q A_t^(-1) Q M_t^*.                               (8)
```

For finite `F`, all factors in `(8)` depend real-analytically on the parameters in `(2)`.  Thus
`t |-> P_t` is operator-norm real analytic.  In particular, the norm-differentiability part of the
finite Euler tangent proposal is unconditional; no graph-topology weakening is required for the
**completed semilocal kernel**.

For one prime put `q_p(z)=p^(-z)`.  At the empty Euler point,

```text
partial_p M_t|_0=-M_(q_p),
partial_p P_t|_0
 =(1-Q)(-M_(q_p))Q+Q(-M_(q_p))^*(1-Q).                    (9)
```

Hence its second fundamental form is exactly

```text
(1-Q)(partial_p P_t|_0)Q=-(1-Q)M_(p^(-z))Q.              (10)
```

Equation `(9)` follows by differentiating `(8)` at `M_0=1`, `A_0=1`:

```text
P'_0=XQ+QX^*-Q(X+X^*)Q
    =(1-Q)XQ+QX^*(1-Q),   X=-M_(q_p).                     (11)
```

## The metric tangent is the formalized positive Euler corner

The pullback metric of the semilocal chart is represented before restriction by

```text
M_t^* M_t.
```

On the critical line, `M_(q_p)^*=M_(p^(z-1))`.  Therefore

```text
partial_p(M_t^*M_t)|_0
 =-M_(p^(-z))-M_(p^(z-1)).                                (12)
```

Under the Mellin/logarithmic-coordinate unitary, `(12)` is

```text
-(1/sqrt(p))(U_p+U_p^(-1)).                               (13)
```

The full positive Euler metric multiplier is

```text
|1-p^(-z)|^2
 =1+p^(-1)-p^(-z)-p^(z-1).                               (14)
```

The constant part of `(14)` has zero cross-boundary across `Q`.  Consequently the lower
cross-boundary of the metric tangent `(12)` is exactly the positive Euler Sonin corner, not merely
an analogy or a principal approximation:

```text
(1-Q) partial_p(M_t^*M_t)|_0 Q
 =-(1/sqrt(p))(1-Q)(U_p+U_p^(-1))Q.                       (15)
```

Lean already proves `(15)` in physical coordinates as

```text
centralPositiveEulerCorner_eq_smul
```

and proves that replacing the actual Sonin projection by its formal principal complement changes
the corner by a Hilbert--Schmidt operator.  Thus the operator-identification part of the proposed
finite tangent construction is discharged exactly for the actual corner and modulo
Hilbert--Schmidt operators for the principal corner.

For arbitrary finite coefficients `c_p`, linearity of `(12)` gives a bounded source-defined
section

```text
sum_(p in F)c_p (1-Q) partial_p(M_t^*M_t)|_0 Q.            (16)
```

This is the `finitePositiveEulerCombination` corner of the Lean corpus.  The formal theorem
`finitePositiveEulerCorners_calkinIndependent` proves that `(16)` is compact only when all finite
coefficients vanish.  Together with `XiPrimeSeamEulerZeroTangent.lean`, the scalar Xi seam
coefficients therefore have an exact finite transfer to the faithful Sonin Calkin carrier.

## Local singularity versus completed regularity

The local ratio alone has a singular kernel limit.  For one prime, write

```text
rho_(p,t)(z)=(1-t p^(z-1))/(1-t p^(-z)),
c=log(t)/log(p),
B_(p,t)(z)=sinh(log(p)(z-c)/2)/sinh(log(p)(z+c-1)/2).      (17)
```

For `0<t<=1`, direct algebra gives

```text
rho_(p,t)(z) B_(p,t)(z)=-p^(z-1/2).                       (18)
```

As `t` decreases to zero, `B_(p,t)` tends locally to the singular inner function
`-p^(z-1/2)`, not to `1`.  Thus the kernel projection of the **uncompleted local Hankel operator**
does not furnish the desired empty-parameter tangent.

There is no contradiction with `(8)`: multiplication by the archimedean completion changes the
kernel problem, and the exact denominator chart `(4)` makes the completed semilocal kernel
norm-analytic.  The route must differentiate the completed semilocal chart or its metric, never the
isolated local Hankel kernel.

## What remains open

The result closes three former hypotheses:

```text
finite Euler semilocal kernel chart
  -> operator-norm differentiable projection,
metric tangent
  -> exact actual positive Euler Sonin corner,
finite scalar seam coefficients
  -> finite seam-weighted Sonin section.                  (19)
```

It does **not** make the normal Gram curvature compact.  The noncompactness in Lean proves that no
argument using only the finite place chart can do so termwise.  More decisively, the finite chart
contains no Xi divisor point: compactness on an actual zero fibre must use an additional global
source--divisor value relation.

The Connes--Consani--Moscovici dual place map supplies the exact flat pairing

```text
<theta_S f,eta_S g>=<f,g>.                                (20)
```

Differentiating `(20)` cancels the primal and dual **tangential connection** terms.  After
orthogonal splitting, the desired normal Gram is balanced by that connection; it is not zero for
free.  The sharp remaining source theorem is therefore:

```text
on every actual Xi-zero fibre, the global summation-map/zeta-cycle relation annihilates the
tangential connection term in the polarized second derivative of `(20)`.                 (21)
```

The formal continuation
`../../3-formalized/not_new_scientific_knowledge/cofinite-euler-connection-reader-rigidity.md`
removes the infinite-dimensional part of `(21)`.  A continuous real-bilinear operator reader that
is compact on every cofinite paired Euler-tangent pair is compact on the complete analytic FE-odd
Schwarz source fibre.  Moreover, mixed derivatives of a norm-analytic compact operator family are
compact.  Hence `(21)` no longer requires a global connection estimate: it is enough to prove the
finite exact value relation identifying each prime-pair connection coefficient with the mixed
derivative of the completed finite quasi-inner Hardy block.  The zero-fibre normal-curvature
identity remains open.

If `(21)` is proved modulo compact operators, the normal remainder is the finite two-prime Gram
coboundary already recognized by Lean.  This gives the genuinely top-down chain

```text
[CONJECTURE] Xi-zero radical annihilation of the semilocal tangential connection
 -> finite two-prime Sonin Gram coboundary is compact
 -> every pair of Xi prime-seam charges is equal
 -> the common charge is zero by cofinal prime decay
 -> RH.                                                     (22)
```

Burnol's Sonine/de Branges theory supplies bounded zero-evaluation functionals, including
multiplicity jets, and complete minimal systems indexed by the actual zeta divisor.  Connes's
spectral realization and the later zeta-cycle construction supply the global radical/quotient in
which actual zeros occur.  These are the correct literature inputs for `(21)`.  Neither cited
source identifies their zero-evaluation/radical relation with the semilocal connection in `(20)`;
that identification is the remaining research problem.

## Literature and novelty boundary

- Connes--Consani, *Quasi-inner functions and local factors*, arXiv:2008.10974, proves finite
  quasi-innerness and the denominator inclusion underlying `(6)`.
- Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423, proves the
  actual semilocal Sonin isomorphism, computes the multiplier `D_t` at the Euler point, and proves
  the primal--dual pairing `(20)`.
- Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, arXiv:math/0203120, supplies the zero-indexed bounded evaluation systems in Sonine
  spaces.

The analytic-chart and projection formulas are standard Hardy-space and closed-range operator
theory.  Their synthesis discharges a live RH-route interface but fails the novelty gate as a new
scientific theorem.

## Gates

- [x] exact deformed finite-place kernel chart
- [x] bounded inverse and surjectivity, not merely the known forward inclusion
- [x] operator-norm real analyticity of the semilocal orthogonal projection
- [x] exact second-fundamental-form derivative
- [x] exact metric-tangent identification with the formalized positive Euler Sonin corner
- [x] finite bounded transfer of the scalar Xi seam coefficients to the Sonin section
- [x] isolated-local-kernel singularity separated from completed semilocal regularity
- [x] reduce continuous polarized connection compactness to cofinite prime-tangent pairs
- [x] prove mixed derivatives of norm-analytic compact operator families are compact
- [ ] zero-fibre annihilation of the tangential connection in `(21)`
- [ ] finite two-prime compact curvature extraction
- [ ] prime-seam coherence and RH
