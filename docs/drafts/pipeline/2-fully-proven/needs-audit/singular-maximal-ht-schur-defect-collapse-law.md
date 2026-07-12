# Singular maximal-HT carriers are strictly interior at every finite Schur stage and collapse only cofinally

- **ID:** `singular-maximal-ht-schur-defect-collapse-law`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** THEOREM / COFINAL ORIENTATION-DEFECT LAW
- **Lane:** general hypertranscendence; singular Herglotz carriers; Schur geometry
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parents:** `spectral-type-stratified-moment-fiber-maximal-ht.md`,
  `pick-defect-finite-selector-maximal-ht-phase-law.md`
- **Statement:** In every indeterminate Hamburger moment fiber, every infinite-support singular
  spectral chart has a residual maximal full-translation HT phase. For every carrier in that chart,
  the Schur parameters of its Cayley-normalized Cauchy transform satisfy
  `|alpha_n|<1` at every finite stage, while the cofinal product
  `product_n(1-|alpha_n|^2)` equals zero. Equivalently, every finite Toeplitz/Pick defect is strict
  but the normalized determinant collapses only at infinity. The same cofinal defect signature is
  forced conditionally on the oriented Xi source.

## Goal

The finite-selector theorem distinguishes singular finite Pick matrices from positive-defect
levels. It leaves open how a nonrational singular carrier reaches the boundary when every finite
matrix is positive definite. The answer is multiplicative and cofinal.

The new HT law is:

> **A singular maximal-HT carrier can remain strictly inside every finite Schur/Pick aperture while
> its total multiplicative aperture vanishes. Global orientation is an infinite-product phase, not
> a finite singular event.**

## Cayley normalization

Let `nu` be a singular probability measure on `R` with infinite support and Cauchy transform

```text
m_nu(z)=integral_R 1/(x-z)d nu(x).                         (1)
```

Push `nu` to the unit circle by a real-line/disk Cayley transform. Singularity and support
cardinality are preserved. Let `mu_hat` be the resulting probability measure on the circle, let
`F` be its Caratheodory function, and let `f` be its Schur function:

```text
F(w)=integral_(unit circle) (zeta+w)/(zeta-w)d mu_hat(zeta),
F(w)=[1+w f(w)]/[1-w f(w)].                               (2)
```

The transformations between `m_nu`, `F`, and `f` are fixed conformal and fractional-linear maps.
The measure `mu_hat` is singular and has infinite support.

Let

```text
alpha_0,alpha_1,...                                        (3)
```

be the Schur--Verblunsky parameters of `f`, and put

```text
delta_n=1-|alpha_n|^2.                                    (4)
```

## Strict finite defects `[SEARCH]`

Verblunsky's theorem gives the exact finite-stage alternative:

- a measure with `N` support points has `|alpha_j|<1` for `j<N-1` and
  `|alpha_(N-1)|=1`, at which point the Schur algorithm terminates;
- a nontrivial infinite-support measure has

```text
|alpha_n|<1,
delta_n>0                                                   (5)
```

for every `n`.

Thus no finite Schur step of `(1)` is singular. Equivalently, every reduced finite
Caratheodory--Fejer Pick matrix of the complete Taylor germ is positive definite.

## Cofinal defect collapse `[SEARCH + SPECIALIZATION]`

Let `D_N(mu_hat)` be the `(N+1) by (N+1)` Toeplitz Gram determinant of
`1,z,...,z^N` in `L^2(mu_hat)`. Szego recursion gives

```text
D_N(mu_hat)=product_(j=0)^(N-1) delta_j^(N-j).             (6)
```

Szego's theorem gives

```text
lim_(N->infinity) D_N(mu_hat)^(1/N)
 =product_(j=0)^infinity delta_j
 =exp(integral_0^(2pi) log w(theta)d theta/(2pi)),         (7)
```

where `w` is the absolutely continuous density of `mu_hat`.

Since `mu_hat` is singular, `w=0` almost everywhere. The logarithmic integral is `-infinity`, so

```text
product_(j=0)^infinity delta_j=0,
lim_(N->infinity) D_N(mu_hat)^(1/N)=0.                    (8)
```

Equations `(5)` and `(8)` are the infinite-interior law:

```text
delta_n>0 for every finite n,
product_n delta_n=0.                                      (9)
```

No individual finite defect detects the boundary phase. The phase is the vanishing of their
cofinal multiplicative accumulation.

## Residual maximal translation HT in the same phase `[PROVED HERE VIA PARENT]`

Fix any indeterminate normalized Hamburger moment sequence. The spectral-type companion constructs
inside its exact representing-measure fiber:

1. positive charts of infinite pure-point measures;
2. positive charts of singular-continuous measures;
3. more generally, every exact pure-point/singular-continuous mass vector with zero absolutely
   continuous component.

Bounded positive reweighting preserves the singular measure class and infinite support. In every
such chart, a dense residual set of Cauchy transforms has a differentially algebraically
independent full complex translation family.

Every point in these charts satisfies `(9)`, while the residual subset is maximally translation
HT. All points still share the same complete Hamburger moments and the same formal translated
derivative asymptotic germ at upper infinity.

Therefore one exact complete-moment constraint contains residual carriers satisfying simultaneously

```text
maximal full-translation HT,
strict positivity of every finite Schur defect,
zero cofinal defect product,
pure singular spectral type.                              (10)
```

## Cofinal orientation-defect law

> **Within a complete indeterminate moment constraint, singular spectral orientation and maximal
> translation hypertranscendence coexist in an infinite-interior phase: every finite Schur/Pick
> defect is strictly positive, but their Szego product and normalized Toeplitz determinant vanish
> cofinally. The boundary is reached only by the completed infinite constraint.**

This is stronger than saying that finite data do not suffice. It identifies the exact positive
finite quantities, their strict sign, and the multiplicative limit carrying the global phase.

## General HT consequence

Hypertranscendence is compatible with both positive Hilbert geometry and inner boundary behavior.
For singular Herglotz carriers, no finite Schur truncation witnesses a defect: every truncation is
strictly inside the positive cone. The global singular phase resides in the failure of a uniform
multiplicative lower bound.

A proposed finite-stage rigidity argument must therefore distinguish:

```text
pointwise finite positivity: delta_n>0 for each n,
uniform/cofinal positivity: inf_N product_(n<=N)delta_n>0.  (11)
```

The first is compatible with singular maximal HT; the second excludes the cofinal singular phase.

## Conditional Xi law `[PROVED HERE; RH NOT PROVED]`

Let `T=continuedPrimeArchSourceRelativeTrace`. The formal tree proves that anti-Pick orientation of
`T` on the centered upper strip is equivalent to RH and that the Xi divisor is infinite.

Assume orientation only to determine the structure it would force. Conformally map the centered
strip to the disk and Cayley-transform `-T` to a Schur function `f_Xi`. The source has real boundary
values away from its divisor, so `f_Xi` is inner. Under RH, the infinite Xi divisor gives infinitely
many distinct boundary contacts; hence `f_Xi` is nonrational and its associated circle measure is
singular with infinite support.

Its Schur parameters therefore satisfy

```text
1-|alpha_n(Xi)|^2>0 for every n,
product_n(1-|alpha_n(Xi)|^2)=0.                            (12)
```

Thus any oriented Xi carrier is strictly Pick-positive at every finite Schur stage and becomes
singular only in the cofinal product. This refines the previous conclusion that every finite
reduced Xi Pick matrix must be positive definite.

Equation `(12)` does not prove orientation: deriving the Schur inequalities from the fixed
prime--Gamma source is still equivalent in strength to establishing the global anti-Pick sign.
It supplies a new exact target for a source proof and rules out finite singularity as the mechanism.

## Parent-theory and novelty attack

1. `[SEARCH]` The Cayley/Herglotz correspondence, Schur algorithm, Verblunsky theorem, Toeplitz
   determinant factorization, and Szego product theorem are classical.
2. `[SEARCH]` Barry Simon's *OPUC on One Foot*, equations (2.19)--(2.20), (8.1)--(8.5), gives the
   exact normalization used in `(5)`--`(8)`:
   `https://web.ma.utexas.edu/mp_arc/c/05/05-78.pdf`.
3. `[BRIDGE]` Exact singular spectral charts and residual maximal full-translation HT are inherited
   from the spectral-type moment-fiber theorem.
4. `[PROVED HERE]` Their intersection gives `(10)`: maximal translation HT inside the strict-finite /
   zero-cofinal Schur-defect phase, with every moment and formal asymptotic fixed.
5. `[FORMALIZED INPUT + COROLLARY]` Xi source orientation and infinitude of the Xi divisor yield the
   conditional cofinal law `(12)`.
6. `[CANDIDATE RESIDUE]` Preliminary exact searches found no theorem linking residual maximal
   translation differential independence, exact moment-fiber singular strata, strict finite Schur
   defects, and zero Szego product.
7. The theorem remains `[NOVELTY UNVERIFIED]` pending OPUC, moment-problem, and differential-algebra
   specialist audit.

No numerical experiment and no RH assumption enter the general theorem.

## Honest significance score

This strengthens the internal **90/100 candidate** by identifying the first genuinely cofinal
orientation invariant in the route. The wide **72--94** range remains appropriate: the Schur and
Szego mechanisms are classical, the new residue is their interaction with the exact maximal-HT
moment-fiber phase, and Xi orientation is not proved.

## Lean status

No Stage 3 claim is made. Exact formalization requires Cayley transport of measures, circle
Lebesgue decomposition, Schur parameters, Verblunsky recursion, Toeplitz determinants, Szego's
theorem, and the parent residual maximal-HT theorem. These layers are not jointly formalized.

## Gates

- [x] real-line singular measure transported to circle without changing type/support cardinality
- [x] strict interior Schur defects at every finite stage
- [x] Toeplitz determinant factorization fixed
- [x] zero cofinal Szego product proved for singular measures
- [x] residual maximal full-translation HT placed in the same exact phase
- [x] conditional Xi cofinal-defect law scoped without claiming RH
- [x] primary OPUC normalization checked
- [x] preliminary novelty search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [ ] unconditional Lean formalization of the entire theorem

## Log

- 2026-07-12 -- Combined the singular spectral HT charts with Verblunsky/Szego theory. Proved that
  every finite Schur defect is strict while the infinite defect product and normalized Toeplitz
  determinant vanish, and derived the same law conditionally for an oriented Xi source.
