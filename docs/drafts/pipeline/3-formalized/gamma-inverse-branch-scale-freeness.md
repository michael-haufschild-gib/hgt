# Joint freeness of the factorial scale and inverse-Gamma pole branches

- **ID:** `gamma-inverse-branch-scale-freeness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/GammaInversePoleBranchScaleFreeness.lean`
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Statement:** Let

  \[
    s_n=\frac{(-1)^{n+1}}{n!},\qquad
    \Gamma(-n+s_nB_n(T))=-\frac1T,qquad
    B_n(T)=T+\sum_{j\ge0}b_{n,j}T^{j+2}.
  \]

  In the eventual pole-index germ ring, the family

  \[
    s=(s_n)_n,\quad b_0=(b_{n,0})_n,\quad b_1=(b_{n,1})_n,\ldots
  \]

  is countably algebraically independent over `ℂ`.

## Goal

Coefficient freeness of the inverse branches alone does not separate different derivative weights:
after the pole reparametrization an order-`r` derivative carries `s_n^{-r}`.  Joint freeness with
`s` makes the derivative-weight grading exact, so no polynomial cancellation can exchange a power
of the factorial scale for inverse-branch data.

## Proof

It is enough to prove every finite prefix.  Fix `m`.

### 1. Scale plus harmonic coordinates

The existing factorial-harmonic evaluation theorem is injective on

\[
  \mathbb C(n)(H_n,H_n^{(2)},\ldots,H_n^{(m)})[s_n].
\]

Restricting scalars gives algebraic independence over `ℂ` of

\[
  s_n,H_n,H_n^{(2)},\ldots,H_n^{(m)}.
\]

Equivalently, this follows by identifying a polynomial in the extra scale variable with
`MvPolynomial.optionEquivLeft` and composing it with the injective
`reciprocalSignedFactorialEval`.

### 2. Logarithmic pole coordinates

The order-`j` logarithmic coordinate has the form

\[
  \ell_{n,j}=s_n^{j+1}(\alpha_jH_n^{(j+1)}+\beta_j),\qquad \alpha_j\ne0.
\]

The change

\[
  (s,h_0,\ldots,h_m)\longmapsto
  (s,s(\alpha_0h_0+\beta_0),\ldots,
       s^{m+1}(\alpha_mh_m+\beta_m))

\]

is birational.  After localizing at `s`, its inverse is

\[
  h_j=\alpha_j^{-1}(s^{-(j+1)}\ell_j-\beta_j).

\]

Since `s` is a unit in the pole-index germ ring, this proves joint algebraic independence of `s`
and the logarithmic coordinates.

### 3. Actual unit and inverse-branch coordinates

The complete Bell transform from logarithmic jets to Taylor coefficients of the actual analytic
unit `U_n` is triangular with nonzero diagonal, hence a polynomial automorphism on every finite
prefix.  Multiplicative inversion of `U_n` and compositional inversion of `X/U_n(X)` are
involutions of the universal coefficient algebra.  Extending each automorphism by the identity on
the scale variable preserves injectivity.  Their composite sends the logarithmic coordinates to
the nonlinear coefficients `b_{n,j}` of `B_n` while fixing `s_n`.

Thus every finite family `s,b_0,…,b_m` is algebraically independent.  Algebraic independence is
finitary, so the countable family is algebraically independent.

## Consequence for composition descent

For `w=-1/T` and `z=-n+s_nB_n(T)`, set `q_n(T)=1/B_n'(T)`.  Then

\[
  D_z=s_n^{-1}q_n(T)D_T
      =s_n^{-1}w^2q_n(T)D_w.
\]

Joint scale-branch freeness separates the highest derivative-weight component exactly; branch
freeness then supplies the generic time-change jets which restore the depth-shifted coordinate.

## Formal surface

The Lean module proves the finite weighted scale--harmonic embedding injective without assuming
that the scale is invertible: it factors the variable weighting through diagonal scaling over an
integral domain.  It then lifts the existing Bell, multiplicative-inverse, and compositional-
inverse coordinate maps while fixing the distinguished scale variable.  The exported headline is

```text
algebraicIndependent_gammaPoleScaleAndInverseBranchCoefficientFamily
```

for the `Option ℕ`-indexed family whose head is `reciprocalSignedFactorialGerm` and whose tail is
`gammaInversePoleBranchCoefficientGerm`.

The cached leaf build
`lake build +GaloisForLFunctions.HTGeometry.GammaInversePoleBranchScaleFreeness` passes.  A separate
`#print axioms` audit of the logarithmic, actual-unit, and final inverse-branch theorems reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: exact obstruction and finite-prefix coordinate map isolated
- [x] 1 → 2 fully-proven: birational coordinate proof complete
- [x] 2 → 3 formalized: joint countable theorem in Lean with direct checks and axiom audit
- [ ] 3 → 4 publication-ready: specialist priority audit and integration into the iterate theorem
