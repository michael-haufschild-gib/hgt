# Completed prime--Gamma Hankel far-right anchor

- **ID:** `completed-prime-gamma-hankel-far-right-anchor`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean status:** Fully formalized unconditionally.  The scalar asymptotic `(7)`, signed Hilbert
  limit positivity, determinant limit `(9)`, exact exponent `2n^2-n`, and eventual strict
  positivity are closed in Lean.  No RH, zero-location, nonvanishing, or winding hypothesis enters
  the far-right theorem.
- **Statement:** Every fixed leading determinant of the moving completed
  prime--Gamma odd-derivative moment matrix is strictly positive sufficiently far to the right,
  with an explicit Hilbert-moment asymptotic.  At the centre the same determinant is the existing
  prime--Gamma/Xi determinant.

## Source-defined moving moments

Let

\[
L(s)=\frac{\xi'(s)}{\xi(s)}
\]

and, away from the Xi divisor, define

\[
c_k(s)=\frac{(-1)^k}{(2k+1)!}L^{(2k+1)}(s).
\]

For `n>=1`, set

\[
\Delta_n(s)=\det[c_{i+j}(s)]_{0\le i,j<n}.
\]

These functions use the completed logarithmic source and no zero enumeration.  On the Euler
half-plane they split into the von Mangoldt, Gamma, and polar derivative channels through the
existing completed-source identity.

At `s=1/2`, the affine coordinate `z -> 1/2+iz` and the normalized divided difference give

\[
c_k(1/2)=\operatorname{analyticTraceMoments}
 \bigl(\operatorname{normalizedTraceMomentGerm}
       (\operatorname{continuedPrimeArchSourceRelativeTrace}),k\bigr).
\]

Consequently,

\[
\Delta_n(1/2)=\det(\texttt{primeArchSourceMomentHankelMatrix }n).
\]

The existing Lean criterion therefore gives

\[
\bigl(\forall n,\ \Delta_n(1/2)>0\bigr)\iff RH.
\]

## Far-right asymptotic target

The completed logarithmic derivative has the source decomposition

\[
L(s)=\frac1s+\frac1{s-1}-\frac12\log\pi
     +\frac12\psi(s/2)+\frac{\zeta'(s)}{\zeta(s)}.
\]

For each fixed `k`, the Gamma channel is dominant:

\[
c_k(s)sim
\frac{(-1)^k}{2(2k+1)s^{2k+1}}
\qquad(s\to+\infty).
\]

The polar derivatives are smaller by one power of `s`; the von Mangoldt derivatives are
exponentially small.  Hence the candidate determinant asymptotic is

\[
s^{2n^2-n}\Delta_n(s)longrightarrow
\det\left[\frac{1}{2(2(i+j)+1)}\right]_{0\le i,j<n}>0.       \tag{1}
\]

The limit matrix is positive definite because

\[
\frac{1}{2(2(i+j)+1)}
=\frac12\int_0^1 t^{2i}t^{2j}\,dt.
\]

The alternating signs in `c_(i+j)` are a diagonal congruence and do not change its determinant.
Thus `(1)` proves `Delta_n(s)>0` for all sufficiently large real `s`, separately for every
fixed `n`.

## Proof of the far-right theorem

Fix `k` and put `q=2k+1`.  On the positive real axis the standard polygamma series is

\[
\psi^{(q)}(x)=q!\sum_{r\ge0}(x+r)^{-(q+1)}.                       \tag{2}
\]

For the positive decreasing function `t -> (x+t)^(-(q+1))`, integral comparison gives

\[
\frac{1}{q x^q}
\le \sum_{r\ge0}(x+r)^{-(q+1)}
\le \frac{1}{x^{q+1}}+\frac{1}{q x^q}.                          \tag{3}
\]

Therefore

\[
x^q\psi^{(q)}(x)\longrightarrow(q-1)!.                          \tag{4}
\]

Since the Gamma contribution to `L` is `psi(s/2)/2`, the chain rule and `(4)` give

\[
s^q\frac{d^q}{ds^q}\left(\frac12\psi(s/2)\right)
\longrightarrow\frac{(q-1)!}{2}.                               \tag{5}
\]

The `q`th derivatives of `1/s` and `1/(s-1)` are `O(s^(-(q+1)))`.  The constant
`-(log pi)/2` disappears.  For the Euler term, termwise differentiation on `s>1` gives

\[
\frac{d^q}{ds^q}\frac{\zeta'(s)}{\zeta(s)}
=\sum_{m\ge2}\Lambda(m)(\log m)^q m^{-s}.                       \tag{6}
\]

The first-coefficient Dirichlet-series asymptotic gives `O(2^(-s))`, so `(6)` is
`o(s^(-q))`.  Combining `(5)`--`(6)` and dividing by `q!` proves

\[
s^{2k+1}c_k(s)\longrightarrow\frac{(-1)^k}{2(2k+1)}.            \tag{7}
\]

For the `n x n` determinant, factor `s^(-2i)` from row `i`, `s^(-2j)` from column `j`, and
`s^(-1)` from every row.  The total extracted power is

\[
n+2\sum_{i<n}i+2\sum_{j<n}j=2n^2-n.                             \tag{8}
\]

Equation `(7)` and continuity of the finite determinant then give

\[
s^{2n^2-n}\Delta_n(s)\longrightarrow
\det\left[\frac{(-1)^{i+j}}{2(2(i+j)+1)}\right]_{i,j<n}.         \tag{9}
\]

Conjugating the matrix in `(9)` by `diag((-1)^i)` removes its alternating signs.  The remaining
matrix is the Gram matrix of the linearly independent functions `t^(2i)/sqrt(2)` in
`L2([0,1])`, hence is positive definite and has positive determinant.  This proves `(1)` and
eventual strict positivity.  `QED`

## Proof of the centre identity

Near the centre the existing source identity is

\[
T(z)=\operatorname{continuedPrimeArchSourceRelativeTrace}(z)
=\frac{d}{dz}\log\Xi_C(z)
=iL(1/2+iz).                                                   \tag{10}
\]

The normalized moment germ is `-T(z)/z`, analytically continued at zero.  Since `T` is odd,
its `z^(2k)` coefficient after normalized division is

\[
-\frac{T^{(2k+1)}(0)}{(2k+1)!}
=-\frac{i^{2k+2}L^{(2k+1)}(1/2)}{(2k+1)!}
=c_k(1/2).                                                     \tag{11}
\]

Taking real parts agrees with `analyticTraceMoments`; the values are real by Schwarz reality.
Thus the moving matrix at `1/2` is entrywise the existing
`primeArchSourceMomentHankelMatrix`, proving the displayed centre identity.  `QED`

## Why the Gamma channel is load-bearing

`EulerNormalizedTraceHankelFarRight.lean` proves that the actual von Mangoldt contribution has a
negative first nontrivial normalized determinant far right:

\[
2^{2s}D_E(s)\to-7(\log2)^8/360.
\]

The completed determinant can nevertheless have the positive asymptotic `(1)` because the Gamma
channel decays polynomially and its limiting Hilbert moment matrix is strictly positive.  This is
the exact source interaction that strict Euler Laplace positivity alone cannot see.

## Top-down chain exposed by the anchor

Every degree now has a canonical positive source endpoint on paper.  The remaining chain is

```text
completed prime--Gamma far-right determinant anchor                         [Lean]
  + exact reflection, holomorphy off Xi, and Schwarz reality                 [Lean]
  + source exclusion of noncentral odd-order real zeros                      [OPEN CORE]
  + nonvanishing at s=1/2                                                     [OPEN CORE]
  -> Delta_n(1/2)>0 for every n                                               [SIGN TRANSFER]
  -> RH.                                                                      [Lean]
```

The reflection theorem is formalized in
`CompletedPrimeGammaMovingHankelReflection.lean`; it supplies the matching far-left anchor and
reduces independent continuation control to the right half-line.  The full complex coefficient
surface and the explicit holomorphic logarithmic-derivative determinant are formalized in
`CompletedPrimeGammaMovingComplexHankel.lean`.

Complete zero exclusion is stronger than necessary.  Once the explicit determinant is used, the
sharp continuation target is exclusion of odd-order real determinant zeros on the right half-line,
together with nonvanishing at the center.  Even-order zeros touch the boundary of the positive
chamber without reversing its orientation.  The source-side odd-order exclusion remains open; it
must come from the completed prime--Gamma decomposition rather than from an RH-equivalent sign or
zero-location assumption.

There is now a sharper scalar consumer.  For every nonzero polynomial `P`, the moving quadratic
test `Q_P(s)=sum_k [X^k]P^2 c_k(s)` has a positive far-right anchor: if `r` is the lowest nonzero
degree of `P`, then `(s^(4r+1)) Q_P(s)` tends to `a_r^2/(2(4r+1))`.  Transporting finite even-root
factorizations of these countably many scalar tests forces central nonnegativity and hence RH.
Because nonnegativity is the consumer, a central even zero is allowed and no central-nonvanishing
theorem is needed.  This route is tracked in
`completed-prime-gamma-polynomial-even-factorization-to-rh.md` and formalized at the interface in
`CompletedPrimeGammaMovingPolynomialParity.lean`.

## Lean tasks

- [x] define the moving completed-source moment germ and determinant in Lean
- [x] prove the centre identity with `primeArchSourceMomentHankelMatrix`
- [x] prove exact base reflection of the moving germ, matrices, and determinants
- [x] retain the full complex coefficient determinant and prove its exact reflection
- [x] define the explicit odd-logarithmic-derivative determinant and prove holomorphy off Xi zeros
- [x] prove the all-order positive-real polygamma asymptotic
- [x] prove polar derivatives are one power smaller
- [x] reuse von Mangoldt first-coefficient decay for the Euler derivative channel
- [x] prove the determinant limit `(1)` and eventual positivity
- [x] formalize the finite polynomial passage from `(7)` to every scalar far-right anchor
- [x] prove the affine chain-rule center bridge for the explicit determinant in Lean
- [x] prove that finite analytic order at the reflection center is even
- [ ] exclude noncentral odd-order real determinant zeros by a source-side theorem *(downstream
      RH sign-transfer producer, not part of the far-right-anchor theorem)*
- [ ] prove central nonvanishing *(downstream RH sign-transfer producer, not part of the
      far-right-anchor theorem)*
- [x] formalize finite even-factor sign transfer, including a possible central zero

## Gates

- [x] source-pure moving determinant specified
- [x] exact centre consumer identified
- [x] non-circular far-right mechanism isolated
- [x] complete paper proof of `(1)`
- [x] unconditional Lean proof of the centre identity
- [x] unconditional Lean proof of the scalar moment asymptotic `(7)`
- [ ] non-circular winding producer *(downstream research gate; not a premise or conclusion of this
      card's proved far-right theorem)*

## Lean realization

Formal carrier:

- `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMomentFarRightAsymptotic.lean` proves the
  unconditional scalar Gamma/polar/Euler asymptotic `(7)`.
- `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaHankelFarRightAnchor.lean` proves strict
  positivity of the signed Hilbert limit through the exact representation
  `(-1)^k/(2(2k+1)) = (1/2) integral_0^1 (-t^2)^k dt`, entrywise normalized matrix convergence,
  exact diagonal determinant scaling, `(9)`, and eventual positivity of the real part of
  `completedOddLogDerivHankelDet`.

Principal final theorems:

- `completedPrimeGammaFarRightHankelMatrix_posDef`;
- `det_completedOddLogDerivFarRightNormalizedHankelMatrix`;
- `completedOddLogDerivHankelDetFarRightAsymptotic`;
- `completedOddLogDerivHankelDet_ofReal_re_pos_eventually`.

Verification on 2026-08-23:

- `lake build GaloisForLFunctions.RHTower.CompletedPrimeGammaHankelFarRightAnchor` passed;
- `#print axioms` on the new positive-moment, scaling, asymptotic, and eventual-positivity theorems
  reports only `propext`, `Classical.choice`, and `Quot.sound`;
- module is wired into `GaloisForLFunctions.RHTower` without building that umbrella.
