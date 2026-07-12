# Completed prime--Gamma Hankel far-right anchor

- **ID:** `completed-prime-gamma-hankel-far-right-anchor`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
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
completed prime--Gamma far-right determinant anchor                         [PAPER]
  + source theorem controlling zero winding of Delta_n to s=1/2 for every n [OPEN CORE]
  -> Delta_n(1/2)>0 for every n                                               [Lean]
  -> RH.                                                                      [Lean]
```

The winding theorem must be proved from the completed source decomposition.  Merely assuming
nonvanishing or endpoint positivity would be an RH-strength reformulation.  Before promoting this
as a live RH route, the determinant zero set must be tested structurally: the fixed detour and its
orientation must be source-selected, and the proposed winding control must survive simple
critical-line divisor models.

## Lean tasks

- [x] define the moving completed-source moment germ and determinant in Lean
- [x] prove the centre identity with `primeArchSourceMomentHankelMatrix`
- [ ] prove the all-order positive-real polygamma asymptotic
- [ ] prove polar derivatives are one power smaller
- [ ] reuse von Mangoldt first-coefficient decay for the Euler derivative channel
- [ ] prove the determinant limit `(1)` and eventual positivity
- [ ] test whether a fixed source-selected zero-winding detour can exist without restating RH

## Gates

- [x] source-pure moving determinant specified
- [x] exact centre consumer identified
- [x] non-circular far-right mechanism isolated
- [x] complete paper proof of `(1)`
- [ ] unconditional Lean proof of the anchor and centre identity
- [ ] non-circular winding producer
