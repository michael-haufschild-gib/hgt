# Rectangular half-density semigroup law

- **ID:** `deninger-rectangular-isogeny-half-density`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/Deninger program.md` · Deninger arithmetic-cohomology construction
- **Statement:** The moving rectangular tangent family has a multiplicative semigroup of
  complex-linear, positive weight-one conformal maps, and the normalized coefficient \(c/r\)
  is forced by the continuous scaling law.

## Goal

Supply a divisor-free local geometric source for the weight-one identity
\(\phi^{t*}g=e^t g\) required by Deninger's Hodge argument.  This is only the local
prime-isogeny atom.  It does not construct the global arithmetic lamination, its orbit
selection, or its cohomology.

## Gates

- [x] 0 → 1  in-progress: exact source-pure statement and hostile boundary
- [x] 1 → 2  fully-proven: complete proof below
- [ ] 2 → 3  formalized: exact tangent/metric theorem in
  `DeningerArithmeticRectangularHalfDensity.lean`
- [ ] 3 → 4  publication-ready

## Frontier

- `[LITERATURE]` Deninger's finite-field solenoid uses a leafwise metric with conformal
  exponent \(1\), and this gives \(\Theta=\tfrac12+S\) on middle leafwise cohomology
  (`Number theory and dynamical systems on foliated spaces`, §5.8).
- `[LITERATURE]` Connes--Consani's absolute-\(\mathbb F_1\) stalk at \(p\) produces the
  rectangular Tate curve with modulus \(i\log(p)/(2\pi)\), its prime longitude, and its
  phase meridian (`On the Absolute Geometry of Spec Z`, §4).
- `[LOCAL-RESEARCH]` The direct Deninger corpus already formalizes the target weight law
  abstractly on completed cohomology.  It does not contain the moving rectangular
  complex-structure/metric atom below.
- **Verdict:** `[BRIDGE] [PAPER-PROVED]`.  The mechanism is elementary and adjacent to
  Deninger's finite-field model; no novelty claim is made.

## Exact theorem

For \(r>0\), put
\[
  E_r=\mathbb C/(\mathbb Z+i r\mathbb Z),\qquad
  J_r(x,y)=(-ry,x/r),\qquad
  g_r((x,y),(x',y'))=\frac{xx'}r+r yy'.
\]
For \(q>0\), let
\[
  A_q(x,y)=(qx,y).
\]
Then
\[
  J_r^2=-1,\qquad A_qJ_r=J_{qr}A_q,
\]
\[
  g_{qr}(A_qv,A_qw)=q\,g_r(v,w),\qquad
  \omega(A_qv,A_qw)=q\,\omega(v,w),
\]
where \(\omega(v,w)=x y'-y x'\), and \(A_{q_1}A_{q_2}=A_{q_1q_2}\).
More generally, let \(c:\mathbb R_{>0}\to\mathbb R_{>0}\) and
\[
  g_r^c=c(r)|dz|^2.
\]
If for every \(q,r>0\)
\[
  A_q^*g_{qr}^c=q\,g_r^c,
\]
then \(c(r)=c(1)/r\).  Thus the half-density normalization is unique up to one
positive constant.

## Proof

In the coordinate \(z=x+i r y\), multiplication by \(i\) is
\((x,y)\mapsto(-ry,x/r)\), proving \(J_r^2=-1\).  The target coordinate after
\(A_q\) is
\[
  qx+i(qr)y=q(x+i r y),
\]
so \(A_qJ_r=J_{qr}A_q\); hence \(A_q\) is complex linear between the two
rectangular complex structures.  Direct bilinear expansion gives
\[
\begin{aligned}
g_{qr}(A_qv,A_qw)
 &=\frac{(qx)(qx')}{qr}+(qr)yy'\\
 &=q\left(\frac{xx'}r+r yy'\right),
\end{aligned}
\]
and
\[
  \omega(A_qv,A_qw)=qx\,y'-y\,qx'=q\,\omega(v,w).
\]
The composition law is immediate.

For the rigidity statement, the pullback law is
\[
  c(qr)q^2=q\,c(r).
\]
Taking the second argument \(r=1\) and the first argument \(q=r\) gives
\[
  c(r)r^2=r c(1).
\]
Since \(r>0\), division by \(r^2\) yields \(c(r)=c(1)/r\).  This closes every
dependency.

## Geometric interpretation

For an integer \(n\geq1\),
\[
  n(\mathbb Z+i r\mathbb Z)=n\mathbb Z+i nr\mathbb Z
    \subseteq \mathbb Z+i nr\mathbb Z.
\]
Thus \(A_n\) descends to
\[
  F_n:E_r\longrightarrow E_{nr},\qquad [z]\longmapsto[nz].
\]
The target lattice modulo the image lattice is \(\mathbb Z/n\mathbb Z\), so this
holomorphic covering has degree \(n\).  This standard quotient interpretation motivates the
promoted tangent theorem; it is not an additional Stage-2 formalization claim.

## Hostile audit

The moving modulus is load-bearing.  On one fixed rectangular elliptic curve,
\([z]\mapsto[nz]\) has degree \(n^2\), not \(n\), and its flat metric scales by
\(n^2\).  Allowing \(r\mapsto nr\) changes the lattice index to \(n\), while
the forced coefficient \(1/r\) changes the metric weight to \(n\).

This theorem does not solve global gluing.  A single compact manifold cannot
carry all prime periods, and a single fixed two-dimensional abelian solenoid
cannot obtain all square-root Frobenius maps from one quadratic endomorphism
algebra.  The surviving representation must use prime-dependent local
holonomy in a non-homogeneous arithmetic groupoid/lamination.

## Log

- 2026-07-26 — `[PAPER-PROVED] [BRIDGE]`; exact proof closed, Lean formalization pending.

## Gate closure (2026-07-31)

Repo-state verification: the "2 → 3 formalized" gate was stale. The named module
`RHTower/Deninger/DeningerArithmeticRectangularHalfDensity.lean` exists, is umbrella-registered, and
covers the exact theorem: `deningerRectangularJ_sq` (J² = −1 on the moving rectangular
tangent plane), `deningerRectangularScale_intertwines_J`, `deningerRectangularMetric_self_pos`
(positivity), `deningerRectangularMetric_scale` (conformal weight q under r ↦ qr),
`deningerRectangularArea_scale`, `deningerRectangularScale_mul` (holonomy group law), and the
rigidity `deningerRectangularCoefficient_eq_const_div` (the 1/r coefficient forced). All
axiom-clean `[propext, Classical.choice, Quot.sound]`. Gate updated:

- [x] 2 → 3  formalized: `DeningerArithmeticRectangularHalfDensity.lean`, verified 2026-07-31

Card moves to `3-formalized/not_new_scientific_knowledge` per its own `[BRIDGE]` /
"no novelty claim" self-grade.
