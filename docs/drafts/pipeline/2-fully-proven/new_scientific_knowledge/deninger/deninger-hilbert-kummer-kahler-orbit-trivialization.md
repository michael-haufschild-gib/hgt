# Hilbert--Kummer radius canonically produces complex Kähler orbit leaves

- **ID:** `deninger-hilbert-kummer-kahler-orbit-trivialization`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Labels:** `DAC_EQUIVARIANT_RADIUS_ORBIT_TRIVIALIZATION`,
  `DAC_DENINGER_HILBERT_KUMMER_KAHLER_ORBIT_COLLAR`
- **Parent:** `deninger-hilbert-kummer-radial-flow-poisson`
- **Lean status:** elementary algebraic identities are to be batched with
  `DeningerArithmeticHilbertKummerRadius.lean`; no Lean process was started
  while the shared machine was saturated.

## Abstract equivariant-radius theorem

Let \(X\) be a topological space with a continuous \(\mathbb R\)-action
\(\phi\), and let
\[
  x:X\longrightarrow\mathbb R_{>0}
\]
be continuous and satisfy
\[
  x(\phi^t p)=e^t x(p).                                      \tag{1}
\]
Put \(\Sigma=x^{-1}(1)\).  Then
\[
  \tau:X\xrightarrow{\sim}\Sigma\times\mathbb R_{>0},\qquad
  p\longmapsto
  \bigl(\phi^{-\log x(p)}p,x(p)\bigr)                         \tag{2}
\]
is an \(\mathbb R\)-equivariant homeomorphism, where the action on the
right is
\[
  t\cdot(q,r)=(q,e^t r).                                     \tag{3}
\]
Its inverse is
\[
  \tau^{-1}(q,r)=\phi^{\log r}q.                             \tag{4}
\]

### Proof

Equation `(1)` gives
\[
 x\!\left(\phi^{-\log x(p)}p\right)
 =e^{-\log x(p)}x(p)=1,
\]
so `(2)` lands in \(\Sigma\times\mathbb R_{>0}\).  Equations `(2)` and
`(4)` are inverse by the flow law and \(\log(e^t r)=t+\log r\).
Continuity follows from continuity of \(x,\log\), and the action.  The
same calculation proves `(3)`.

In particular, the action is free: if \(\phi^t p=p\), then `(1)` gives
\(e^t=1\), hence \(t=0\).  When \(X\) is Hausdorff, it is also proper.  If
\((p,\phi^t p)\) ranges in a compact subset of \(X\times X\), both
\(x(p)\) and \(x(\phi^t p)\) range in compact subsets of
\(\mathbb R_{>0}\), and
\[
 e^t=\frac{x(\phi^t p)}{x(p)}
\]
bounds \(t\) in a compact interval.  The inverse image of a compact
set under the action graph is therefore closed in a compact product.

## Canonical half-density circle refinement

Define
\[
 \mathcal L_x^\times
 =
 \{(p,z)\in X\times\mathbb C^\times:|z|^2=x(p)\}.             \tag{5}
\]
It carries commuting actions
\[
\begin{aligned}
 \Phi^t(p,z)&=(\phi^t p,e^{t/2}z),\\
 R_\theta(p,z)&=(p,e^{i\theta}z).
\end{aligned}                                                 \tag{6}
\]
They preserve `(5)` by `(1)`.  There is a canonical homeomorphism
\[
 \mathcal L_x^\times\xrightarrow{\sim}\Sigma\times\mathbb C^\times,
 \qquad
 (p,z)\longmapsto
 \left(\phi^{-\log |z|^2}p,z\right),                          \tag{7}
\]
with inverse
\[
 (q,z)\longmapsto
 \left(\phi^{\log |z|^2}q,z\right).                           \tag{8}
\]
Under `(7)`, \(\Phi^t(q,z)=(q,e^{t/2}z)\) and
\(R_\theta(q,z)=(q,e^{i\theta}z)\).  Consequently the joint
\(\mathbb R\times S^1\)-orbits are exactly the complex leaves
\[
 \{q\}\times\mathbb C^\times.                                \tag{9}
\]

This construction uses no choice of a unitary character and no
square-root branch.  The circle in `(5)` is the unit circle of the
positive half-density line forced by the weight-one radius.  It is not
the Gamma-rank regular representation and is not obtained by listing
zeta zeros.

## Leafwise Kähler and Hodge structure

Give every leaf in `(9)` its standard complex coordinate \(z=u+iv\)
and Kähler form
\[
 \omega=du\wedge dv
       =\frac12\,d(|z|^2)\wedge d\theta.                       \tag{10}
\]
Then
\[
  (\Phi^t)^*\omega=e^t\omega.                                 \tag{11}
\]
On real leafwise one-forms,
\[
 *\,du=dv,\qquad *\,dv=-du,\qquad *^2=-1,                     \tag{12}
\]
and for every nonzero one-form \(\alpha\),
\[
 \alpha\wedge *\alpha=|\alpha|^2\omega>0.                     \tag{13}
\]
After complexification, \(J=*c\), with coefficient conjugation \(c\),
is anti-linear, satisfies \(J^2=-1\), and cup followed by \(J\) is
positive.

For a radial function \(F(z)=f(|z|^2)\), polar coordinates give
\[
 \int_{\mathbb C^\times}|F(z)|^2\,\omega
   =\pi\int_0^\infty |f(r)|^2\,dr.                            \tag{14}
\]
Thus the radial Hilbert measure is exactly Meyer's critical
\(L^2_{1/2}=L^2(\mathbb R_{>0},dr)\), up to the harmless factor
\(\pi\).  Moreover
\[
 (\Phi^{\log n})^*F(z)=f(n|z|^2),                             \tag{15}
\]
so the Poisson summands remain Deninger's discrete flow pullbacks on
the Kähler refinement.

## Deninger specialization and exact scope

Take \(X=X_{\rm HK}^{\times}\), the positive-radius part of the
Hilbert--Kummer suspension, and
\[
 x([P,u])=u\|\ell_P\|.
\]
`DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION` and
`DAC_DENINGER_FLOW_POISSON_DILATION` prove `(1)`.  Hence `(2)`--`(15)`
construct, rather than conjecture:

1. a canonical global transversal
   \(\Sigma_{\rm HK}=x^{-1}(1)\);
2. a canonical complex-one-dimensional Kähler orbit collar
   \(\Sigma_{\rm HK}\times\mathbb C^\times\);
3. weight-one Kähler flow and positive odd degree-one Hodge operator;
4. the exact critical radial measure and every Poisson dilation.

This orbit collar is not yet the Kähler--Riemann foliation required by
Deninger--Singhof.  The flow in `(6)` is tangent to the collar leaves,
and the leaves \(\{q\}\times\mathbb C^\times\) are closed rather than
dense.  Therefore the theorem fixes the radial chain metric, local
Hodge operator, Poisson pullbacks, and endpoint geometry, but does not
invoke the dense-leaf Poincaré-duality or purity theorem.  The actual
arithmetic leaf complex, or an equivalent twisted Hilbert complex,
must restrict to this collar and then be compared harmonically with
the Poisson quotient.

For the isolated \(\mathbb Q\)/Riemann-zeta collar, no additional
quaternionic coefficient is required to define the local operator:
the complexified real \(J=*c\) already has the required odd
\(K_{\mathbb R}\) parity.  Functorial extension to all number fields
still faces Deninger's no-real obstruction and may require a genuine
twist.

## Exact remaining boundary and comparison gates

This theorem constructs the positive-radius interior.  It does not
silently identify \(r(P)=0\) with the limit \(u\to0\).  They are
different loci in the uncompactified suspension.  To obtain the full
Poisson--zeta relevant complex one must still construct:

1. a strict source attachment of
   \(\Sigma_{\rm HK}\times\{0\}\);
2. sheafification of the already-proved endpoint formulas
   \(Rf(0)=f(0)\) and
   \(\int_{\mathbb C}Rf\,\omega=(\pi/2)\mathcal Ff(0)\);
3. the strict nuclear Schwartz/residue topology in which the flow sum
   has image \(Z(H_\cap)\);
4. a cup-isometric harmonic comparison from the resulting leafwise
   complex to \(M_\zeta=H_-/Z(H_\cap)\);
5. faithfulness on every Meyer generalized spectral jet.

The last two gates, not construction of the Kähler orbit collar or a
positive local Hodge star, contain the RH-bearing content.

## Hostile audit

- The unitary-character factor and the Gamma-rank regular
  representation are not identified with the circle in `(5)`.
- No compactness of the infinite-dimensional transversal is claimed.
  The orbit-collar structure is the explicit global product `(7)`, so
  no slice theorem is being assumed.
- These closed orbit leaves are not renamed Deninger's conjectural
  dense arithmetic leaves.  The flow is tangent here; the
  Deninger--Singhof purity theorem is not applied.
- Bare \(L^2\) completion would make the zeta multiplier range dense
  and erase distributional zero classes.  Equation `(14)` supplies
  the chain metric, not the completed arithmetic \(H^1\).
- No endpoint extension, harmonic comparison, zeta spectral theorem,
  RH statement, or simplicity statement is inferred from the
  interior trivialization.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- Christopher Deninger and Wilhelm Singhof,
  *Real polarizable Hodge structures arising from foliations*,
  arXiv:math/0204111.
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277.

## Log

- 2026-07-27 — Proved that the Hilbert--Kummer equivariant radius
  globally trivializes the nonunitary suspension and canonically
  upgrades it to a complex Kähler orbit collar with the exact critical
  radial measure.  Separated this collar from the still-conjectural
  dense arithmetic leaf complex.
