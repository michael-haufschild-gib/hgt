# Arithmetic extended-cusp Hodge boundary

- **ID:** `deninger-arithmetic-extended-cusp-hodge-boundary`
- **Stage:** 2-fully-proven
- **Type:** SOURCE LOCAL EXTENDED-HODGE THEOREM
- **Labels:** `DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY`,
  `DAC_LOG_RESIDUE_AS_EXTENDED_HODGE_DATA`
- **Parent:** `deninger-pro-log-kummer-cusp-hodge-extension`
- **Statement:** the finite-prime logarithmic Kummer cusp has a
  canonical extended unweighted \(L^2\) Hodge domain; it retains the
  Poincaré residue as Lagrangian Green boundary data while ordinary
  \(L^2\) discards it.

## Cylindrical conformal model

On the normal punctured disc put
\[
 z=xe^{i\theta},\qquad s=-\log x,\qquad x\in(0,1).
\]
The prime metric of `DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION` is
\[
 g_{v,u}
 =
 \frac{u}{s}(ds^2+d\theta^2).                                  \tag{1}
\]
For one-forms in real dimension two, Hodge star and \(L^2\)-energy
are invariant under a positive conformal change.  Thus the
degree-one problem for `(1)` is exactly the problem for the
cylindrical \(b\)-metric
\[
 g_b=ds^2+d\theta^2
 =\left(\frac{dx}{x}\right)^2+d\theta^2.                        \tag{2}
\]

Use Hunsicker's convention
\[
 x^cL^2=\{\omega:x^{-c}\omega\in L^2\}.
\]
The unweighted extended harmonic domain is
\[
 \mathcal H_{\mathrm{ext}}^1
 =
 \left\{
  \omega\in\bigcap_{\epsilon>0}x^{-\epsilon}L^2:
  (d+\delta)\omega=0
 \right\}.                                                     \tag{3}
\]

## Extended logarithmic generator

`[PROVED HERE] [DAC_LOG_RESIDUE_AS_EXTENDED_HODGE_DATA]`

The logarithmic generator satisfies
\[
 d\log z=-ds+i\,d\theta
 \in
 \bigcap_{\epsilon>0}x^{-\epsilon}L^2
 \setminus L^2.                                                \tag{4}
\]
It is closed and coclosed for `(2)`, and
\[
 *d\log z=i\,d\log z.                                         \tag{5}
\]

### Proof

Both \(ds\) and \(d\theta\) have constant pointwise norm for `(2)`,
whose volume is \(ds\,d\theta=dx\,d\theta/x\).  Their unweighted
square integral diverges as \(\int_0 dx/x\).  In the
\(x^{-\epsilon}L^2\) norm the form is multiplied by \(x^\epsilon\),
and
\[
 \int_0^1x^{2\epsilon}\frac{dx}{x}
 =
 \frac1{2\epsilon}<\infty
\]
for every \(\epsilon>0\), proving `(4)`.  Constant cylindrical
one-forms are harmonic.  With the orientation and star convention of
the prime-cusp theorem,
\[
 *ds=d\theta,\qquad *d\theta=-ds,
\]
which gives `(5)`.

Poincaré residue reads the coefficient of \(d\log z\), so `(4)`
realizes
\[
 \operatorname{Res}_v(d\log\chi^a)=v(a)
\]
as extended harmonic boundary data rather than an \(L^2\) bulk
class.

## Green boundary pairing

Write the leading term of an extended harmonic one-form as
\[
 \omega_\infty=a\,d\theta+b\,ds .
\]
For two leading packets \((a,b)\) and \((a',b')\), integration by
parts gives the boundary Green form
\[
 \mathfrak b((a,b),(a',b'))
 =
 \langle a,b'\rangle-\langle b,a'\rangle.                     \tag{6}
\]
This is the \(f=0,c=0\) case of Hunsicker's extended fibred-cusp
boundary theorem.  The boundary values of extended harmonic forms
form a Lagrangian subspace for `(6)`, and the Hodge star exchanges
the two complementary relative/absolute boundary images.

`[LITERATURE-SPECIALIZED] [DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY]`

At every finite log-toric prime stage:

1. ordinary \(L^2\) harmonic forms represent the image of relative
   cohomology in absolute cohomology;
2. extended harmonic forms split into exact extended, coexact
   extended, and ordinary \(L^2\) harmonic parts;
3. their boundary values are Lagrangian for `(6)`;
4. \(d\log z\) supplies the arithmetic residue line inside the
   extended exact part;
5. Hodge star and Poincaré residue obey
   \[
   \operatorname{Res}_v(*\alpha)
   =
   i\,\operatorname{Res}_v(\alpha)
   \]
   on the holomorphic logarithmic summand.

Items 1--3 are Hunsicker's theorems specialized to a cylindrical end
with trivial link fibre.  Items 4--5 are `(4)`--`(5)` and
`DAC_PRIME_LOG_HODGE_RESIDUE_COMPATIBILITY`.

## Equivariance

The deck map sends
\[
 (s,\theta,u)\longmapsto(qs,q\theta,u/q).
\]
It preserves `(1)` and its star.  Pullback multiplies \(d\log z\) and
its residue by \(q\); the Tate normal line of weight \(-1\) cancels
that factor.  Hence the extended domain, Green form, star, and
Tate-normalized residue pass through finite-index lattice refinement,
Galois descent, and positive-rational power maps.

## Exact boundary of the theorem

This theorem closes the **local prime-domain** defect.  It does not:

1. prove a uniform Fredholm theorem for the full pro-log inverse
   system;
2. complete the restricted sum over all primes;
3. glue the unitary \(r=0\) Poisson boundary;
4. identify the resulting global harmonic quotient with \(M_\zeta\);
5. prove cup isometry or generalized-jet faithfulness.

Those are global Calderón/Green obligations, not missing local Hodge
star calculations.

## Hostile audit

- The extended domain is strictly larger than ordinary \(L^2\); no
  Cheeger middle-extension theorem is misquoted.
- The compact/fibred-cusp hypotheses of Hunsicker are used only at a
  finite cylindrical stage.  Pro-limit compatibility remains open.
- The logarithmic residue is boundary data, not falsely labeled an
  \(L^2\) harmonic class.
- No zeta zero, RH premise, CCM object, or numerical computation
  enters.

## References

- Eugenie Hunsicker, *Extended Hodge Theory for Fibred Cusp
  Manifolds*, arXiv:1408.3257, Theorems 1--4.
- `DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION`.
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.

## Log

- 2026-07-27 — Replaced the residue-killing ordinary \(L^2\) domain
  by the exact extended cylindrical domain and identified Poincaré
  residue with its Lagrangian boundary data.
