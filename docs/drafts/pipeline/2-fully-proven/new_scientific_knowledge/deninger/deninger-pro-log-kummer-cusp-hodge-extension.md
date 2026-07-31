# Pro-log Kummer cusp Hodge extension

- **ID:** `deninger-pro-log-kummer-cusp-hodge-extension`
- **Stage:** 2-fully-proven
- **Type:** SOURCE LOCAL-HODGE THEOREM
- **Labels:** `DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION`,
  `DAC_PRIME_LOG_HODGE_RESIDUE_COMPATIBILITY`
- **Parent:** `deninger-poisson-hodge-polarization`
- **Statement:** every finite pro-log Kummer prime chart carries a
  canonical logarithmic conformal leaf germ whose metric descends
  through Deninger's suspension, has flow weight one, and whose
  positive odd degree-one Hodge operator extends to the logarithmic
  residue complex.  This is the prime-normal atom; overlap gluing to
  mixed generic Kummer directions is a separate theorem.

## 1. Source chart

Use the finite log-toric chart of
`DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`:
\[
 \overline Z_{L,v}
 \cong
 \operatorname{Hom}(\ker\lambda_v,\mathbb C^\times)
 \times\mathbb C_z ,
 \qquad D_{L,v}=(z=0).                                      \tag{1}
\]
Fix the kernel character and work on the punctured normal collar
\[
 0<|z|<1,\qquad
 L_z=-\log|z|>0,\qquad
 \theta=\arg z.
\]
The positive-rational power correspondence is
\[
 F_q(z)=z^q,\qquad
 L_{z^q}=qL_z,\qquad
 d\theta_{z^q}=q\,d\theta.                                  \tag{2}
\]
The suspension height is \(u>0\), with deck map
\[
 (z,u)\longmapsto(z^q,u/q).                                 \tag{3}
\]

## 2. Logarithmic Kähler cusp

Define on the normal complex leaf
\[
\begin{aligned}
 g_{v,u}
   &=
   \frac{u}{L_z}\left(dL_z^2+d\theta^2\right),\\
 \omega_{v,u}
   &=
   \frac{u}{L_z}\,dL_z\wedge d\theta,\\
 *dL_z&=d\theta,\qquad *d\theta=-dL_z .
\end{aligned}                                                \tag{4}
\]

`[PROVED HERE] [DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION]`

The data `(4)` have the following properties.

1. The deck map `(3)` is an isometry and preserves
   \(\omega\), the complex orientation, and \(*\).
2. Deninger's transverse flow
   \(\phi^t(z,u)=(z,e^tu)\) satisfies
   \[
    (\phi^t)^*g=e^tg,\qquad
    (\phi^t)^*\omega=e^t\omega,\qquad
    (\phi^t)^**=*(\phi^t)^*.                                  \tag{5}
   \]
3. The metric is complete toward \(z=0\).
4. The star preserves the real smooth logarithmic one-form
   complex and satisfies \(*^2=-1\).
5. After complexification, the anti-linear operator
   \[
    J=*c                                                        \tag{6}
   \]
   satisfies \(J^2=-1\), commutes with all power
   correspondences and the flow, and polarizes the alternating
   wedge form:
   \[
    \alpha\wedge J\alpha
    =
    \alpha\wedge *\overline\alpha>0
    \quad(\alpha\ne0).                                         \tag{7}
   \]

### Proof

Pulling the target metric of `(4)` through `(3)` gives
\[
 \frac{u/q}{qL_z}
 \left((q\,dL_z)^2+(q\,d\theta)^2\right)
 =
 \frac{u}{L_z}
 \left(dL_z^2+d\theta^2\right).                                \tag{8}
\]
The identical calculation with the wedge gives deck invariance of
\(\omega\).  The Hodge star on one-forms in real dimension two
depends only on the oriented conformal class, so it is also
preserved.  Replacing \(u\) by \(e^tu\) proves `(5)`.

The radial distance to \(L_z=\infty\) is
\[
 \int^{\infty}\sqrt{\frac{u}{L}}\,dL=\infty,                    \tag{9}
\]
so the divisor is a complete leafwise cusp end.  Smooth logarithmic
one-forms are generated over smooth functions by \(dL_z\) and
\(d\theta\); the last two formulas of `(4)` preserve their span and
give \(*^2=-1\).

Complex conjugation commutes with the real operator \(*\), so
\[
 J^2=*c*c=*^2=-1.
\]
Equation `(7)` is the ordinary pointwise Hermitian norm identity.
Holomorphic power maps are oriented conformal, hence their pullbacks
commute with both \(*\) and \(c\).

## 3. Compatibility with Kummer residue

In the coordinate `(1)`,
\[
 d\log z=-dL_z+i\,d\theta,\qquad
 *d\log z=i\,d\log z.                                        \tag{10}
\]
Poincare residue is
\[
 \operatorname{Res}_{v}(d\log z)=1.                            \tag{11}
\]
Give the complexified residue orientation line the degree-one
operator \(i\).  Then
\[
 \operatorname{Res}_{v}(*\alpha)
 =
 i\,\operatorname{Res}_{v}(\alpha)                             \tag{12}
\]
on the holomorphic logarithmic summand.

`[PROVED HERE] [DAC_PRIME_LOG_HODGE_RESIDUE_COMPATIBILITY]`

Equation `(12)` is independent of the chosen uniformizer.  Indeed,
if \(z'=\chi^a z\) with \(a\in\ker\lambda_v\), then
\[
 d\log z'=d\log z+d\log\chi^a
\]
and the second term has zero residue.  Along a fixed normal leaf it
is constant, so the two metrics differ only by a positive conformal
factor.  Their degree-one Hodge stars agree.

For \(F_q\), both \(d\log z\) and its residue scale by \(q\).
Tensoring the residue with the Tate line of weight \(-1\) cancels
this factor, exactly as in
`DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`.  Thus `(12)`
passes through the Tate-normalized residue square and all
unit-amalgamated relative cells.

## 4. Relation to the generic Hilbert--Kummer leaf

On the generic Hilbert--Kummer chart,
\[
 \ell_h(\pi)=\log|\chi^\pi|=-L_z .
\]
The prime divisor is therefore an infinite-modulus end, not the
zero vector \(h=0\).  Along a pure prime-normal ray for which \(L_z\)
is proportional
to \(\|h\|\), the affine leaf coframe of
`DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION` is
\[
 \alpha=\frac{dL_z}{L_z},\qquad
 \beta=\frac{d\theta}{L_z}.
\]
Its metric \(u\|h\|(\alpha^2+\beta^2)\) is conformal to `(4)`.
Consequently the generic and prime-normal degree-one stars agree
exactly on this common normal sector; only their positive conformal
factors differ.

This closes the local normal Hodge atom at every finite prime chart.
Filtered lattice enlargement preserves the logarithmic complex,
residue, and conformal star, so the atoms form a compatible pro-log
cylinder system.  A global leaf distribution still requires an
overlap theorem interpolating mixed kernel-modulus directions with
the affine generic distribution.

## 5. Boundary of the theorem

This theorem does not claim:

1. that the prime divisor is a finite-distance smooth leaf point;
2. that \(z\mapsto z^p\) becomes a local diffeomorphism at \(z=0\);
3. that the reduced global harmonic comparison with \(M_\zeta\) is
   faithful;
4. that local cusp positivity proves RH;
5. that prime-normal leaves already glue to every mixed generic
   affine leaf.

The prime stratum is a complete cusp boundary carrying a residue
complex.  Periodic prime packets remain transverse suspension
strata.  Their Lefschetz contribution is computed by the source
power correspondence and residue trace, not by pretending that
\(z^p\) is a nondegenerate smooth return germ at the origin.

## Hostile audit

- All coordinates and residues come from Deninger's finite
  log-toric character chart.
- Power/deck identities are exact, including the suspension height.
- Uniformizer changes alter only the positive conformal factor and
  a zero-residue logarithmic unit.
- Completeness, not smooth extension across a finite-distance point,
  is proved.
- No zeta zero, RH premise, spectral divisor, CCM object, or
  numerical computation enters the construction.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §§11--12: https://arxiv.org/abs/1807.06400.
- Kazuya Kato, *Logarithmic structures of Fontaine--Illusie*.
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.
- `DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION`.

## Log

- 2026-07-27 — Constructed the suspension-invariant complete
  logarithmic cusp, proved weight-one flow, positive odd Hodge star,
  uniformizer independence, and compatibility with the
  Tate-normalized Poincare residue.
