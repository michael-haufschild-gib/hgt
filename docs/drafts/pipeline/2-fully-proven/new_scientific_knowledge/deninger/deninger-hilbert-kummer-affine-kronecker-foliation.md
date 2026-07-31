# Hilbert--Kummer affine Kronecker foliation

- **ID:** `deninger-hilbert-kummer-affine-kronecker-foliation`
- **Stage:** 2-fully-proven
- **Type:** SOURCE GENERIC-FOLIATION THEOREM
- **Labels:** `DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION`,
  `DAC_RESIDUAL_DENSE_KUMMER_LEAVES`
- **Parent:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Statement:** the Hilbert--Kummer modulus Euler field and its
  associated Kronecker phase field define a canonical
  two-real-dimensional integrable distribution on the nonunitary
  generic suspension; Deninger's flow is transverse, scales its
  Kähler form with weight one, and a residual set of leaves is dense
  in the unitary phase direction.

## 1. Fine generic source

Before positive-rational descent, write the nonunitary
Hilbert--Kummer generic suspension as
\[
 \widetilde X_{\mathrm{HK}}^\times
 =
 X_{\mathrm{unit}}\times(H_{\mathrm{Kum}}\setminus\{0\})
 \times\mathbb R_{>0}.                                           \tag{1}
\]
A point is \((\eta,h,u)\).  For \(a\in
V=\overline{\mathbb Q}^{\times}/\mu_\infty\otimes\mathbb Q\), put
\[
 \ell_h(a)=\langle h,f_a\rangle_{H_{\mathrm{Kum}}}.               \tag{2}
\]
The unitary character determined by \(h\) and time \(t\) is
\[
 \kappa_h^t(a)=\exp(i t\ell_h(a)).                               \tag{3}
\]

Define two cylinder-smooth vector fields:

1. the modulus Euler field
   \[
   A_{(\eta,h,u)}
   =
   \left.\frac d{ds}\right|_{0}(\eta,e^s h,u);
                                                                    \tag{4}
   \]
2. the Kummer--Kronecker phase field
   \[
   K_{(\eta,h,u)}
   =
   \left.\frac d{dt}\right|_{0}(\eta\kappa_h^t,h,u).              \tag{5}
   \]

Both fields are defined at every finite character-lattice stage and
are compatible with the pro-Stein transition maps.

## 2. Integrable affine distribution

`[PROVED HERE] [DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION]`

On `(1)`,
\[
 \mathcal F_{\mathrm{aff}}=\operatorname{span}_{\mathbb R}\{A,K\}
                                                                    \tag{6}
\]
is a rank-two integrable oriented distribution.  It is preserved by
Galois maps, positive rational powers, suspension deck descent, and
Deninger's flow.

### Proof

The vector \(A\) is nonzero because \(h\ne0\).  If \(K=0\), then
\(\ell_h(a)=0\) for every \(a\).  Logarithmic Kummer functions span a
dense subspace of \(H_{\mathrm{Kum}}\), so `(2)` would force \(h=0\),
a contradiction.  The two fields lie in different modulus and phase
factors, hence are linearly independent.

Scaling \(h\) scales `(2)`, so
\[
 [A,K]=K.                                                         \tag{7}
\]
Thus the span is involutive.  Frobenius sends
\[
 (\eta,h,u)\longmapsto(\eta^q,qh,u/q).
\]
It sends the curve `(4)` to the corresponding curve through
\((\eta^q,qh,u/q)\).  On `(5)`,
\[
 (\eta\kappa_h^t)^q
 =
 \eta^q\kappa_{qh}^t,
\]
so it also sends \(K_h\) to \(K_{qh}\).  Hence `(6)` descends through
the deck relation.  Galois naturality follows from invariance of the
Allcock--Vaaler pairing.  Deninger's flow changes only \(u\), so it
preserves both fields.

The flow vector
\[
 T=\left.\frac d{d\tau}\right|_0(\eta,h,e^\tau u)
\]
is not in `(6)`: it has a nonzero suspension-height component, while
\(A\) and \(K\) do not.  Therefore the flow is transverse to the
leaves.  This fixes the tangent-flow defect of the Kähler orbit
collar.

## 3. Weight-one Kähler geometry

Let \(\alpha,\beta\) be the leafwise coframe dual to \(A,K\), and set
\[
 x(\eta,h,u)=u\|h\|,\qquad
 g_{\mathcal F}=x(\alpha^2+\beta^2),\qquad
 \omega_{\mathcal F}=x\,\alpha\wedge\beta.                       \tag{8}
\]
The deck identities \(u\mapsto u/q\), \(h\mapsto qh\) show that \(x\)
is invariant.  Since the deck map preserves \(A,K\), `(8)` descends.

Define
\[
 J A=K,\qquad JK=-A.                                              \tag{9}
\]
Every oriented real surface is complex, so `(9)` is integrable
leafwise.  Equations `(8)`--`(9)` give
\[
 *\alpha=\beta,\qquad *\beta=-\alpha,\qquad *^2=-1,              \tag{10}
\]
and
\[
 \gamma\wedge *\gamma
 =
 (a^2+b^2)\alpha\wedge\beta>0
\quad
\text{for }\gamma=a\alpha+b\beta\ne0.                            \tag{11}
\]

Deninger's transverse flow preserves the coframe and sends
\(x\mapsto e^\tau x\).  Therefore
\[
 (\phi^\tau)^*g_{\mathcal F}=e^\tau g_{\mathcal F},
\qquad
 (\phi^\tau)^*\omega_{\mathcal F}=e^\tau\omega_{\mathcal F}.     \tag{12}
\]
This is the required weight-one conformal law with transverse, not
tangent, flow.

Along the Euler direction,
\[
 A(\log x)=1,\qquad K(x)=0.
\]
Thus locally \(\alpha=d\log x\) and
\[
 \omega_{\mathcal F}
 =
 x\,d\log x\wedge\beta
 =
 dx\wedge\beta.                                                   \tag{13}
\]
After normalized phase integration, `(13)` is exactly Meyer's
critical radial measure \(dx\).

## 4. Residual dense leaves

The Pontryagin dual of
\[
 X_{\mathrm{unit}}=\operatorname{Hom}(V,S^1)
\]
is the discrete countable group \(V\).  The closure of the
one-parameter subgroup `(3)` has annihilator
\[
 \operatorname{Ann}(\overline{\kappa_h^\mathbb R})
 =
 \{a\in V:\ell_h(a)=0\}.                                        \tag{14}
\]

`[PROVED HERE] [DAC_RESIDUAL_DENSE_KUMMER_LEAVES]`

The set
\[
 H_{\mathrm{dense}}
 =
 H_{\mathrm{Kum}}
 \setminus
 \bigcup_{0\ne a\in V}f_a^\perp                                \tag{15}
\]
is dense \(G_\delta\), Galois invariant, and stable under nonzero
real scaling.  For \(h\in H_{\mathrm{dense}}\), the Kronecker orbit
`(3)` is dense in \(X_{\mathrm{unit}}\).  Hence the affine leaf
through \((\eta,h,u)\) is dense in the phase factor over its positive
modulus ray.

### Proof

Every \(f_a^\perp\) in `(15)` is a closed nowhere-dense hyperplane:
\(f_a\ne0\) for non-torsion \(a\).  The group \(V\) is countable, so
Baire's theorem makes the complement dense \(G_\delta\).  Equations
`(2)` and `(14)` then show its annihilator is zero.  Pontryagin
duality says a subgroup of a compact abelian group is dense exactly
when its annihilator is zero.

Galois maps permute the nonzero Kummer vectors, and nonzero scaling
does not change their orthogonal hyperplanes, proving the remaining
claims.

## 5. Arithmetic interpretation

The new distribution separates three directions that the orbit collar
alone conflated:

- \(A\): leafwise modulus direction;
- \(K\): leafwise Kummer phase direction;
- \(T\): transverse arithmetic Frobenius flow.

The modulus sphere remains a transverse parameter but is
cohomologically removed by
`DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION`.  On the
residual locus `(15)`, the surviving leaves are dense in the relevant
phase--radial collar.  The local pro-log prime model has the same
Euler/phase frame: logarithmic radial and angular fields around the
prime divisor, while the prime periodic orbit belongs to the
transverse Deninger flow.

This theorem constructs the generic arithmetic foliation and its
Kähler metric.  Local boundary atoms are supplied by
`DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION` at every prime and
`DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX` at infinity.
`DAC_AFFINE_PRO_LOG_PRIME_HODGE_OVERLAP` proves their
oriented-conformal overlap on actual prime packets.  Remaining global
work is:

1. glue the complete-cusp rigged complexes and their
   orientation-twisted real endpoint through the pro-system;
2. prove the reduced leafwise harmonic complex maps
   cup-isometrically and faithfully to \(M_\zeta\);
3. identify transverse prime-return Lefschetz indices.

## Hostile audit

- Deninger's flow is transverse to `(6)`.
- No closed orbit collar is relabeled as the arithmetic foliation.
- Density is proved only on the residual Kummer locus `(15)`, not at
  every modulus functional.
- Infinite-dimensional sphere contractibility and phase-orbit
  density are distinct statements.
- Local positivity does not imply nonzero reduced harmonic
  cohomology; `DAC_CRITICAL_RADIAL_L2_POISSON_QUOTIENT_NO_GO` remains
  binding.
- No zeta zero, RH, Weil positivity, CCM object, or numerical
  computation enters the construction.

## References

- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §§6 and 12: https://arxiv.org/abs/1807.06400.
- Standard Pontryagin duality criterion for density of a subgroup in
  a compact abelian group.

## Log

- 2026-07-27 — Constructed the affine Euler--Kronecker leaf
  distribution with transverse Deninger flow, proved weight-one
  Kähler geometry, and proved residual phase-density by Baire and
  Pontryagin duality.
