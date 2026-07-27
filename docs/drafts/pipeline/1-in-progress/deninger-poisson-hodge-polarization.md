# Poisson--zeta geometric Hodge polarization

- **ID:** `deninger-poisson-hodge-polarization`
- **Stage:** 1-in-progress
- **Type:** THEOREM plus source construction conjecture
- **Labels:** `DAC_POISSON_HODGE_LOCAL_RIGIDITY`,
  `DAC_POISSON_GEOMETRIC_HODGE_POLARIZATION`
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Scope:** exact positivity gate in Deninger's arithmetic-cohomology
  program for \(\overline{\operatorname{Spec}\mathbb Z}\)
- **Statement:** a cup-compatible, flow-natural positive Hodge operator
  on the Poisson--zeta middle coefficient forces the critical line.
  Such an operator must be transported from a source Kähler leaf
  complex; none of the obvious operators on the Schwartz quotient
  supplies it.

## 1. Fixed source data

Let
\[
 M_\zeta=H_-/Z(H_\cap),\qquad
 Zf(x)=\sum_{n\ge1}f(nx),
\]
with scaling flow \(T_t=\lambda_{e^t}\) and generator \(\Theta\).
Let
\[
 \psi:M_\zeta\times M_\zeta\longrightarrow\mathbb C(1)
\]
be Paugam's unconditional alternating weight-one pairing, on the
topological domain where it is continuous.  Its infinitesimal
equivariance law is
\[
 \psi(\Theta x,y)+\psi(x,\Theta y)=\psi(x,y).             \tag{1}
\]

The source objects \(H_\cap,H_-,Z,T_t,\psi\) are defined without
listing a zeta zero.

After passing to the nonreal spectral suspension, Paugam also defines
the sign--conjugation
\[
 C=\begin{pmatrix}1&0\\0&-1\end{pmatrix}c
\]
for the upper/lower imaginary spectral splitting.  Conjugation exchanges
the two summands, so \(C^2=-1\), and anti-linearity gives
\(C\Theta=\Theta C\).  This is an unconditional odd
\(K_{\mathbb R}\)-structure on spectral \(H^1\).  It is not yet the
desired geometric Hodge theorem: positivity of
\(\psi(x,Cy)\) is the RH-bearing statement.

## 2. Exact Hodge obligation

A Deninger Hodge operator on the middle coefficient is a closed
antilinear operator
\[
 \star:\mathcal D(\star)\subset M_\zeta\longrightarrow M_\zeta
\]
such that:

1. the finite generalized spectral vectors form a core;
2. \(\star^2=-1\) on that core;
3. \(\star\Theta=\Theta\star\);
4. the form
   \[
    h(x,y)=\psi(x,\star y)                                  \tag{2}
   \]
   is Hermitian and strictly positive;
5. \(h\) completes the finite spectral core to a Hilbert space and the
   inclusion into the strong-dual spectral realization is faithful.

Equivalently, the centered flow
\[
 U_t=e^{-t/2}T_t                                             \tag{3}
\]
is unitary for \(h\).

## 3. Local rigidity theorem

`[PROVED HERE] [DAC_POISSON_HODGE_LOCAL_RIGIDITY]`

Let \(V\) be a finite-dimensional \(\Theta\)-stable subquotient on
which `(1)` is nondegenerate.  If a Hodge operator satisfying clauses
2--4 exists on \(V\), then:

1. every eigenvalue \(\rho\) of \(\Theta|_V\) satisfies
   \[
    \rho+\bar\rho=1;
   \]
2. \(\Theta|_V\) is semisimple.

### Proof

From `(1)`, commutation of \(\star\) with \(\Theta\), and `(2)`,
\[
 h(\Theta x,y)+h(x,\Theta y)=h(x,y).                       \tag{4}
\]
Thus \(S=\Theta-\tfrac12\) is skew-Hermitian.  A skew-Hermitian
operator on a finite-dimensional positive Hermitian space is normal,
hence diagonalizable, and every eigenvalue of \(S\) is purely
imaginary.  Therefore every eigenvalue of \(\Theta\) lies on
\(\operatorname{Re}s=\tfrac12\), and no nontrivial Jordan block
survives.

The same conclusion can be read directly from a nonzero eigenvector:
flow naturality gives
\[
 h(T_tx,T_tx)=e^t h(x,x),
\]
whereas \(T_tx=e^{t\rho}x\) gives
\[
 h(T_tx,T_tx)=e^{2t\operatorname{Re}\rho}h(x,x).
\]
Strict positivity forces
\(\operatorname{Re}\rho=\tfrac12\).

## 4. Arithmetic consequence

Meyer's theorem identifies the generalized point spectrum of the
strong dual of \(M_\zeta\) with every nontrivial zeta zero, with
algebraic multiplicity equal to its zero order.  Therefore a Hodge
operator satisfying Section 2 and faithful on these generalized
spectral blocks implies:
\[
 \operatorname{Re}\rho=\frac12
 \quad\text{for every nontrivial zeta zero }\rho.            \tag{5}
\]
Hence it proves RH.  If it acts on the full generalized-jet
realization, it also proves that every nontrivial zero is simple.

The simplicity conclusion is not assumed.  It records that the raw
Meyer quotient is a stronger target than a semisimple
multiplicity-preserving Hodge realization.

## 5. Source construction conjecture

`[CONJECTURE] [DAC_POISSON_GEOMETRIC_HODGE_POLARIZATION]`

The comparison in
`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON` factors through a
closed twisted-complex leafwise Hilbert complex
\[
 \left(E^\bullet(\mathscr S_{\mathrm{arith}}),Q\right)
 \longrightarrow C^\bullet_{\mathrm{PZ}}                    \tag{6}
\]
with the following properties.

1. **Kähler leaf source.**  \(E^\bullet(\mathscr S_{\mathrm{arith}})\)
   is the reduced leafwise de
   Rham complex of a pro-laminated complex-one-dimensional refinement
   of Deninger's rational-Witt suspension.  Its metric and orientation
   are constructed from real Betti orientation and the strict
   Milnor--Arakelov trace, before Mellin transformation.
2. **Odd \(K_{\mathbb R}\) coefficient.**
   \(\mathscr S_{\mathrm{arith}}\) is a leafwise flat positive
   Hermitian complex coefficient with a parallel antiunitary
   anti-linear operator \(J\), \(J^2=-1\), genuine twisted transition
   data.  Put
   \(\psi_E(u,v)=-h_E(u,Jv)\).  Then \(\psi_E\) is complex-bilinear
   alternating and \(\psi_E(v,Jv)=h_E(v,v)>0\).  The local model is
   `DAC_RECTANGULAR_QUATERNIONIC_HODGE`: for
   \[
     \psi_r((z,w),(z',w'))=zw'-wz',\qquad
     \star_r(z,w)=(-r\bar w,\bar z/r),
   \]
   one has
   \[
     \star_r^2=-1,\qquad
     \psi_r(v,\star_rv)=|z|^2/r+r|w|^2>0
   \]
   for \(v\ne0\), and centered power maps are unitary Hodge
   intertwiners.  Global descent must retain this odd parity without
   doubling \(M_\zeta\).  No-real transition data is additionally
   required for a theory functorial over all number fields, but not for
   the isolated \(\mathbb Q\) Hodge comparison.  On that source the
   operator is already \(J=*c\) on complexified real leafwise
   one-forms, so \(J^2=-1\) and cup followed by \(J\) is the positive
   leafwise \(L^2\) metric.
3. **Closed Hodge theory.**  \(Q\) is closed and densely defined.  At
   each compact Riemannian stage, coefficient parallel transport is
   unitary and hence bounded.  Benameur--Heitsch's theorem therefore
   makes the leafwise harmonic projection transversely smooth, and
   their Hodge lemma identifies its range with reduced
   \(L^2\)-cohomology.  These projectors are compatible with the
   pro-limit and the harmonic projection identifies reduced
   cohomology with \(\ker Q\cap\ker Q^\dagger\).
4. **Conformal weight one.**  The source flow scales the leafwise
   Kähler class by \(e^t\).  Leafwise Hodge star is therefore
   antiunitary of square \(-1\) in degree one, and the centered flow is
   unitary on harmonic degree one.
5. **Poisson comparison.**  The degree-zero comparison domain is
   \(H_\cap\), the generic degree-one target is \(H_-\), and its
   differential is \(Z=\sum_{n\ge1}F_n^{-1}\).  The harmonic
   comparison induces the identity on
   \(H_-/Z(H_\cap)\).
6. **Cup isometry.**  Leafwise integration transports the source cup
   form induced by \(\psi_E=-h_E(-,J-)\), with the coefficient's
   internal Koszul parity, to Paugam's \(\psi\), including all
   continuous generalized-jet directions.
7. **Faithfulness.**  No nonzero Meyer generalized spectral functional
   vanishes on the harmonic comparison image.

Under these clauses, leafwise Hodge star transports through `(6)` to
the operator in Section 2, so `(5)` follows from the proved local
rigidity theorem.

The difficult assertion is therefore clause 6 together with
faithfulness, not existence of a positive source star: \(J=*c\) is
already positive on the leaf source.  Proving that the harmonic
comparison reaches every Meyer generalized-zero direction is the
noncircular content that would imply RH.

## 6. Multiplicity-preserving RH-only variant

If clause 4 cannot hold on the raw nonsemisimple quotient, replace its
target by the associated graded of the canonical generalized-spectral
filtration:
\[
 \operatorname{gr}M_\zeta
 =
 \bigoplus_{\rho}\bigoplus_{j=0}^{m_\rho-1}
   \mathfrak m_\rho^j/\mathfrak m_\rho^{j+1}.               \tag{7}
\]
The flow on `(7)` is semisimple, while the dimension of the
\(\rho\)-block remains \(m_\rho\); trace and determinant multiplicity
are unchanged.  A positive faithful Hodge operator on `(7)` proves RH
without proving simplicity.

This variant is admissible only if `(7)` is constructed functorially
from the Poisson complex and the comparison preserves cup, trace, and
the nuclear character.  Declaring one Hilbert basis vector for every
zero multiplicity is not a source construction.

## 7. Rejection of obvious fake stars

1. **Fourier--inversion operator.**  \(J\mathcal F\) is a useful
   linear Poisson intertwiner, but complex conjugation does not turn it
   into a canonical odd positive star.  Its parity and square do not
   give the required quaternionic degree-one structure.
2. **Multiplicative Hilbert transform.**  The translation-invariant
   Hilbert transform has the correct formal square on an \(L^2\)
   boundary line, but its sign multiplier is not holomorphic in the
   Mellin variable.  It does not preserve the entire all-strips
   space \(H_-\), hence does not define an operator on \(M_\zeta\).
3. **Paugam spectral sign.**  Paugam's operator
   \(C=\operatorname{diag}(1,-1)c\) does construct the unconditional
   odd \(K_{\mathbb R}\)-parity: \(C^2=-1\) and it commutes with the
   flow on the nonreal spectral suspension.  It does not close the
   Hodge gate.  Its displayed positive sum uses critical-line
   reflection, and its full generalized-jet positivity is stronger
   still.  A source proof must realize this parity before divisor
   evaluation and derive positivity from geometry.
4. **Meyer \(*\)-reality.**  Requiring every self-adjoint convolution
   element to have real spectrum is equivalent to GRH.  It is a
   criterion, not the missing proof.
5. **Hedenmalm differential pair.**  The Jacobi-theta boundary problem
   gives an independent source spectral realization, but its 2026
   paper explicitly leaves construction of the related positive
   sesquilinear forms open.  The repository theorem
   `hedenmalm-theta-pair-divisor-supported-metric-law` sharpens this:
   every positive translation-stable Schwartz-core symmetrizing form
   is a nonlocal Fourier measure supported on the real Xi divisor, and
   faithfulness on all eigenfunctions is equivalent to RH plus
   simplicity.  This is an obstruction/classification, not a source
   construction of the missing metric.
6. **Bare \(L^2\) quotient.**  Completing before taking the analytic
   quotient can make \(Z(H_\cap)\) dense and erase the middle
   cohomology.  Reduced analytic cohomology must be compared before
   Hilbert completion.

## 8. Literature boundary for twisted leafwise Hodge theory

Benameur--Heitsch proves exactly the finite-stage analytic implication
used in clauses 2--3: on a compact Riemannian foliated manifold, a
leafwise flat complex bundle with preserved positive Hermitian metric
has bounded parallel translation; the harmonic projection on the
homotopy groupoid is transversely smooth, and harmonic forms represent
reduced leafwise \(L^2\)-cohomology.  Their signature construction also
permits preserved nondegenerate indefinite metrics, but then transverse
smoothness is an additional hypothesis unless boundedness is proved.

This result does not imply clauses 1, 4--7.  In particular it supplies
neither the arithmetic quaternionic bundle nor the Poisson differential,
the conformal weight-one flow, Paugam cup comparison, or faithfulness on
Meyer generalized jets.  Using it as a direct RH proof would therefore
be circular by omission.

## 9. Falsifiers

The conjecture fails if:

- no complex-one-dimensional leaf refinement gives the Poisson domain
  \(H_\cap\);
- the leaf differential differs from \(Z\) by a noncanonical collar
  multiplier;
- harmonic comparison has a kernel on any zero block;
- transported cup differs from Paugam's pairing;
- the flow scales the Kähler class by \(e^{ct}\) with \(c\ne1\);
- full-jet comparison exists but a nontrivial Jordan vector remains in
  a positive harmonic block;
- positivity is proved only after evaluating the zeta divisor.

## 10. Immediate construction steps

1. Construct the logarithmic Schwartz collar and Poisson comparison
   from `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`.
2. Define the real Betti orientation line and leafwise complex
   structure on each rational-Witt chart, then construct the genuinely
   twisted odd \(K_{\mathbb R}\) coefficient; do not globalize chartwise
   conjugation as a real form.
3. Prove power correspondences scale the chartwise Kähler form by
   their degree.
4. Establish a common closed core for \(Q,Q^\dagger\), and the flow.
5. Prove the harmonic comparison is cup-isometric and strict.
6. Decide, before any divisor evaluation, whether comparison lands in
   raw \(M_\zeta\) or the functorial associated graded `(7)`.
7. Prove that the harmonic metric escapes the
   translation-stable-Schwartz classification through a geometrically
   defined restricted domain, or construct its nonlocal atomic
   incidence measure directly from prime-orbit/real-boundary geometry.
   Asserting conservativity of that measure is RH-equivalent.
8. Apply `DAC_POISSON_HODGE_LOCAL_RIGIDITY` only after all source
   clauses are proved.

## 11. Lean surface

The local rigidity implication is already covered abstractly by:

- `DeningerArithmeticThreeTermHodgePurity.lean`;
- `DeningerArithmeticJordanObstruction.lean`;
- `DeningerTopologicalHodgeRHSimplicityRealJetUniversalityLaw.lean`.

New Lean work should formalize only the Poisson three-term assembly and
instantiate these generic theorems.  The analytic construction in
Section 5 remains a paper theorem obligation; it must not be encoded as
an axiom or structure instance claiming existence.

## References

- Christopher Deninger, *Some analogies between number theory and
  dynamical systems on foliated spaces*, ICM 1998.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- Christopher Deninger, *There is no "Weil-"cohomology theory with real
  coefficients for arithmetic curves*, arXiv:2204.02714.
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277.
- Frederic Paugam, *Spectral symmetries of zeta functions*,
  arXiv:0803.0199.
- Moulay-Tahar Benameur and James L. Heitsch, *The twisted higher
  harmonic signature for foliations*, arXiv:0711.0352.
- Haakan Hedenmalm, *Spectral interpretation of Riemann zeta zeros*,
  arXiv:2606.17494.
- `hedenmalm-theta-pair-divisor-supported-metric-law` in this
  repository, including its paper proof and unconditional Lean
  formalization of the algebraic obstruction surface.

## Log

- 2026-07-27 — Isolated the exact Poisson-source Hodge conjecture,
  proved its finite-block rigidity consequence, separated raw-jet and
  associated-graded targets, and rejected direct Fourier, Hilbert,
  spectral-sign, and bare-\(L^2\) fake polarizations.
- 2026-07-27 — Refined the source to a genuinely twisted odd
  \(K_{\mathbb R}\) coefficient and inserted the already-proved
  rectangular quaternionic local atom; global descent without
  multiplicity doubling is now an explicit gate.
- 2026-07-27 — Audited Benameur--Heitsch's primary source and isolated
  its exact contribution: finite-stage reduced twisted \(L^2\)-Hodge
  theory plus transverse smoothness for the positive unitary
  quaternionic coefficient.  Arithmetic coefficient construction,
  conformal flow, Poisson comparison, cup isometry, and faithfulness
  remain separate obligations.
