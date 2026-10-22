# Route R: five-program polarized-descent frontier

- **ID:** `route-r-five-program-polarized-descent-frontier`
- **Stage:** 1 — in progress
- **Type:** RESEARCH PROGRAM / SOURCE-PURE SELECTION / FUNCTION-FIELD CONTROL /
  RELATIVE LOCALIZATION / ARAKELOV COMPLETION
- **Statement:** Route R is flat before scalarization. Its literal ordinary-prime source now has a
  retained zero-isotropy relative class, a strict prime/depth/divisor-faithful map to the resolved
  Xi complex, a source Stokes regulator descending to `H¹` with period one on that class, a
  positive parallel resolved polarization, and an unconditional source-pure norm-conservative
  selection theorem. Its RH-bearing open core is a graded variable-ideal,
  coefficient-faithful singular Cartier comparison identifying that resolved boundary and metric
  with the fixed physical same-fibre Xi conormal. The five programs below determine the exact
  mathematical type of that comparison and exclude flatness, reciprocity, determinant-line,
  fixed-Hilbert, and localization theatre.
- **Parents:**
  - `route-r-resolved-bv-wold-source-frame-annihilation.md`;
  - `route-r-essential-edge-occupation-det2-bv-relative-class.md`;
  - `prime-wold-determinant-connection-purity-law.md`;
  - `source-localization-modular-defect-conservation-law.md`;
  - `polarized-critical-rees-corona-transgression-rh.md`.

## Goal

Construct and classify the strongest source-pure Route-R statements in five directions:

1. function-field control;
2. regular/singular localization;
3. relation-valued reciprocity;
4. archimedean/Arakelov completion;
5. a divisor-free selection theorem.

The goal is not another RH-equivalent consumer.  It is to identify which parts are unconditional
source mathematics, which external theories supply real infrastructure, and which single
arithmetic producer remains absent.

## Frontier theorem: resolved flatness is not purity

For any two real source records (m_i) and nonzero clocks \(\lambda_i\), put

\[
 \theta_{ij}=m_i\lambda_j-m_j\lambda_i,
 \qquad
 G_i(a)=\begin{pmatrix}\lambda_i^{-1}&a m_i\\0&\lambda_i\end{pmatrix}.
\]

Then

\[
 {\theta_{ij}\over\lambda_i\lambda_j}
 ={m_i\over\lambda_i}-{m_j\over\lambda_j},
 \qquad
 T_{ij}(a):=G_i(a)^{-1}G_j(a),
 \qquad
 T_{ij}T_{jk}=T_{ik}.                                      \tag{R1}
\]

Hence the resolved covariant square vanishes for every (a).  The scalar reporter

\[
 U_{ij}(a)=\exp(a\theta_{ij})                               \tag{R2}
\]

forgets the diagonal clock characters.  On any triangle with nonzero additive defect, `(R2)` is
flat exactly when (a=0).  Therefore:

> `[PROVED HERE] [SOURCE-PURE CLASSIFICATION]` Source flatness is automatic gauge coherence.
> Scalar flatness is an additional descent property.  No functorial chain map from the resolved
> source complex can produce the nonzero scalar curvature: a chain map sends the identically zero
> resolved square to zero.  Any successful scalar boundary must be a genuinely relative
> connecting class, not ordinary scalarization of `(R1)`.

This is the correction against which all five programs are audited.

## Program 1: function-field analogue

Let (C/\mathbb F_q) be a smooth projective curve and (v) a closed place of degree (d_v>0).
Write (N_v=q^{d_v}).  The literal Route-R analogue is

\[
 m_{v,e}=(1-N_v^{-1})N_v^{-e},
 \qquad
 \lambda_{v,e}=(e+1)d_v\log q,
 \qquad
 \theta_{ij}=m_i\lambda_j-m_j\lambda_i.                   \tag{F1}
\]

For one place and depths (0,1,2), the scalar triangle defect is

\[
 \theta_{01}+\theta_{12}-\theta_{02}
 =-(1-N_v^{-1})^3d_v\log q<0.                              \tag{F2}
\]

Thus the function-field scalar reporter is curved away from centered rate zero, while its
resolved triangular frame is flat for every rate, exactly as over (\mathbb Q).

For a Frobenius eigenvalue (\alpha), define the centered weight-one rate

\[
 a_q(\alpha)
 ={\log(\lVert\alpha\rVert^2/q)\over\log q}.               \tag{F3}
\]

The logical roles of the geometric inputs are distinct:

- Poincare duality/functional equation gives reciprocal pairing
  (\alpha\leftrightarrow q/\alpha), hence (a\leftrightarrow-a).  It does not force (a=0).
- Resolved source flatness `(R1)` holds for every (a).  It does not force (a=0).
- The positive primitive polarization produced by the Weil/Deligne package makes Frobenius a
  (q)-similitude.  If (Fx=\alpha x\), (x\ne0), then

  \[
    \lVert Fx\rVert^2=q\lVert x\rVert^2
    =\lVert\alpha\rVert^2\lVert x\rVert^2,
  \]

  so (\lVert\alpha\rVert^2=q) and `(F3)` is zero.
- Hard Lefschetz supplies the primitive decomposition and definite Lefschetz form in the
  higher-dimensional purity package.  For a curve it is not an independent equation on (H^1);
  positivity of the same-fibre form is the load-bearing selector.

`[PROVED HERE] [CONTROL VERDICT]` Function fields do not validate a flatness proof of RH.  They
validate a **polarized descent** proof: reciprocal duality must be identified with adjunction in a
positive same-fibre realization.  The number-field problem is construction of that realization,
not the algebra after it exists.

Existing Lean supplies coefficient-level reciprocal closure
(`FunctionFieldFE.lean`, `FunctionFieldSpectralClosureUniversalityLaw.lean`), the similitude
spectral locus (`SimilitudeSpectralLocus.lean`), and weight-one polarization
(`DeningerWeightOnePolarization.lean`).  Missing infrastructure to add is the literal `(F1)`--`(F3)`
Route-R bridge and the resolved/scalar comparison.

## Program 2: regular/singular localization

The source-derived essential-edge occupation operator has spectrum (1/n).  For a prime (p),

\[
 Z_p(s)=(1-p^{-s})\zeta(s)                                 \tag{L1}
\]

simultaneously carries:

- regular grades (k\ge2): \(\operatorname{Tr}(E_pQ)^k=Z_p(k)\), hence the `det2` moments;
- singular grade (1): \(\operatorname{Res}_{s=1}Z_p(s)=1-p^{-1}\), the BV/Wold first trace.

This is a genuine graded relative class. The corpus now constructs both its essential-edge
operator realization and a literal rational-adelic zero-isotropy relative complex. The latter has
`D₁D₀=0`, retains the ordinary-prime cocycle because prime-scaling-fixed Schwartz vectors vanish at
the zero adele, and admits a strict chain map to the resolved actual-Xi complex. The source class
lands nontrivially, retaining prime, depth, divisor, and leading-jet provenance, as an exact target
boundary annihilated by the next differential. Thus existence of a source complex, connecting
class, and strict resolved comparison is no longer open. A bilateral prime-orbit sum supplies an
independent source Stokes regulator: it kills every relative boundary, descends to genuine `H¹`,
and evaluates to one on the retained class. Source Stokes flatness and non-erasure are therefore
also closed; they do not identify the scalar Cartier fibre.

Parent theories provide three legitimate carriers:

1. excision/localization in cyclic homology and mixed complexes;
2. localization cofiber sequences in THH/TC, compatible with the cyclotomic trace from K-theory;
3. determinant-bundle curvature with Wodzicki-residue correction.

They do not identify `(L1)` with the required arithmetic boundary.  Moreover `(R1)` forces an
exact restriction:

> `[PROVED HERE] [LOCALIZATION NO-GO]` A connecting class equal to scalar Route-R curvature cannot
> be induced by an ordinary chain map from the resolved complex, because its square is identically
> zero.  The class must measure failure of scalar descent, closure, or regularization—precisely a
> relative boundary—not source curvature.

`[OPEN CORE] [ROUTE_R_REGULAR_SINGULAR_CARTIER_COMPARISON]` Extend the constructed strict resolved
comparison to a graded variable-ideal singular Cartier comparison whose `ell1` coefficient data
survive, and prove that its resolved target boundary equals the fixed scalar physical landing on
the actual leading Xi conormal. The actual/Fisher edge differs by an `ell1` correction throughout
the Xi strip, but both reflected Fisher sectors lie in one fixed `ell2` carrier only for
`|2 Re(rho)-1|<1/2`; therefore a fixed Hilbert ideal cannot supply the full comparison. Neither
abstract excision nor the exact closed cyclic recipient supplies this identification
automatically.

## Program 3: relation-valued reciprocity retaining labels

The graph relations

\[
 \mathcal R_{ij}(a)=\operatorname{graph}(T_{ij}(a))          \tag{Q1}
\]

retain both endpoint labels, BV mass, and Wold clock.  They satisfy exact relational composition
and inverse reciprocity:

\[
 \mathcal R_{jk};\mathcal R_{ij}=\mathcal R_{ik},
 \qquad
 \mathcal R_{ji}=\mathcal R_{ij}^{-1}.                     \tag{Q2}
\]

This is the maximal honest relation-valued reciprocity already forced by the resolved source
frame.  It exists for every real (a), so `(Q1)`--`(Q2)` cannot select the critical value.

The corpus also proves a complementary closure no-go: a closed linear relation extending the old
zero boundary on the dense cross-prime arithmetic core is the full source space times its vertical
fibre; if single-valued it is the zero graph.  Thus neither graph completion of the old zero
boundary nor unrestricted multivaluedness can be the missing annihilator.

`[PROVED HERE] [RELATION VERDICT]` Label-retaining reciprocity exists and is nonselective. A
positive Hermitian functor on the labelled resolved relation now also exists: its fibre metric is
strictly positive and every resolved transition is an isometry. Orbitwise reciprocity and this
transported metric both permit every rate. The load-bearing datum is identification with the
fixed same-fibre Cartier metric on the principal conormal; their difference is an explicit strict
square off rate zero.

`[OPEN CORE] [ROUTE_R_RELATION_DAGGER_IDENTIFICATION]` Prove from the literal source that the
constructed resolved dagger realization agrees with the fixed Cartier dagger on the arithmetic
conormal, through the variable-ideal singular comparison of Program 2. The unconditional theorem
`normConservative_sourceCharacterFibre_descent_dichotomy` then forces either zero descent or rate
zero; coefficient-faithful nonvanishing must exclude the zero branch. A relation field, groupoid
law, or closed graph without this same-fibre identification adds no selection.

## Program 4: archimedean place and determinant geometry

The finite singular residue has an exact Arakelov completion.  For a finitely supported real prime
divisor (d), put

\[
 \operatorname{tr}_{\mathrm f}(d)=\sum_p d_p\log p,
 \qquad
 \partial_\infty d=-\operatorname{tr}_{\mathrm f}(d),
 \qquad
 d\longmapsto(d,\partial_\infty d).                       \tag{A1}
\]

The corpus proves that `(A1)` is injective, its image is the kernel of the total Arakelov trace,
and its cokernel is the real orientation line.  Applied to finite BV/Wold residue coefficients,
the infinity coordinate is the canonical negative finite residue sum.  This is the correct
product-formula closure of the singular first trace.

However:

- a trivial determinant line permits arbitrary zero divisors;
- ordinary Quillen/Chern scaling has the wrong weight for logarithmic Hardy--Green pole energy;
- exact product-formula cancellation erases total degree but not labelled scalar-descent defect;
- the Wodzicki correction explains how regularized curvature differs from a naive first Chern
  form, but does not identify the arithmetic correction with the Xi principal conormal.

`[OPEN CORE] [ROUTE_R_ARAKELOV_RESIDUE_DETERMINANT_CHARACTER]` Construct a relative determinant
character whose finite regular face is the Wold--Gamma `det2` connection, finite singular face is
the BV residue, and infinity face is the Arakelov/analytic-torsion correction.  Its metric must be
the source-capacity or polarized Rees--corona metric, not an ordinary Quillen metric.  Prove its
same-fibre dagger law and conormal faithfulness.  Existing Arakelov exactness supplies the degree
closure only.

## Program 5: divisor-free source-pure selection

Fix the nonzero labelled Route-R edge

\[
 c=\theta((2,0),(2,1))>0.
\]

Let a real source fibre carry the scalar action (x\mapsto e^{ac}x).  Suppose a nonzero linear
descent (T) intertwines this action with an operator (V) on a normed target and (V) preserves
norms.  For (Tx\ne0),

\[
 \lVert Tx\rVert
 =\lVert VTx\rVert
 =\lVert T(e^{ac}x)\rVert
 =e^{ac}\lVert Tx\rVert.
\]

Therefore (e^{ac}=1), hence (ac=0), and (a=0).

> `[PROVED HERE] [SOURCE-PURE SELECTION THEOREM]` A nonzero equivariant descent of the scalar
> Route-R character into any norm-conservative target forces the centered rate to vanish.

This theorem contains neither `XiDivisorSupport` nor a zero coordinate, and it does not define the
rate as (2\operatorname{Re}\rho-1).  It is an unconditional source theorem.  It is also only a
consumer: the arithmetic work is to construct (T), prove it nonzero on the completed principal
conormal, and derive norm conservation from the source. Its generic form is now formalized in
`SourceCharacterFibreConservativeDescentLaw.lean`; the generic resolved connection and
`D₁D₀=0` law are formalized in `HTGeometry/TwoRecordResolvedConnection.lean`.

`[OPEN CORE] [ROUTE_R_SOURCE_PURE_NONZERO_CONSERVATIVE_DESCENT]` Construct that (T) from the
regular/singular relative determinant character of Programs 2 and 4, with the relation-valued
labels of Program 3.  Function-field Program 1 says the needed theorem is the number-field analogue
of polarized Frobenius similitude.

## Unified architecture after five-program audit

```text
literal prime/depth source
  -> inverse-prime occupation operator
  -> one graded relative zeta class (regular det2 + singular BV)
  -> retained rational-adelic zero-isotropy class
  -> bilateral source Stokes regulator, period one on H1 class
  -> strict source-to-resolved-Xi chain map
  -> resolved labelled triangular relation (flat and positively polarized for every rate)
  -> Arakelov/analytic-torsion infinity correction
  -> graded variable-ideal singular Cartier comparison
  -> fixed same-fibre dagger identification, nonzero on source conormal
  -> norm-conservative scalar character
  -> centered rate zero.
```

The source relative class, period-one Stokes regulator, strict resolved map, positive transported
frame, and last selection implication are formalized. The unresolved scientific core is the
middle comparison: assemble the
infinity correction with a graded variable ideal, retain coefficients, and identify the resolved
boundary/metric with the fixed physical Cartier fibre without allowing zero descent.

## External boundary through 4 August 2026

- Deligne's Weil theorem supplies the function-field purity endpoint; the corpus does not contain
  etale cohomology or a formal proof of Weil II.
- Connes--Consani--Marcolli construct the cyclic-homology cokernel of the adelic restriction map and
  express the explicit formula as a Lefschetz trace formula; their RH endpoint is positivity of the
  trace pairing. The corpus now realizes the exact closed nonunital strong recipient, descended
  Lefschetz/Real/Clifford structure, and a separate prime-isotropy strict resolved-Xi chain map.
  The corpus also has a bilateral source Stokes regulator detecting that prime-isotropy class with
  period one. Their literature still does not provide Route R's singular Cartier comparison.
- Blumberg--Mandell supply localization cofiber sequences for THH/TC and compatibility with the
  cyclotomic trace; Hesselholt realizes Hasse--Weil zeta regularized determinants in THH Tate
  cohomology over finite fields.  Neither result constructs the number-field Route-R class.
- Paycha--Rosenberg identify the Wodzicki-residue correction between regularized first Chern forms
  and determinant-bundle curvature.  This validates residue correction as an object type, not its
  arithmetic identification.
- Deninger and Flach--Morin provide conjectural arithmetic cohomology/Weil-etale frameworks with
  determinant and duality structures.  They do not prove the required same-fibre positive descent.
- Connes--Consani--Moscovici's semilocal Sonin and 2025 zeta-spectral-triple programs provide
  source-side spectral and determinant infrastructure.  Their remaining convergence/positivity
  theorem is different from, and does not imply, Route R's relative descent.

No located source contains the exact two-record BV/Wold triangular frame, its resolved-flat versus
scalar-curved boundary, the essential-edge occupation extraction, or the proposed relative
Arakelov dagger descent.  Novelty is restricted to those source-specific constructions and their
joint architecture; all ambient homological, determinant, and purity theories are parent
mathematics.

## Hostile audit

1. Resolved flatness for every rate forbids using (D^2=0) as selector.
2. Poincare reciprocity permits paired nonzero rates.
3. Relation-valued graph composition permits every rate.
4. Product-formula/Arakelov degree cancellation permits labelled defects.
5. Determinant-line triviality permits arbitrary zeros.
6. Ordinary chain maps cannot turn a zero resolved square into nonzero scalar curvature.
7. Abstract localization supplies a triangle but not the arithmetic boundary class.
8. A positive target may erase the principal conormal; nonzero faithfulness is load-bearing.
9. A nonzero source `H¹` period proves source non-erasure but does not identify a resolved target
   boundary with the fixed scalar Cartier fibre.
10. Defining target topology, norm, or harmonic space from Xi evaluation restates RH.
11. Generalized-prime off-line systems remain falsifiers unless excluded by a proved property of
    the literal integer occupation/BV/Gamma/Arakelov source.

## Gates

- [x] resolved-flat/scalar-curved correction incorporated
- [x] five programs stated with distinct theorem and open-core boundaries
- [x] internal corpus collision audit
- [x] targeted primary-literature audit through 4 August 2026
- [x] dependency-closed paper proof of generic two-record resolution
- [x] dependency-closed paper proof of function-field scalar curvature formula
- [x] dependency-closed paper proof locating purity at positive Frobenius similitude
- [x] dependency-closed paper proof of divisor-free source-pure selection theorem
- [x] relation-valued reciprocity classified as exact but nonselective
- [x] Arakelov degree correction separated from determinant/purity content
- [x] unconditional Lean formalization of generic two-record resolution and source-pure selection
- [ ] unconditional Lean formalization of the literal function-field `(F1)`--`(F3)` bridge
- [x] construct retained prime-isotropy relative class and strict resolved-Xi chain map
- [x] construct source Stokes regulator descending to `H¹` and detecting the class with period one
- [ ] construct Route-R graded variable-ideal regular/singular Cartier comparison
- [ ] construct infinity-corrected relative determinant character
- [ ] prove coefficient-faithful nonzero identification of resolved and fixed Cartier daggers
- [ ] RH

## Literature

- P. Deligne, *La conjecture de Weil I*, Publ. Math. IHES 43 (1974), 273--307.
- A. Connes, C. Consani, M. Marcolli, *The Weil proof and the geometry of the adeles class space*,
  https://arxiv.org/abs/math/0703392.
- A. Blumberg, M. Mandell, *Localization theorems in topological Hochschild homology and
  topological cyclic homology*, https://arxiv.org/abs/0802.3938.
- L. Hesselholt, *Topological Hochschild homology and the Hasse--Weil zeta function*,
  https://arxiv.org/abs/1602.01980.
- S. Paycha, S. Rosenberg, *Curvature on determinant bundles and first Chern forms*,
  https://arxiv.org/abs/math/0009172.
- C. Deninger, *Analogies between analysis on foliated spaces and arithmetic geometry*,
  https://arxiv.org/abs/0709.2801.
- M. Flach, B. Morin, *Weil-etale cohomology and zeta-values of proper regular arithmetic
  schemes*, https://arxiv.org/abs/1605.01277.
- A. Connes, C. Consani, H. Moscovici, *Zeta zeros and prolate wave operators*,
  https://arxiv.org/abs/2310.18423.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*,
  https://arxiv.org/abs/2511.22755.
