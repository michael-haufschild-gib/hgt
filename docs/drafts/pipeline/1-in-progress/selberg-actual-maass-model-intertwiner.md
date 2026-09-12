# Actual Maass-to-model intertwiner

- **ID:** selberg-actual-maass-model-intertwiner
- **Stage:** 1-in-progress — finite differentiated correspondence, faithful hyperbolic source L2, first ladder energy, actual quotient unitary representation, Iwasawa Haar formula, finite covolume, and faithful nonzero spherical Maass admission to quotient L2 are formalized and individually audited. All-order Hilbert generator domains and cyclic model completion remain unfinished.
- **Type:** THEOREM (Lean, finite differentiated cyclic correspondence and actual nonzero spherical Maass vector in the quotient unitary representation); identification with the completed cyclic model remains open in the formalization.
- **Date:** 2026-09-12
- **Statement:** Every nonzero Maass eigenfunction with (0<\lambda<1/4\) generates, under the actual differentiated right action, a spherical Harish-Chandra module explicitly isomorphic to the corpus model with (s=2\sqrt{1/4-\lambda}\).
- **Scope:** Known representation theory, reconstructed here with the corpus's signs and normalization. No claim of a new proof of Selberg's conjecture.

## Proof chain and precise target

The chain is

\[
 f\longmapsto u_0(g)=f(g i)
 \longmapsto V_f=U(\mathfrak{sl}_2(\mathbb C))u_0
 \mathrel{\mathop{\cong}^{T_f^{-1}}} I_s^{K\text{-fin}}.
\]

Here (V_f) is a subspace of the actual smooth, left-\(\Gamma\)-invariant functions on (G=\mathrm{SL}_2(\mathbb R)). All its operators are differentiated right translations. It is not an abstract module supplied with unproved compatibility fields.

The formalization now proves C-infinity regularity, actual source and model flow derivatives, normalized source ladder identities, and the finite intertwiner. `GaloisForLFunctions.RHTower.MaassSmooth.maassDifferentialModelEquiv` identifies the intrinsically defined differentiated cyclic source with the existing spherical model. The forward map is the explicit normalized derivative construction below; Lean's inverse uses its proved injectivity and range equality. The separate polynomial/evaluation inverse formula below remains a paper formula.

`MaassCongruenceL2` now places the existing finite-coset source vector faithfully in actual hyperbolic L2, with a strictly positive norm equal to the original trace integral, for every real eigenvalue and positive principal congruence level. `MaassLadderL2` admits the first raised/lowered source vectors and the normalized model coefficients at indices 1 and -1; their combined squared norm is exactly twice eigenvalue times source squared norm. This does not assert all-order domains or right-group unitarity.

`RealSL2Haar` proves unimodularity from algebraic perfectness. `IntegralSubgroupQuotientMeasure` constructs a measurable strict fundamental domain, then an actual nonzero, sigma-finite, locally finite, regular invariant measure on G/Gamma for every integral subgroup. `IntegralSubgroupUnitaryRepresentation` builds the complex linear isometric automorphisms, representation multiplication law, literal pullback formula, and joint continuity. This is the ambient quotient Hilbert representation. `RealIwasawaMeasure` now proves its Haar disintegration up to an actual positive scalar. `IntegralSubgroupFiniteCovolume` proves finite quotient volume for every finite-index integral subgroup and full support for every integral subgroup. `MaassQuotientL2` constructs the specified Maass source as a nonzero spherical vector, proves faithful admission for every real eigenvalue and positive principal congruence level, and identifies literal unitary translations. The comparison constant with the old finite-coset norm, including central -I multiplicity, is still unproved. That comparison is no longer needed merely to admit the source: finite covolume and proved global boundedness discharge admission directly.

The existing `maassCyclicAutomorphicRepresentation` is the group-algebra span of **all** right translates. That space must not be silently identified with (V_f), which is stable under the Lie algebra and (K). Noncompact translations generally take finite (K)-support to infinite (K)-support. Extending this correspondence to closed unitary group representations is a further analytic theorem.

The construction is attached to each specified nonzero (f). It does not assert multiplicity one for an entire Laplace eigenspace or choose a distinguished copy when several independent forms have the same eigenvalue.

## 1. Derive the source operators from actual right multiplication

Use coordinates

\[
 g=n_xa_yk_\theta,qquad
 n_x=\begin{pmatrix}1&x\\0&1\end{pmatrix},quad
 a_y=\begin{pmatrix}\sqrt y&0\\0&1/\sqrt y\end{pmatrix},quad
 k_\theta=\begin{pmatrix}\cos\theta&-\sin\theta\\\sin\theta&\cos\theta\end{pmatrix},quad y>0.
\]

Then (gi=x+iy), and the spherical lift is (u_0(x,y,\theta)=f(x+iy)). The existing elliptic regularity theorem upgrades its original C2 regularity to C-infinity. The coordinate functions are smooth, so this is a smooth function on (G).

For a real trace-zero matrix (X), define the genuine differential operator

\[
 (R_Xu)(g)=\left.\frac{d}{dt}\right|_{t=0}u(g\exp(tX)).
\]

This preserves smooth left-\(\Gamma\)-invariant functions: the identity

\[
 u(\gamma g\exp(tX))=u(g\exp(tX))
\]

can be differentiated. It also commutes with taking finite linear combinations. Thus all iterates below are defined on the actual source, and remain automorphic, without a separate assumed covariance theorem.

Take

\[
 A=\begin{pmatrix}-1&0\\0&1\end{pmatrix},quad
 B=\begin{pmatrix}0&-1\\-1&0\end{pmatrix},quad
 C=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
\]

Write \(\mathcal A=R_A,\mathcal B=R_B,\mathcal C=R_C\). At \(\theta=0\), differentiating \(g\exp(tA)\) gives \(x'=0,y'=-2y,\theta'=0\). For (B), at the identity the Möbius velocity is (-1+z^2=-2) at (z=i), and the lower-row phase has derivative (-i). Left multiplication by (n_xa_y) therefore gives (x'=-2y,y'=0,\theta'=-1). For (C), right multiplication adds (t) to \(\theta\).

The matrix identities

\[
 \operatorname{Ad}(k_\theta)A=\cos(2\theta)A+\sin(2\theta)B,qquad
 \operatorname{Ad}(k_\theta)B=\cos(2\theta)B-\sin(2\theta)A
\]

then give, at every point,

\[
\begin{aligned}
 \mathcal A&=-2y\sin(2\theta)\partial_x-2y\cos(2\theta)\partial_y-\sin(2\theta)\partial_\theta,\\
 \mathcal B&=-2y\cos(2\theta)\partial_x+2y\sin(2\theta)\partial_y-\cos(2\theta)\partial_\theta,\\
 \mathcal C&=\partial_\theta.
\end{aligned}
\]

Consequently the actual source operators matching the corpus are

\[
\boxed{
\begin{aligned}
 E&=(\mathcal A-i\mathcal B)/2
   =e^{2i\theta}(iy\partial_x-y\partial_y+(i/2)\partial_\theta),\\
 F&=(\mathcal A+i\mathcal B)/2
   =e^{-2i\theta}(-iy\partial_x-y\partial_y-(i/2)\partial_\theta),\\
 H&=-i\mathcal C=-i\partial_\theta.
\end{aligned}}
\]

In particular, on (h(x,y)e^{2im\theta}), the coefficient operators are

\[
 E_mh=iyh_x-yh_y-mh,qquad F_mh=-iyh_x-yh_y+mh.
\]

These formulas are consequences of the group action, not definitions of unrelated formal jets. Smoothness justifies every product rule and interchange of mixed partial derivatives used below.

## 2. Derive the commutators and the Laplacian relation

The real matrices satisfy

\[
 [C,A]=2B,qquad [C,B]=-2A,qquad [A,B]=-2C.
\]

For the fields (g\mapsto gX), differentiating the coefficient of the second field in the first direction gives (gXY); the opposite order gives (gYX). The second derivatives of a smooth test function cancel in the commutator. Hence ([R_X,R_Y]=R_{[X,Y]}). Complex linear combination gives

\[
 [H,E]=2E,qquad [H,F]=-2F,qquad [E,F]=H.
\]

The essential source-to-Casimir calculation already occurs at weight zero. Put (X=iy\partial_x) and (Y=y\partial_y). Then ([Y,X]=X), and

\[
 F_1E_0=(-X-Y+1)(X-Y)
       =-X^2+Y^2-Y
       =y^2(\partial_x^2+\partial_y^2).
\]

Thus the actual eigenfunction equation gives

\[
 Hu_0=0,qquad FEu_0=-\lambda u_0,qquad EFu_0=-\lambda u_0.
\]

In the corpus convention

\[
 \Omega=FE+\tfrac14(H+1)^2,qquad
 \Omega u_0=(\tfrac14-\lambda)u_0=\tfrac{s^2}{4}u_0.
\]

For a check at every weight, direct expansion yields

\[
 F_{m+1}E_m=y^2(\partial_x^2+\partial_y^2)+2imy\partial_x-m(m+1).
\]

Therefore, with \(\Delta_{2m}=-y^2(\partial_x^2+\partial_y^2)-2imy\partial_x\), the same operator is \(\Omega=1/4-\Delta_{2m}\). This checks the sign of the source Laplacian against the model; it is not an arbitrary conjugated operator.

## 3. Prove the opposite ladder recurrences, rather than assume them

Define actual smooth functions

\[
 u_n^+=E^nu_0,qquad u_n^-=F^nu_0quad(n\geq0).
\]

Induction using the first two commutators gives

\[
 Hu_n^+=2nu_n^+,qquad Hu_n^-=-2nu_n^-.
\]

The zero-weight calculation supplies the initial opposite step. If
\(Fu_n^+=-(\lambda+n(n-1))u_{n-1}^+\), then

\[
 Fu_{n+1}^+=FEu_n^+=(EF-H)u_n^+
 =-(\lambda+n(n-1)+2n)u_n^+
 =-(\lambda+n(n+1))u_n^+.
\]

Similarly, (EF=FE+H) and the negative weight give the other recurrence. Altogether,

\[
\boxed{Fu_{n+1}^+=-(\lambda+n(n+1))u_n^+,qquad
 Eu_{n+1}^-=-(\lambda+n(n+1))u_n^-.}
\]

Iterating back to zero proves

\[
 F^nE^nu_0=E^nF^nu_0
 =(-1)^n\prod_{j=0}^{n-1}(\lambda+j(j+1))u_0.
\]

Every factor is positive when (\lambda>0). Since (u_0\ne0), no vector (u_n^+) or (u_n^-) vanishes. This argument uses neither an assumed irreducible automorphic representation nor an assumed positive invariant form. It works for every positive eigenvalue, before specializing to the complementary interval.

## 4. Normalize to the existing principal-series basis

Set

\[
 s=2\sqrt{1/4-\lambda}\in(0,1),qquad
 a_m=\frac{s-1-2m}{2},quad b_m=\frac{s-1+2m}{2},qquad
 d_n=\prod_{j=0}^{n-1}a_j,quad d_0=1.
\]

All (a_m,b_m) are nonzero. Define

\[
\boxed{v_0=u_0,qquad v_n=d_n^{-1}E^nu_0,qquad
 v_{-n}=d_n^{-1}F^nu_0quad(n\geq1).}
\]

The same denominator works on the negative side because (b_{-j}=a_j). The algebraic identities

\[
 a_mb_{m+1}=-(\lambda+m(m+1)),qquad
 b_ma_{m-1}=-(\lambda+m(m-1))
\]

and the recurrences above prove, for **every** integer (m),

\[
 Hv_m=2mv_m,qquad Ev_m=a_mv_{m+1},qquad Fv_m=b_mv_{m-1}.
\]

The coordinate expressions also show

\[
 R(k_\alpha)v_m=e^{2im\alpha}v_m.
\]

These are exactly `sphericalPrincipalH`, `sphericalPrincipalE`, `sphericalPrincipalF`, and `sphericalKTypeRepresentation` in the corpus. The corresponding normalized compact inducing exponent is **(1-s)**. As a second sign check, (y^{(1-s)/2}e^{2im\theta}) has precisely the coefficients (a_m,b_m) under the actual source differential operators.

## 5. The intertwiner and its injectivity

Let (e_m) denote the basis vector of `SphericalKFiniteModel = ℤ →₀ ℂ`. Define

\[
\boxed{T_f\!\left(\sum_m c_me_m\right)=\sum_m c_mv_m.}
\]

This is a finite sum of actual smooth automorphic functions. The preceding formulas prove (T_f E_s=ET_f), (T_f F_s=FT_f), (T_fH=HT_f), and (T_fR_s(k)=R(k)T_f).

For injectivity, suppose \(\sum_{m\in S}c_mv_m=0\), with (S\subset\mathbb Z) finite. Fix (m\in S) and apply

\[
 P_{m,S}(H)=\prod_{j\in S\setminus\{m\}}\frac{H-2j}{2(m-j)}.
\]

Each denominator is nonzero, and the weight equations give (P_{m,S}(H)v_j=\delta_{mj}v_j). It follows that (c_mv_m=0), hence (c_m=0). All coefficients vanish. This proves injectivity directly. Mathlib's independence theorem for distinct eigenvalues can replace this argument in Lean after the actual source operator is bundled.

The image is exactly (V_f): every (v_m) is an explicit derivative word in (u_0), while the span of the (v_m) contains (u_0) and is stable under (E,F,H). Since those operators span the complexified Lie algebra, it is stable under every derivative word. It is also stable under (K), by the displayed character equation.

Thus **[PROVED HERE, on paper]**

\[
 T_f:I_s^{K\text{-fin}}\xrightarrow{\sim}V_f
\]

is an actual ((\mathfrak g,K))-intertwiner, uniquely normalized by (T_f(e_0)=u_0). Uniqueness follows because the same nonzero ladder coefficients generate every (e_m) from (e_0).

The requested **Maass-to-model** map is (\mathcal I_f=T_f^{-1}). Composing it with the existing `sphericalModelCompactKFiniteEquiv s` gives the actual finite compact-picture target, where (e_m(k_\theta)=e^{2im\theta}).

## 6. Explicit inverse by derivatives and a single nonzero evaluation

Choose (z_*=x_*+iy_*\) with (f(z_*)\ne0), and put (g_*=n_{x_*}a_{y_*}). This exists from the original nonvanishing condition. Let

\[
 q_n=\prod_{j=0}^{n-1}\frac{s+1+2j}{2},qquad
 D_m=\begin{cases}F^m&m\geq0,\\E^{-m}&m<0.\end{cases}
\]

The normalized recurrences give (D_mv_m=q_{|m|}u_0). All (q_n>0).

If (w\in V_f) and (S) contains its finite weight support, then

\[
\boxed{
 \mathcal I_f(w)=
 \sum_{m\in S}
 \frac{\bigl[D_mP_{m,S}(H)w\bigr](g_*)}
      {q_{|m|}f(z_*)}\,e_m.}
\]

Indeed, if (w=\sum c_mv_m), each summand's scalar is exactly (c_m). This proves that the formula is independent of (S), the selected nonzero evaluation point, and any expression for (w). There is no division by the Maass function as a function, so its nodal set causes no problem.

The support need not be discovered by a spectral theorem: if (w) is expressed using derivative words of length at most (L), use (S=\{-L,\ldots,L\}). Each application of (E,F,H) shifts the weight by at most one. The formula then uses a finite polynomial in the actual differential operators.

## 7. What this closes, and what it does not

The paper proof closes source-side Casimir compatibility, explicit construction, both ladder directions, nonvanishing of every weight, injectivity, surjectivity onto the differentiated cyclic module, and compatibility with the existing finite compact picture. None requires Fourier inversion, Hecke multiplicity one, a spectral decomposition, an assumed local-factor identification, or a positive-form hypothesis.

The following are still distinct tasks:

1. **Lean closure of this actual construction.** Bundle the original smooth automorphic functions; derive the three right-flow operators there; prove the source commutators and `F E u₀ = -λ • u₀`; construct and prove the normalized ladder. A structure which merely assumes these relations is not the missing result.
2. **Hilbert/group globalization.** Show these actual derivatives lie in the appropriate quotient (L^2) domains, prove the adjoint relations, and extend the finite intertwiner to the closed unitary representations. The pointwise C-infinity theorem alone does not imply smoothness as an (L^2) vector. The existing group-algebra cyclic space has a different definition.
3. **Arithmetic exclusion.** The model at (0<s<1) is itself unitarizable, as the corpus already proves. Identifying it therefore produces no contradiction. The Selberg route still needs an arithmetic argument, such as suitable unbounded-degree automorphic lifts together with their actual local parameter compatibility and generic-unitary bounds. The scalar packet obstruction is not a substitute for those representation-theoretic theorems.

A useful globalization consistency check, once the analytic domains are proved, is

\[
 \frac{\|v_{m+1}\|^2}{\|v_m\|^2}
 =-\frac{b_{m+1}}{a_m}
 =\frac{2m+1+s}{2m+1-s}.
\]

For (m\geq0), this recovers exactly the already formalized complementary weights; the negative weights are their even extension. This identity follows from (E^*=-F), but that adjoint relation on the actual Maass derivatives is **not** established by the algebraic proof above and is not counted as a new proved result here.

### Explicit check that the finite model is not a full group target

The existing compact action gives, for (t\ne0),

\[
 [\pi_s(\exp(tA))e_0](k_\theta)
 =\bigl(\cosh(2t)+\sinh(2t)\cos(2\theta)\bigr)^r,qquad
 r=(s-1)/2\in(-1/2,0).
\]

This is not a finite Fourier polynomial. To prove this without any numerical expansion, write (z=e^{2i\theta}) and (D(z)=a+(b/2)(z+z^{-1})), where (b=\sinh(2t)\ne0). A hypothetical nonzero Laurent polynomial (P(z)) representing the displayed function would satisfy (D(z)zP'(z)=r zD'(z)P(z)) on the unit circle, by differentiating there. Equality on infinitely many points makes it a Laurent-polynomial identity. If (M\in\mathbb Z) is the largest exponent of (P), comparison of the coefficient of (z^{M+1}) gives (M=r), impossible since (r\in(-1/2,0)).

Thus the finite target genuinely cannot carry the full noncompact group action. The positive result is the proved differentiated cyclic correspondence, not a claim that no larger group intertwiner exists. This target correction has a paper proof here; its Lean audit is not marked complete.

### Concrete next attack for the full group intertwiner

For actual quotient-(L^2) realizations, the natural extension on group-cyclic spans would be

\[
 \sum_i c_i R(g_i)\frac{u_0}{\|u_0\|}
 \longmapsto \sum_i c_i\pi_s(g_i)e_0,
\]

where the model spherical vector has norm one. The exact well-definedness obligation is equality of spherical matrix coefficients

\[
 \frac{\langle u_0,R(g)u_0\rangle}{\|u_0\|^2}
 =\langle e_0,\pi_s(g)e_0\rangle.
\]

This equality makes the Gram matrices of any two finite translate sums identical, so the map is well-defined, isometric, and extends to their Hilbert closures. A route to that equality is the radial Casimir equation with spherical normalization at the identity. However, passing the actual Maass eigen-equation to these matrix coefficients and supplying the unitary group model require the analytic domain/globalization work stated above. No equality of matrix coefficients or Hilbert extension is assumed or claimed proved in this card.

## 8. Corpus searches and applicability audit

Used the documented `scripts/formal_tools.py research` command directly, including deep statement, proof-body, and method retrieval. Searches were mechanism-based:

- `cyclic weight vector Casimir sl2 raising lowering intertwiner principal series` — partial; many irrelevant finite-dimensional and cyclic-algebra hits.
- `Maass differential raising lowering Laplacian automorphic weight` — partial; located actual Maass differential identities but no general source-to-model map.
- `construct homomorphism cyclic module universal enveloping algebra annihilator weight recurrence` — partial; overly broad homomorphism results did not supply the construction.
- `raising lowering --any --module RHTower` in deep mode — completed; recovered the model, exact coefficient recurrences, and actual Whittaker-mode calculations.
- `eigenvectors distinct eigenvalues linear independence` in deep mode — completed; recovered the direct general independence theorem. Orthogonality suggestions were rejected: no Hilbert symmetry premise is needed for algebraic independence.
- `left invariant vector field smooth derivative Lie group` in deep mode — partial; recovered Mathlib's manifold vector fields and the corpus's polynomial-jet derivations.
- `eigenspace linearIndependent --any --module Mathlib.LinearAlgebra.Eigenspace` in lexical mode — cross-check of the exact installed declarations.
- `iterate commutator` in deep mode — completed; recovered the induction mechanism for weights of repeated derivatives.

All searched files were inventoried in the reported snapshot, but compiler metadata was mostly pending/source-only. Partial searches are not evidence of absence. Exact source statements were inspected for the dependencies below. No new Lean theorem is claimed from search metadata, and no build was run during this investigation.

| Corpus source | Usable result / exact limitation |
|---|---|
| `formal/GaloisForLFunctions/RHTower/MaassCuspSmoothness.lean` | `IsMaassEigenfunction.contDiffOn`, `MaassCuspEigenform.contDiffOn`: regularity of the original source, already checked in the preceding formalization. |
| `formal/GaloisForLFunctions/RHTower/MaassCuspAutomorphicCorrespondence.lean` | Actual lift (u_0(g)=f(gi)); source nonvanishing and eigen-equation. |
| `formal/GaloisForLFunctions/RHTower/MaassCyclicAutomorphicRepresentation.lean` | Actual group-algebra cyclic span; cannot substitute for the differentiated finite-(K) module. |
| `formal/GaloisForLFunctions/RHTower/RealPrincipalSeriesDerivedDirections.lean` | Model's actual flow derivatives and (E,F,H) normalization; no source intertwiner. |
| `formal/GaloisForLFunctions/RHTower/RealSphericalHarishChandra.lean` | Exact coefficients (a_m,b_m), commutators, Casimir. Reuse, do not duplicate the model. |
| `formal/GaloisForLFunctions/RHTower/RealSphericalIrreducibility.lean` | Nonzero coefficients and model irreducibility. Its submodule condition explicitly includes weight projections; kernel stability under (E,F) alone is not its full premise. |
| `formal/GaloisForLFunctions/RHTower/RealPrincipalSeriesCompactHarishChandra.lean` | Existing `sphericalModelCompactKFiniteEquiv` gives the compact-picture endpoint. |
| `formal/GaloisForLFunctions/RHTower/SelbergExceptionalSphericalModel.lean` | Existing bundled parameter (s=2\sqrt{1/4-\lambda}) and exact scalar relation. |
| `formal/.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean:721` | `Module.End.eigenvectors_linearIndependent'`: directly applicable once actual (H) and the nonzero vectors are bundled; no finite-dimensionality or self-adjointness required. |
| `formal/GaloisForLFunctions/HTGeometry/AffineHypertranscendenceHorizon.lean:35` | `euler_iterate_of_commutator`: its induction is the same weight propagation method. Its field-valued derivation signature is not directly the smooth-function module; reuse the argument rather than claim direct instantiation. |
| `formal/.lake/packages/mathlib/Mathlib/Geometry/Manifold/GroupLieAlgebra.lean` | `mulInvariantVectorField` and its regularity. Requires the actual Lie-group/chart instances; does not instantiate the source representation automatically. |
| `formal/GaloisForLFunctions/HTGeometry/LeftInvariantJetDerivation.lean` | Matrix-field commutator method, but its functions are differential polynomials. It is not a theorem about arbitrary smooth Maass functions. |
| `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMEisensteinActualMaassModeJet.lean` | Actual first raising/lowering identities for specified Whittaker modes. They do not give an arbitrary Maass eigenfunction's all-order cyclic module. Sign conventions require translation. |

The deep engine also proposed an ingredient set combining Whittaker identities with a prolate leakage constant and a different cyclic-algebra lowering operator. That combination was rejected: the objects and operator domains do not match.

## 9. Broad recent-paper search and proof/fail/pivot record

Used broad arXiv queries with `ladder`, `cyclicity`, `Poisson`, `recursion`, `transmutation`, `factorization`, and `observability`, requesting June–September 2026 results. No direct problem-name query was used.

1. **Attempt: a cyclic group representation is already the finite model. Failed.** Its algebraic group span and its differentiated finite-(K) span have different closure properties. The survivor is the explicit isomorphism onto (V_f), with globalization stated separately.
2. **Attempt: recover a cyclic function by division. Rejected.** The zero-free hypotheses in the September paper [Critical cyclicity in Dirichlet-type spaces on the bidisk](https://arxiv.org/abs/2609.09952) do not apply to arbitrary nodal Maass functions. The construction instead divides only by nonzero scalar ladder coefficients and one nonzero value of (f).
3. **Attempt: normalized one-sided ladders automatically intertwine both operators. Incomplete until proved.** The missing opposite recurrence is now derived from the actual commutator and the original Laplace eigen-equation in Section 3. Iterating it proves nonvanishing as well.
4. **Attempt: use an unrelated graded-algebra projection method. Succeeds as a method transfer.** Lemma 6.2 of [Poisson derivations and cohomology of Poisson nilpotent algebras](https://arxiv.org/abs/2607.10782) isolates finitely many homogeneous components using iterated derivations and an invertible Vandermonde matrix. Here the corresponding interpolation polynomial in the actual (H) isolates each (K)-weight, yielding the explicit inverse in Section 6. The paper's Poisson-algebra theorem itself is not applied to Maass forms; the interpolation argument is proved here.
5. **Other broad hits rejected.** A July domain-generalization paper using the acronym LADDER, dark-matter collapse timescale work, and agentic-system observability supplied no applicable identity. The construction does not rely on those papers or infer relevance from a shared word.

## Log

- 2026-09-12 — Recovered prior regularity/derived-action work; searched corpus before proposing new mathematics; derived the actual source vector fields and checked normalization.
- 2026-09-12 — Proved opposite ladder recurrences and all-order nonvanishing; constructed the normalized finite intertwiner and a polynomial/evaluation inverse on paper.
- 2026-09-12 — Kept formal and Hilbert status explicit. No Lean source changes, computations, heartbeat changes, or builds in this investigation.


## Source differential formalization

The source coefficient calculus and all-order ladder argument are now implemented in:

- `formal/GaloisForLFunctions/RHTower/MaassSmoothDifferentialOperators.lean`
- `formal/GaloisForLFunctions/RHTower/MaassDifferentialLadder.lean`

`MaassSmooth.space` consists of actual smooth functions on the upper half-plane. Its directional derivatives use the original real Fréchet derivatives, and multiplication by height uses the actual imaginary coordinate. Smoothness, linearity, mixed-derivative commutation, and the height product rule are proved. The operators `raise` and `lower` are the coefficient formulas of Sections 1–3. Their changing-weight commutator is proved from those differential identities, not assumed.

`laplacian_apply` identifies the smooth-space operator with the existing `positiveHyperbolicLaplacian` definition. `lower_raise_ofMaass` then proves the source equation from the original Maass eigenfunction. `lower_raised` and `raise_lowered` establish both all-order opposite recurrences. `raised_ne_zero` and `lowered_ne_zero` prove nonvanishing for every order and every bundled exceptional-eigenvalue Maass form. `lowerToZero_raised` and `raiseToZero_lowered` prove the exact finite product of the return coefficients.

This closes the coefficient-level differential and ladder portions in Lean. It does **not** yet prove that lifting these coefficient functions to G preserves automorphy or differentiates to these operators at every group point. That source flow identification, the normalized intertwiner assembly, Hilbert globalization, and the higher-rank local classification remain unfinished. The paper proof above is not reclassified as fully formalized.

The next source-flow theorem must identify differentiation of the literal weight lift along inverse diagonal translation, at every group element, with the sum of the lifted `raise m` and `lower m` terms. Compact rotation and the conjugate diagonal direction then separate the two operators and propagate automorphy to the whole ladder.

Validation of the two source modules:

- Scratch proofs checked with `lake env lean`, with at most one foreground Lean process.
- Only the needed new source operator olean was produced before checking its dependent ladder module.
- Final targeted audit: `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassDifferentialLadder` passed without warnings. It built the source operators in 3.1 seconds and the ladder in 2.5 seconds; all other jobs used the existing cache.
- Both modules wired once into `RHTower.lean`; no umbrella/full build.
- No new axioms, unfinished terms, computational certificates, or heartbeat/recursion/transparency option increases. Expansive operator formulas are not global simp rules.

Further corpus searches used `smooth directional derivative commutator vector field` (deep, complete) and `Iwasawa derivative upperHalfPlane smul --any --module RHTower` (deep, partial). The first returned the existing mixed-derivative and vector-field methods; the second found the Iwasawa scale/phase derivatives needed for the next group-flow step. Source statements were inspected before use. Broad recent arXiv searches for `commutation` and `interpolation` also found [extended Gevrey interpolation](https://arxiv.org/abs/2609.06258): its derivative-growth assumptions do not supply the missing group-flow or quotient-L2 domain identification, so it is not used as a dependency.


- All 37 public theorems audited with `#print axioms` in `/tmp/maass_source_ladder_axioms.lean`: only `propext`, `Classical.choice`, `Quot.sound`. Audit log: `/tmp/maass_source_ladder_axioms.log`.
- Generated indexes refreshed successfully (`formal_tools.py index`, 6 changed sources, no removals).
- `formal_tools.py lint` is not globally clean: it reports large pre-existing files and unreachable modules outside this change, including `ThetaCuspHawkingBMHorizonCoordinateJets`, `ThetaCuspHawkingBMHorizonModeOuterUniformBound`, `ThetaCuspHawkingBMPrincipalChannelHorizonJet`, `ThetaCuspHawkingBMSelfChannelHorizonJet`, `ThetaCuspHawkingBMTemporalCurrentHorizonJet`, `AnalyticJetGerm`, `ElementaryHorizonJets`, `JetCoefficientUniqueness`, `SecondEndpointMellinLaurentInterchange`, and `UniformSecondOrderJet`. Neither new Maass module is among the reported failures. These unrelated modules were not modified.
- Both new imports checked for exact single occurrence. No owned Lean processes remain. No commit or push performed.


## Actual group derivatives and automorphic ladders

The next source gap is now closed in `MaassWeightLift.lean`. The literal lift is
`f(g • I) * realSphericalKTypeCharacter m (realIwasawaK g)`. Its right K covariance,
section recovery and injectivity are proved. At every group element, inverse diagonal
right translation differentiates to the sum of the lifted raising/lowering operators;
compact rotation differentiates to weight `2m i`; quarter-rotation conjugated diagonal
translation differentiates to `i` times raising minus lowering. The proof uses actual
Möbius derivatives and the existing Iwasawa character identities. No differential
compatibility is assumed.

`MaassAutomorphicDifferentialLadder.lean` propagates left Γ invariance through these
actual derivatives, for both ladders at every order. It bundles the resulting functions
in the existing `automorphicFunctionSpace`, proves their exceptional-parameter
nonvanishing, and proves independence of every finite set of integer weights using
the existing independent compact characters. Its finite coordinate map is injective.
Both files passed foreground `lake env lean` checks producing only needed oleans and
are wired into RHTower. The final targeted Lake audit remains pending while the
standard spherical coefficient normalization is being completed.

The full proof chain still requires the normalized intertwiner, identification of its
image with the differentiated cyclic module, Hilbert globalization, and arithmetic
exclusion of complementary parameters. No statement here excludes an exceptional
Maass form. Recent broad arXiv searches `rigidity` and `transport` found
https://arxiv.org/abs/2609.10527 and https://arxiv.org/abs/2609.11702. Their positive
curvature and higher-dimensional assumptions do not give an applicable estimate for
this hyperbolic congruence problem; neither is used as a proof dependency.

Corpus search logs for this continuation: `/tmp/maass_group_flow_deep.json`,
`/tmp/maass_group_flow_methods.json`, `/tmp/maass_iwasawa_reuse.json`,
`/tmp/maass_derivative_automorphy_search.json`,
`/tmp/maass_weight_independence_search.json`, `/tmp/maass_ladder_normalization_search.json`.
Both broad complete and narrower partial searches were inspected, including method
source arguments and ingredient sets. Source-only suggestions were checked against
source and Lean; irrelevant Lie-weight, angular-current and transcendence suggestions
were not treated as proofs of the source correspondence.


## Verified finite Maass-to-model equivalence

`formal/GaloisForLFunctions/RHTower/MaassModelIntertwiner.lean` completes the
normalization and source identification. For an actual bundled exceptional Maass
form, `modelStep` uses the existing parameter `2*complementaryExponent` and
`ladderScale` normalizes the actual derivatives. `raise_modelSource` and
`lower_modelSource` prove the existing model coefficients at every integer weight.
`modelToMaass` realizes the standard finitely supported model inside the existing
automorphic function space; independence proves injectivity.

Theorems `modelToMaass_diagonal_hasDerivAt`,
`modelToMaass_quarterDiagonal_hasDerivAt`, and
`modelToMaass_rotation_hasDerivAt` prove pointwise on every group element that
literal right translations differentiate to the existing `E+F`, `i(E-F)`, and `iH`.
`modelToMaass_K` proves compact group intertwining. `modelToMaass_spherical`
identifies the generator with the original Maass function.

The construction also identifies the source intrinsically. `maassDifferentialCyclicSpace`
is the infimum of all complex subspaces containing the original spherical Maass
vector and stable under the two actual noncompact right derivatives.
`modelToMaass_range_stable` and `modelToMaass_range_minimal` prove this definition
agrees with the explicit model image; `modelToMaass_range_eq_cyclic` packages the
equality. Consequently `maassDifferentialModelEquiv` is a linear equivalence from
that intrinsic source space to `SphericalKFiniteModel`. Its inverse identities are
proved. No intertwining, covariance, irreducibility or nonvanishing assertion is
supplied as an unproved input.

The source is finite under K and differentiated right action. It is not identified
with the algebraic span of every noncompact group translate or with a completed
quotient L2 representation. Hilbert globalization, higher-rank generic unitary
bounds and compatible arithmetic lifts remain unfinished. In particular, this
construction does not exclude complementary representations on congruence quotients.

Validation completed:

- `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassModelIntertwiner`
  passed without warnings. Only three new modules rebuilt: MaassWeightLift (15s),
  MaassAutomorphicDifferentialLadder (6.1s), MaassModelIntertwiner (33s). Remaining
  jobs used the existing dependency cache. Log: `/tmp/maass_intertwiner_final_build.log`.
- All 50 public theorems audited through `lake env lean /tmp/maass_intertwiner_axioms.lean`.
  Only `propext`, `Classical.choice`, `Quot.sound`; no new axioms or unfinished terms.
  Log: `/tmp/maass_intertwiner_axioms.log`.
- No heartbeat, recursion or transparency increases; no numerical or native certificates.
  Foreground checking used one Lean process at a time. New modules are wired exactly once.
- Generated indexes refreshed (4 changed sources, no removals); `git diff --check` passed.
- Global lint remains blocked by unrelated unreachable modules:
  ThetaCuspHawkingBMHorizonModeOuterUniformBound,
  ThetaCuspHawkingBMTemporalCurrentClearedDensity,
  ThetaCuspHawkingBMTemporalCurrentClearedDensityBound,
  ThetaCuspHawkingBMTemporalCurrentRadialCutoff,
  ThetaCuspHawkingBMTemporalOppositeCurrentProfile,
  JetCoefficientUniqueness, SecondEndpointMellinLaurentInterchange.
  There are also existing large-file warnings. None concerns the new Maass modules.
  Log: `/tmp/maass_intertwiner_lint.log`.

A further deep corpus search for the Hilbert continuation is saved at
`/tmp/maass_hilbert_followthrough_search.json` (partial; source-only candidates).
Source inspection confirms `SelbergMaassTailEnergy.hyperbolicMass_tail_integrable`
at line 92 proves integrability of actual cusp mass divided by height squared,
and `SelbergMaassBessel.mode_hyperbolicMass_integrable` at line 185 supplies the
modal version. These are usable ingredients for the quotient-L2 bridge; they do
not by themselves provide all-order smooth-vector domains or unitary globalization.

## Actual source L2 admission: current attack (2026-09-12)

The next obstruction is the actual integral norm on the congruence source, not an
inner product transported from the finite model. Deep/method search found
`ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO`, whose hypotheses are
continuity, finite index, actual invariance, and cusp bounds; it does not require
holomorphy. Specializing to exponent zero should prove global boundedness of the
original bundled Maass function for every real eigenvalue. This is stronger than
the initial compact-core/tail proposal and reuses its existing general proof.

Then use `HTGeometry.volume_fd_lt_top` and the actual finite congruence family
`SelbergMaassCongruenceTrace.quotientForm`. The vector of these literal translates
has squared Euclidean norm equal to the existing trace density. Finite-volume
integration gives L2 admission; `density_pos_interior` plus positivity of hyperbolic
measure on open sets proves a strictly positive integral. The target is a nonzero
vector in `Lp (EuclideanSpace complex (Deck N)) 2 (volume.restrict fd)` with its
norm computed by the literal hyperbolic integral. No exceptional-eigenvalue
hypothesis is needed for this admission step.

This finite-coset realization retains the possible central multiplicity from -I.
It is not yet a proof of right-SL2R invariance, the quotient Haar disintegration,
or the all-order derivative domain. Those remain the globalization obstacles.

Searches: `/tmp/maass_quotient_l2_bridge_search.json`,
`/tmp/maass_quotient_l2_methods.json` (partial coverage; methods inspected),
`/tmp/maass_fd_bounded_admission_search.json` (complete; irrelevant holomorphic
suggestions rejected), `/tmp/maass_source_global_bound_methods.json`.
Broad recent arXiv searches for closure/dilation returned arXiv:2609.04003
(mesh refinement complexity) and 2609.03260 (cosmological constraint closure).
Their assumptions do not establish the required measure or operator-domain
identities; neither supplies a proof dependency.

The first scratch construction passed, including recovery of the actual Maass form
from equality of its L2 classes. Follow-up exhaustive source inspection found the
canonical vector already defined in `SelbergMaassCongruenceAverage.sourceVector`
with its exact squared-norm identity. The duplicate scratch definition is removed;
final admission uses that existing vector.

A more consequential existing result is
`SelbergMaassFullGradient.cell_gradient_integrable`, backed by original-source
Stokes, proved cusp flux decay and monotone exhaustion. It supplies precisely the
first-order energy needed for the first actual raising/lowering vectors. The next
attack reuses this result rather than introducing an assumed gradient estimate.
The all-order domain remains open in the formal chain. `PlanarElliptic.local_all_orders`
only proves compactly localized Sobolev membership, so it cannot be used as a
uniform quotient estimate without additional work.

Broad arXiv search for coercivity found [arXiv:2609.03164](https://arxiv.org/abs/2609.03164)
(September 2, 2026). Its energy-decay assertion assumes localized coercivity;
it does not discharge the missing arithmetic spectral estimate. This is rejected
as a direct closure mechanism, not imported as a premise.

## First ladder L2 proof under verification

For the already-defined actual source derivative vector D, set U = i y D_x
and V = y D_y. The first actual differential ladders are R = U - V and
L = -U - V, component by component on each original translated Maass form.
Parallelogram gives ||R||² + ||L||² = 2 y² (||D_x||² + ||D_y||²).
The existing `sourceDerivative_gradient` identifies the right side as twice
`hyperbolicGradient`. Each nonnegative summand is integrable by the existing
`cell_gradient_integrable`; hence both literal vectors have actual L2 classes.
Existing source Stokes and cusp-flux decay give the integrated identity
||R||_L2² + ||L||_L2² = 2 lambda ||f||_L2².

This paper proof uses only the actual bundled exceptional Maass form and proved
source theorems. It is not a quarter-bound proof or a proof of all-order domains.
The current scratch is `/tmp/maass_ladder_l2.lean`; promote only after it passes.

## Verified actual source and first ladder L2 bridge

The preceding scratch proof is now promoted and checked:

- `formal/GaloisForLFunctions/RHTower/MaassCongruenceL2.lean`:
  `source_bounded`, `density_bounded`, `density_integrable`,
  `sourceVector_memLp`, `sourceLp_norm_sq`, `source_mass_pos`,
  `sourceLp_ne_zero`, `sourceLp_injective`. The source is the existing
  `SelbergMaassCongruenceAverage.sourceVector`, not a duplicate definition.
  No exceptional-interval restriction is used for these source admission results.
- `formal/GaloisForLFunctions/RHTower/MaassLadderL2.lean`:
  actual `firstRaised` and `firstLowered` use `MaassSmooth.raised/lowered` on each
  original translated Maass form. Their pointwise identities identify the physical
  derivatives. Existing `SelbergMaassFullGradient.cell_gradient_integrable`
  discharges both L2 obligations. `firstLadderLp_energy` proves the exact combined
  norm identity; `modelSource_one_memLp` and `modelSource_neg_one_memLp` admit the
  already-defined normalized intertwiner coefficients at indices 1 and -1.
  These derivative admission results concern the bundled exceptional interval.

Validation:

- Foreground scratch checks passed, followed by
  `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassLadderL2`.
  Only the two new modules rebuilt (24s and 37s). Other dependency jobs were
  cached; the log contains a pre-existing informational replay from
  `EvenL2LogUnitary`, with no warning or error in the new modules.
  `/tmp/maass_l2_final_build.log`.
- All 21 public theorems passed `lake env lean /tmp/maass_l2_axioms.lean`;
  every axiom list contains only `propext`, `Classical.choice`, `Quot.sound`.
  `/tmp/maass_l2_axioms.log`.
- Both modules are imported exactly once by `RHTower.lean`. No umbrella build,
  heartbeat/transparency increase, numerical certificate, or additional axiom.
  Source forbidden-token scan and scoped `git diff --check` passed.
- Generated indexes refreshed via `scripts/formal_tools.py index`.
  `/tmp/maass_l2_index.log`.

Remaining hard steps are actual quotient Haar disintegration and right-SL2R
isometry, admission of every derivative order, and their Hilbert globalization.
A possible next known-mathematics attack is SL2R unimodularity: its modular
character is invariant under conjugacy; diagonal conjugacy sends n(x) to n(2x)
while n(2x)=n(x)^2, forcing the character to be 1 on unipotents. Diagonals are
conjugate to their inverses. Compactness controls the remaining K factor in
Iwasawa decomposition. This argument still needs actual Lean declarations and
cannot be inserted as an assumed property. Arithmetic exclusion of complementary
spectrum remains a further, unsolved step in the Selberg proof chain.

Final lint result: `scripts/formal_tools.py lint --check-generated` passed;
only existing large-file warnings were emitted. The unrelated unreachable-module
errors reported by the previous turn are absent in this audit. All owned Lean,
build, and search commands finished and their sessions were collected.

## Unimodularity attack (next continuation, 2026-09-12)

Previous turn is verified progress: actual source L2 and first derivative domains
were added and audited. Current target is right invariance of actual SL2R Haar
measure, an input to quotient norm invariance.

Search/source inspection improves the paper plan: installed Mathlib already has
`Matrix.SpecialLinearGroup.SL2.commutator_eq_top` (verify exact namespace in Lean),
proved by transvection generation and explicit commutators. With a real scalar
whose square differs from one this proves perfectness of SL2R. Consequently its
modular character must be trivial, through `Abelianization.commutator_subset_ker`.
The initial compact-K character argument would require continuity of the modular
character, currently a TODO in Mathlib's `MeasureTheory/Group/ModularCharacter.lean`.
The perfectness argument bypasses that analytic gap entirely.

Next prove the actual topological instances, discharge the modular character,
and use `map_right_mul_eq_modularCharacterFun_smul` for the actual Haar measure.
No perfectness, local compactness, or character triviality is to be left as an
unproved assumption in the real-SL2 conclusion.


Unimodularity scratch proof passes. Exact namespace is `Matrix.SL2.commutator_eq_top`.
Concrete topology, Borel structure, local compactness, Polishness, and sigma-finite
Haar measure are supplied in `RealSL2Haar.lean`; targeted final audit remains.

Next conjecture: every integral subgroup acting freely by translation on SL2R
has a measurable strict fundamental domain. Paper mechanism: discreteness gives
an open identity neighborhood meeting each orbit at most once. Translate this
to a countable open cover. Keep, in patch n, exactly those points whose orbit
misses every earlier patch. Countable intersections are measurable; least-index
selection proves existence and patch injectivity proves uniqueness. This attacks
the currently assumed `HasFundamentalDomain` input directly. No finite-covolume
or Maass-L2 comparison is inferred from domain existence.

Broad arXiv searches, checked 2026-09-12: rigidity found Chow–Wang,
https://arxiv.org/abs/2609.11702 (September 10), whose eigenform estimate assumes
positive isotropic curvature in higher dimension. Transport found Weng,
https://arxiv.org/abs/2608.17363 (August 18), using locally compact abelian groups.
Neither hypothesis applies to the present hyperbolic/SL2R problem; no claimed
transfer of their estimates.


## Actual quotient Hilbert representation (2026-09-12)

The least-patch selector conjecture is now proved in Lean. The selector first
removes every earlier orbit-saturated patch from patch n. A least natural index
gives existence; orbit injectivity in each open patch gives uniqueness. This
proves the previously missing fundamental-domain input, not just conditional
periodization. Integer matrix embeddings discharge discreteness and countability
for every actual `realImage Γ` with `Γ : Subgroup SL2Z`.

Three new modules:

- `RealSL2Haar.lean`: actual SL2R topology/Borel/local compactness/Polishness,
  perfectness via `Matrix.SL2.commutator_eq_top`, trivial modular character through
  the units of its commutative codomain, and right Haar invariance.
- `IntegralSubgroupQuotientMeasure.lean`: strict measurable selector, Haar
  fundamental domain, quotient measure, invariance under every actual group
  element, sigma-finiteness, nonzero mass, local finiteness and regularity. The
  stronger positive bound `quotientMeasure (π '' A) ≤ haar A` follows by unfolding
  to the countable translates, and proves local finiteness without finite covolume.
- `IntegralSubgroupUnitaryRepresentation.lean`: actual L2 complex-linear
  isometric automorphisms, multiplication law, a bundled representation, literal
  inverse-translation pullback almost everywhere, joint continuity and inner
  product preservation. Regularity is provided explicitly to keep instance
  search bounded; exponent `2 ≠ ∞` is discharged locally. No limits are raised.

Current validation: combined scratch, needed Haar/quotient oleans, and capstone
`lake env lean` all pass. Final targeted `lake build` and 37-public-declaration
axiom audit are running; no umbrella build is requested.

Precise survivor/frontier: an unconditional ambient unitary representation now
exists for every integral subgroup, even infinite-index ones. This does not claim
finite covolume, nor admission of the actual Maass lift into this quotient L2.
Next bridge: establish the actual Iwasawa measure disintegration, including the
central -I multiplicity, to identify the old finite-coset hyperbolic source norm
with the Haar quotient norm. Then establish all-order differentiated domains
and identify the cyclic Hilbert closure. Unitarity still permits complementary
series; excluding their arithmetic occurrence is a further unproved obstacle.

Possible next paper proof of the measure bridge: use the actual section b(z)
and compact stabilizer K, push hyperbolic volume times normalized Haar(K) through
(z,k) ↦ b(z)k. Left multiplication becomes (z,k) ↦ (gz,c(g,z)k), so hyperbolic
measure invariance plus fiberwise Haar invariance proves left Haar invariance.
Haar uniqueness then fixes the comparison up to a positive scalar. This remains
a paper plan; continuity/measurability, K normalization, and quotient multiplicity
must be proved for the existing actual matrix maps before use.

Final audit for the three quotient modules:

- `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.IntegralSubgroupUnitaryRepresentation`
  passed. Only three modules rebuilt (2.2s, 2.5s, 2.7s); dependencies cached.
  Log: `/tmp/maass_quotient_final_build.log`.
- `lake env lean /tmp/maass_quotient_axioms.lean` passed. Every one of 37 public
  declarations was checked, including instances and definitions: dependencies
  are confined to `propext`, `Classical.choice`, `Quot.sound`.
  Log: `/tmp/maass_quotient_axioms.log`.
- All three imports occur exactly once in RHTower umbrella. Scoped forbidden-token,
  limit-change, whitespace and diff checks pass. No umbrella build was run.
- Generated indexes refreshed twice: the second refresh was justified by other
  concurrent source changes invalidating the first lint check. Stale-index errors
  are now gone. Global `lint --check-generated` still fails ONLY on the unrelated,
  untracked and unwired `ThetaCuspHawkingBMBackgroundDiagonalJet` module.
  That other active work was not edited or built. Final lint log:
  `/tmp/maass_quotient_lint_refresh.log`.
- All owned Lean, lake and search sessions completed and were collected; process
  audit found zero remaining owned Lean/lake processes. No commits or pushes.

The Selberg objective stays active: the actual ambient quotient representation
is now built, while the Iwasawa/Maass norm comparison and subsequent arithmetic
exclusion remain unproved.

## Iwasawa measure attack (next continuation, 2026-09-12)

Previous turn is verified progress: actual integral quotient unitary representation
is built. Current hard target is its comparison with the actual hyperbolic Maass
source norm. Scratch now proves compactness of the literal stabilizer of I from
Mathlib's proper orbit map, and the actual homeomorphism
`g ↦ (g I, (toSL2R(g I))⁻¹ g)` with inverse `(z,k) ↦ toSL2R(z) k`.

Next conjecture: pushforward of hyperbolic volume times normalized Haar on this
literal K is Haar on SL2R. The already proved section cocycle turns left group
translation into a skew product. `MeasurePreserving.skew_product` reduces measure
invariance to actual hyperbolic invariance and left Haar invariance on K. The
homeomorphism supplies local finiteness and positivity; Haar uniqueness then
supplies an actual positive normalization constant. No norm comparison is to be
assumed as a field or hypothesis.


## Verified Iwasawa, finite covolume, and actual Maass admission (2026-09-12)

Three consecutive conjecture/proof steps are now closed in Lean:

1. **Actual Iwasawa Haar:** `RealIwasawaMeasure.lean` (176 lines) constructs the
   literal homeomorphism G ≃ H × K and normalized Haar on the actual compact
   stabilizer. The actual section cocycle makes left translation a
   measure-preserving skew product. Haar uniqueness gives a strictly positive
   NNReal scalar comparing this measure with `realSL2Haar`. Actual unimodularity
   gives inversion invariance. The inverse orbit preimage of the modular cell
   has mass `realIwasawaHaarScale * volume fd`, hence finite mass.
2. **Finite covolume:** `IntegralSubgroupFiniteCovolume.lean` (89 lines) constructs
   a finite translate cover using SL2Z/Gamma. Modular reduction moves g^-1 I
   into fd; the coset representative identity r = A gamma proves that its
   translate projects to [g]. Every cell has the same finite Haar mass, and
   folding into the quotient cannot increase mass. The proof does not assume
   that the subgroup is normal in SL2R. Full support is proved separately from
   the actual fundamental domain and Haar positivity, for every integral subgroup.
3. **Actual source:** `MaassQuotientL2.lean` (138 lines) descends the literal
   function [g] ↦ f(g^-1 I). The original Maass cusp hypotheses give global
   boundedness; finite quotient volume gives L2 membership. Continuity and
   full support prove injectivity and nonvanishing. The actual unitary action
   gives f(h^-1 g I) at [h], almost everywhere, and the actual K fixes the vector.
   Positive principal congruence levels discharge finite-index obligations
   internally; no extra analytic admission or spectral estimate is assumed.

This closes **source admission to the actual Hilbert representation**, not the
identification of the full differentiated ladder with Hilbert generator domains.
The finite algebraic intertwiner and this actual Hilbert vector are now both
constructed; their all-order analytic compatibility is the next missing bridge.
No exclusion of arithmetic complementary series has been proved.

### Searches and applicability

Custom searches preceded construction and inspected statement and method results:
`maass_iwasawa_measure_search`, `maass_skew_haar_methods`,
`maass_finite_covolume_search`, `maass_quotient_embedding_search`, and lexical
`maass_quotient_embedding_lexical` (JSON outputs in /tmp). Initial deep results
were partial/source-only and were not treated as verified theorem applications.
The actual applicable methods were Haar uniqueness, skew-product preservation,
modular reduction, finite-index cosets, and full-support equality of continuous
representatives. Every application was checked in Lean. Suggested finite-ring,
p-adic Iwasawa, and unrelated positive-density arguments were rejected.

Further deep searches `maass_allorder_domain_methods` and
`maass_radial_smoothing_methods` completed without unfinished stages. Their
candidates still required source inspection. `ProlateGlobalDerivativeBounds`
159–181 differentiates a proved integral eigenfunction identity; this is a
useful mechanism, but its band-transform hypothesis is not known for a Maass
source. `PlanarElliptic.local_all_orders` gives each compact localization all
Sobolev orders; it supplies no uniform estimate over cusp translates.

### Next attack: radial smoothing, with exact remaining obligations

Attempt A was to infer global derivative bounds from existing local smoothness.
That implication is insufficient: local bounds may grow through the cusp.
A viable strengthening is a uniform interior elliptic estimate after hyperbolic
rescaling, but the searched corpus did not supply that estimate for this source.
This route is not retired.

Attempt B uses a concrete integral eigenfunction identity. Let M_z(r) average f
on the hyperbolic circle of radius r centered at z. The target Darboux identity is

    (sinh(r) M_z'(r))' + lambda sinh(r) M_z(r) = 0,
    M_z(0) = f(z).

For differences with zero initial value, integrate twice. The Volterra kernel
has integral tanh(t/2), bounded by t/2. On [0,R], this bounds the sup norm by
`abs(lambda) * R^2 / 4` times itself; choosing this coefficient below one proves
local uniqueness even at the singular radius zero. Comparing with a point
where f is nonzero then gives M_z(r) = phi(r) f(z), with phi(0)=1. A compact
radial smooth kernel supported where Re(phi)>1/2 gives an actual nonzero scalar
c with U(kernel)f = c f. Differentiating the compact kernel then supplies actual
Hilbert generator derivatives. This would avoid assuming uniform cusp bounds
or the unproved finite-coset normalization constant.

**Status: proof mechanism, not a dependency-closed theorem yet.** Missing Lean
steps: actual Maass circle Darboux identity, local Volterra uniqueness, radial
integration for the actual Haar coordinates, compact smooth kernel construction,
and Hilbert-valued differentiation under the actual representation integral.

A concrete cross-topic source was found: `RHTower.D4BMNativeCircle.mean_radial_action`
in `ThetaCuspHawkingBMNativeCircleMean.lean:191` proves the circle Darboux identity
for the actual theta potential. Its proof differentiates compact angular
integrals and cancels the periodic angular second derivative. The companion
`ThetaCuspHawkingBMNativeCircleSource` contains actual circle chart derivatives.
These statements specialize to that theta source and cannot be directly applied
to Maass forms. Their proof mechanism can be generalized in a fresh module;
existing heartbeat/transparency settings in those files must not be copied.
No higher-domain theorem is claimed from these hits.

### Broad recent arXiv screening

Single-word searches included disintegration, averaging, smoothing, and rigidity.
Opened primary arXiv abstracts and assessed the stated hypotheses/results:

- [Averaging Principle for Ordinary Differential Equations in a Multiscale Random Environment](https://arxiv.org/abs/2608.02319)
  (August 3): fast-component invariant measures and ergodicity are inputs; no
  needed arithmetic spectral exclusion follows.
- [Averaging Principle and Pullback Attractor Convergence for McKean–Vlasov Stochastic Reaction–Diffusion Equations](https://arxiv.org/abs/2608.09319)
  (August 10): the strong global conclusion uses contraction; it does not supply
  the missing estimate.
- [Sharp Metric Cotype Inequalities for L1 via Nonlinear Cut Smoothing](https://arxiv.org/abs/2609.08749)
  (September 8, revised September 9): finite cut representations and nonlinear
  torus inequalities. No applicable SL2 Hilbert generator theorem was identified
  in the abstract; this is screening, not a full-paper audit.
- [Pinching and Tensorial Rigidity for Ergodicity of Frame Flows](https://arxiv.org/abs/2608.09600)
  (August 10): closed negatively curved manifolds and ergodicity under curvature
  pinching. The stated result gives no quantitative arithmetic eigenvalue bound
  for the congruence quotient. The occurrence of 1/4 is not evidence of transfer.

### Verification

- Final targeted command `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassQuotientL2`
  passed. Exactly the three new modules were built (12s, 5s, 23s); the other
  dependencies were cached. The 8808-job dependency traversal is not an umbrella
  build. Log `/tmp/maass_iwasawa_final_build.log`.
- `lake env lean /tmp/maass_iwasawa_axioms.lean` passed for all 43 public
  declarations, including definitions and instances. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur. No added axioms or placeholders.
- No raised heartbeats, transparency overrides, or computation certificates in
  the new code. One owned foreground Lean process at a time.
- Each new module occurs once in the RHTower umbrella. No umbrella/full build.
- Source lint passed. Generated lint initially found stale LEAN_API, LEAN_GAPS,
  and LEAN_OVERVIEW; the documented index refresh was run. Final generated lint
  status is recorded below after collection.

Final collection: `scripts/formal_tools.py lint --check-generated` passed after
index refresh (`/tmp/maass_iwasawa_generated_lint_final.log`). Existing large-file
warnings concern other modules. Scoped diff/whitespace/forbidden-token checks
passed. All owned Lean, lake, lint, index and search sessions completed and were
collected. Process audit found zero owned Lean/lake processes. No commit or push.
The broader Selberg formalization goal remains active.

## Next continuation: actual Maass circle Darboux equation

Previous turn is verified progress (three built/audited modules). Current attack
reuses the existing circle chart's actual radial/angular derivatives and polar
principal-symbol/connection cancellations. Compose that chart with the original
smooth Maass function, derive first/second derivatives by its actual directional
operators, then integrate the angular second derivative to zero by periodicity.
Target is the actual averaged ODE, including radius zero; no scalar multiplier
identity or generator-domain theorem is assumed. Searches for a pre-existing
Maass Darboux bridge and singular Volterra uniqueness run before new code.

### Circle equation attack: paper proof and checked ingredients

The custom Darboux deep search found actual circle-coordinate principal and
connection identities, but no existing general Maass circular-mean theorem.
The angular-average method search exposed compact-rectangle domination and
periodic FTC arguments. Both are now applied to the original source, without
copying the source modules' elaborator settings.

1. Compose the explicit hyperbolic circle chart with the original smooth Maass
   function. Real first/second chain rules and the existing polar cancellations
   give `sinh(r)^2 F_rr + sinh(r)cosh(r) F_r + F_theta_theta =
   -sinh(r)^2 lambda F`. This scratch proof passed, including smoothness,
   periodicity, and the radius-zero chart identity.
2. Normalize angular Lebesgue integration by `1/(2*pi)`. Compact rectangles
   supply the bounds for differentiation under the integral. Smoothness, two
   derivative interchanges, and zero mean of a periodic derivative passed.
3. The Volterra search returned theorems requiring regular bounded kernels;
   those do not directly settle the singular origin. Pivot to positive-eigenvalue
   energy uniqueness: continuity of the multiplied ODE forces `u'(0)=0`;
   `E = |u'|^2 + lambda |u|^2` satisfies
   `E' = -2 coth(r) |u'|^2 <= 0` for `r>0`. Thus a smooth zero-trace solution
   vanishes on `r>=0`. This proof passed in scratch for every positive real
   lambda. The nonpositive-lambda case is not asserted by this lemma.
4. The capstone now being checked averages the actual polar equation and applies
   uniqueness to `g(w) M_f(z,r) - f(z) M_g(w,r)`. This derives the scalar action;
   neither a multiplier identity nor an intertwining premise is assumed.

The smooth-kernel deep search completed (snapshot inventory complete, compiler
metadata predominantly source-only). `UnitaryFlowSmoothing` gives bounded
one-parameter convolution and commutation, but its source does not prove the
needed SL2 smooth-vector theorem. Its finite-dimensional block statements also
require compactness; they cannot be used as an arithmetic spectral gap.

### Additional broad recent-paper screening

Broad arXiv searches used `Volterra` and `transmutation`. Primary abstracts opened:

- [On (fake) Stationarity in Stochastic Volterra Equations with Affine Drift and Regular Kernels](https://arxiv.org/abs/2608.31099)
  (August 31): regular stochastic kernels and moment stationarity; no theorem
  resolves the singular radial initial point here.
- [Sharp logarithmic corrections for a strong-weak Lotka-Volterra competition system](https://arxiv.org/abs/2608.11956)
  (August 12): parabolic comparison and spreading fronts; no applicable SL2
  generator estimate identified.
- [Transmutation Timescales for Dark Matter Induced Collapse of Compact Stars into Black Holes](https://arxiv.org/abs/2608.10594)
  (August 11): accretion and collapse ODEs, not the needed radial uniqueness law.

These are abstract-level relevance screens. No result from these papers is an
input to the Lean proof, and no unrelated paper is claimed to settle an
arithmetic obstruction. The successful pivot is the explicit decreasing energy
of the actual positive-eigenvalue radial equation.

### Final checked result of this continuation

Four new modules, 565 lines total:

- `HTGeometry/SmoothAngularAverage.lean`: compact normalized angular averaging,
  smoothness, two radial derivative interchanges, and periodic derivative cancellation.
- `HTGeometry/HyperbolicRadialODE.lean`: energy uniqueness at the singular
  initial point for every positive real eigenvalue.
- `RHTower/MaassCircleDifferential.lean`: the original Maass source's polar
  Laplacian identity, derived from actual directional derivatives and existing
  circle-coordinate identities.
- `RHTower/MaassCircleMean.lean`: actual Darboux equation and
  `mean_cross_mul` for any two Maass cusp eigenforms with the same positive
  eigenvalue, even for different subgroups. `exists_mean_multiplier` derives a
  smooth scalar multiplier, normalized to one at radius zero, from the original
  source's nonvanishing. No averaging or intertwining law is assumed.

The complete capstone passed in scratch. Final targeted command
`LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassCircleMean`
passed: exactly four new modules built (19s, 8.9s, 40s, 5.2s), with all remaining
12611-job dependency traversal cached. No umbrella or full build. All 29 public
declarations passed `/tmp/maass_circle_axioms.lean`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No raised settings, new axioms,
placeholders, computation certificates, or new-module warnings. Each module
appears exactly once in its own theorem-area umbrella.

`index` refreshed LEAN_API, LEAN_GAPS, LEAN_OVERVIEW and the search database
(11 changed files). Both source lint and generated lint exit with the same
unrelated error: untracked `RHTower/MobiusThetaNativeMeyerAdmission.lean` is
unreachable from its umbrella. This continuation did not edit that module or
wire another worker's unfinished source. Therefore the global lint gate is NOT
reported as passing. Scoped imports, whitespace and forbidden-token checks pass.
Logs: `/tmp/maass_circle_final_build.log`, `/tmp/maass_circle_axioms.log`,
`/tmp/maass_circle_lint.log`, `/tmp/maass_circle_generated_lint.log`,
`/tmp/maass_circle_index.log`.

### Next obstacle attack: transfer derivatives to the circle kernel

A more direct route may avoid the outstanding Haar polar-integration step.
This paragraph records a paper calculation, NOT a Lean theorem yet.

Write `F_z(r,theta)=f(circlePoint r theta z)`, with `r>0`. For the invariant
base-point operators `X=y*d_x` and `Y=y*d_y`, direct substitution of the already
proved circle derivatives gives the transfer vector fields

```
X_z F_z = sin(theta) * d_r F_z
        + (coth(r)*cos(theta)-1) * d_theta F_z
Y_z F_z = cos(theta) * d_r F_z
        - coth(r)*sin(theta) * d_theta F_z.
```

The coordinate checks reduce respectively to
`sin(theta)*offsetRadial + (coth(r)*cos(theta)-1)*offsetAngular = 1`,
the same combination of height derivatives equal to zero, and the Y
combinations equal to `offset` and `height`. They follow by clearing the
nonzero `sinh(r)` and positive circle denominator, using
`cosh(r)^2-sinh(r)^2=1` and `sin(theta)^2+cos(theta)^2=1`.

Choose a smooth radial weight supported in a small positive annulus where the
proved multiplier has positive real part. Its averaged action on f is `c*f`
with `c != 0`. Integration by parts moves X and Y onto the kernel via the
formal transposes of the two vector fields above. Kernels remain smooth,
periodic and supported in that annulus. Repeating should bound every word in
X,Y applied to f by `|c|^-1 * ||f||_infty * ||transposed_kernel||_1`.
The corpus already proves global boundedness of the original congruence Maass
source and finite quotient measure. These uniform derivative bounds would
therefore give all ladder vectors in L2, and dominated difference quotients
could identify the actual Hilbert generators with the existing differential
ladder. This attacks the current domain gap directly.

Still to prove in Lean: transfer identities; nonzero compact kernel construction;
iterated parameter integration by parts; all-word uniform bounds; Hilbert norm
differentiation and completion. Search each mechanism before new code. Arithmetic
exclusion of complementary series remains a separate open obstacle; no quarter
bound or completed Maass-to-model Hilbert intertwiner is claimed here.

Final process audit: zero owned Lean/lake processes. All build, scratch, axiom, search, lint, and index sessions collected. No commit or push. Goal remains active with verified mathematical progress.

## Continuation: all-order bounds from compact circle kernels

Previous turn is verified progress: four modules and 29 declaration audits passed.
Current attack is the derivative-transfer route recorded above. Search actual
radial/angular transference, compact kernel parameter differentiation, repeated
integration by parts, and nonzero smooth bump construction before implementing.
The target is uniform bounds for the original Maass ladder, hence actual L2
generator domains. A supplied derivative bound is not an acceptable endpoint.
