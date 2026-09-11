# Actual Maass-to-model intertwiner

- **ID:** selberg-actual-maass-model-intertwiner
- **Stage:** 1-in-progress — the explicit algebraic correspondence has a paper proof below; its source-side Lean implementation and Hilbert globalization remain unfinished.
- **Type:** THEOREM (paper), not yet THEOREM (Lean)
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

The previous formalization proved C-infinity regularity of the original Maass function and identified the model operators with actual principal-series flow derivatives. The missing mathematical construction was the map between these two actual realizations. The normalized derivative construction below supplies that map on paper, including an explicit inverse.

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

Validation so far:

- Scratch proofs checked with `lake env lean`, with at most one foreground Lean process.
- Only the needed new source operator olean was produced before checking its dependent ladder module.
- Final targeted audit: `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassDifferentialLadder` passed without warnings. It built the source operators in 3.1 seconds and the ladder in 2.5 seconds; all other jobs used the existing cache.
- Both modules wired once into `RHTower.lean`; no umbrella/full build.
- No new axioms, unfinished terms, computational certificates, or heartbeat/recursion/transparency option increases. Expansive operator formulas are not global simp rules.

Further corpus searches used `smooth directional derivative commutator vector field` (deep, complete) and `Iwasawa derivative upperHalfPlane smul --any --module RHTower` (deep, partial). The first returned the existing mixed-derivative and vector-field methods; the second found the Iwasawa scale/phase derivatives needed for the next group-flow step. Source statements were inspected before use. Broad recent arXiv searches for `commutation` and `interpolation` also found [extended Gevrey interpolation](https://arxiv.org/abs/2609.06258): its derivative-growth assumptions do not supply the missing group-flow or quotient-L2 domain identification, so it is not used as a dependency.
