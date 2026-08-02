# Canonical finite provenance support for complete shell observables

- **ID:** `relative-shell-canonical-provenance-support`
- **Stage:** 3-formalized
- **Type:** CANONICAL SOURCE INVARIANT / COMPLETE BOOLEAN FIELD CONSEQUENCE / ANTI-THEATRE INFRASTRUCTURE
- **Label:** `DAC_RELATIVE_SHELL_CANONICAL_PROVENANCE_SUPPORT`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** Every observable in the full complete-shell differential field has a unique least
  finite set of private shell labels.  Membership in any shell-subset field is exactly containment
  of this canonical support.  Common zeta has empty private support, private shell \(m\) has
  singleton support, and field operations or differentiation cannot manufacture a label outside
  the input support.

## 1. From finite presentation to canonical provenance

Let \(\Lambda=\{m\in\mathbb N:m\ge12\}\), and let
\[
 \mathcal F_A
 =
 \mathbb C(s)\langle \zeta,\ H_m:m\in A\rangle_\partial
 \qquad(A\subseteq\Lambda)
\]
be the complete family of relative shell differential fields.  The updated source-horizon theorem
proves:
\[
 \bigcap_{i\in I}\mathcal F_{A_i}
 =
 \mathcal F_{\cap_iA_i}
 \quad(I\ne\varnothing),
 \tag{1}
\]
and every \(x\in\mathcal F_A\) belongs to \(\mathcal F_C\) for some finite
\(C\subseteq A\).

For \(x\in\mathcal F_\Lambda\), define its private source support by
\[
 \operatorname{src}(x)
 =
 \bigcap_{\substack{A\subseteq\Lambda\\x\in\mathcal F_A}}A.
 \tag{2}
\]
The family in (2) is nonempty because \(x\in\mathcal F_\Lambda\).  Equation (1) gives
\[
 x\in\mathcal F_{\operatorname{src}(x)}.
 \tag{3}
\]
By definition, \(\operatorname{src}(x)\subseteq A\) for every presentation
\(x\in\mathcal F_A\).  Conversely, monotonicity and (3) show that
\[
 \boxed{\quad
 x\in\mathcal F_A
 \iff
 \operatorname{src}(x)\subseteq A.
 \quad}
 \tag{4}
\]

Choose any finite presentation \(x\in\mathcal F_C\).  Minimality gives
\(\operatorname{src}(x)\subseteq C\), so \(\operatorname{src}(x)\) is finite.  Therefore
\(\operatorname{src}(x)\) is the unique least finite source presentation of \(x\).

This is stronger than existential finite support.  Different algebraic expressions for the same
observable now have one invariant source provenance.

## 2. Provenance calculus

Exact field closure yields:
\[
 \begin{aligned}
 \operatorname{src}(x+y)
   &\subseteq \operatorname{src}(x)\cup\operatorname{src}(y),\\
 \operatorname{src}(xy)
   &\subseteq \operatorname{src}(x)\cup\operatorname{src}(y),\\
 \operatorname{src}(-x)&=\operatorname{src}(x),\\
 \operatorname{src}(x^{-1})&=\operatorname{src}(x),\\
 \operatorname{src}(\partial x)&\subseteq\operatorname{src}(x).
 \end{aligned}
 \tag{5}
\]
The inclusions permit genuine algebraic cancellation; equality would be false in general.

The intrinsic bottom is detected exactly:
\[
 \operatorname{src}(x)=\varnothing
 \iff
 x\in\mathcal F_\varnothing.
 \tag{6}
\]
In particular,
\[
 \operatorname{src}(\zeta)=\varnothing.
 \tag{7}
\]
Differential independence of the complete shell family implies
\[
 H_m\notin\mathcal F_\varnothing.
 \]
Since \(H_m\in\mathcal F_{\{m\}}\), equations (4) and (6) give the atomic law
\[
 \boxed{\quad\operatorname{src}(H_m)=\{m\}.\quad}
 \tag{8}
\]

## 3. Canonical complexity filtration

Define the source grade
\[
 \gamma(x)=
 \begin{cases}
  0,&\operatorname{src}(x)=\varnothing,\\
  \max\{m:m\in\operatorname{src}(x)\},&\text{otherwise}.
 \end{cases}
\]
Let
\[
 \Lambda_{\le N}=\{m\in\Lambda:m\le N\},
 \qquad
 \mathcal F_{\le N}=\mathcal F_{\Lambda_{\le N}}.
\]
Every \(\Lambda_{\le N}\) is finite, and the universal provenance law gives the exact
minimal-stage characterization
\[
 \boxed{\quad
 \gamma(x)\le N
 \iff
 x\in\mathcal F_{\le N}.
 \quad}
 \tag{9}
\]
Consequently
\[
 \mathcal F_{\le0}\subseteq\mathcal F_{\le1}\subseteq\cdots,
 \qquad
 \bigvee_{N\ge0}\mathcal F_{\le N}=\mathcal F_\Lambda.
 \tag{10}
\]
The provenance calculus becomes a non-Archimedean complexity law:
\[
 \begin{aligned}
 \gamma(x+y)&\le\max(\gamma(x),\gamma(y)),\\
 \gamma(xy)&\le\max(\gamma(x),\gamma(y)),\\
 \gamma(-x)&=\gamma(x),\\
 \gamma(x^{-1})&=\gamma(x),\\
 \gamma(\partial x)&\le\gamma(x).
 \end{aligned}
 \tag{11}
\]
Moreover \(\gamma(\zeta)=0\) and \(\gamma(H_m)=m\).

This is an exhaustive algebraic differential-field filtration.  No claim is made that it already
has the mixed nuclear topology needed by the relevant complex.  It is nevertheless a canonical
source-derived scale against which continuity and provenance preservation can be tested.

## 4. Transverse provenance ultrametric

The grade filtration canonically produces a strong source seminorm.  Define
\[
 p(x)=
 \begin{cases}
  0,&\operatorname{src}(x)=\varnothing,\\
  2^{\gamma(x)},&\operatorname{src}(x)\ne\varnothing.
 \end{cases}
 \tag{12}
\]
Adding an element of \(\mathcal F_\varnothing\) does not change canonical support.  Equations
(6) and (11) therefore give
\[
 p(x)=0\iff x\in\mathcal F_\varnothing,
 \qquad
 p(x+y)\le\max(p(x),p(y)),
 \qquad
 p(-x)=p(x).
 \tag{13}
\]
Thus \(p\) is a non-Archimedean additive-group seminorm whose radical is exactly the common
differential field.  It descends to an honest non-Archimedean norm on
\[
 \mathcal F_\Lambda/\mathcal F_\varnothing.
 \tag{14}
\]
The quotient is formally equipped with the induced normed additive-group structure.  Private
atoms have exact size
\[
 \boxed{\quad p([H_m])=2^m.\quad}
 \tag{15}
\]
This initially appears to prevent cofinal private-label escape.  Hostile audit gives the sharper
and adverse conclusion.  Every nonzero quotient class has \(p\ge1\) (in fact every atomic class
has \(p\ge2^{12}\)), hence
\[
 \boxed{\quad
 (\mathcal F_\Lambda/\mathcal F_\varnothing,p)
 \text{ has the discrete topology.}
 \quad}
 \tag{16}
\]
Therefore \(p\) is an exact provenance invariant but cannot be the missing mixed
nuclear/complex topology.  In particular, the open core cannot ask for a topology refining
\(p\): a refinement of a discrete topology is still discrete.

## 5. Non-discrete dyadic provenance and exact cofinal escape

The same canonical finite support admits a second, analytically opposite scalarization:
\[
 q(x)=\sum_{m\in\operatorname{src}(x)}2^{-m}.
 \tag{17}
\]
Positivity of every weight, support subadditivity, and exact common-translation invariance give
\[
 \begin{aligned}
 q(x)&\ge0,\\
 q(x+y)&\le q(x)+q(y),\\
 q(-x)&=q(x),\\
 q(x)=0&\iff x\in\mathcal F_\varnothing.
 \end{aligned}
 \tag{18}
\]
Thus \(q\) also descends to an honest additive-group norm on the same transverse quotient, with
the same exact common-field radical before quotienting.  But now
\[
 \boxed{\quad q([H_m])=2^{-m}.\quad}
 \tag{19}
\]
For the explicit cofinal sequence \(m_n=n+12\),
\[
 [H_{m_n}]\ne0
 \qquad\text{and}\qquad
 [H_{m_n}]\longrightarrow0
 \quad\text{in the \(q\)-topology}.
 \tag{20}
\]
Consequently the \(q\)-topology is non-discrete.  The two source-derived norms are not uniformly
comparable in the fidelity direction:
\[
 \boxed{\quad
 \nexists C\ge0\ \forall u,\quad p(u)\le Cq(u).
 \quad}
 \tag{21}
\]
Indeed (21) on \(u=[H_m]\) would force \(4^m\le C\) for every cofinal \(m\).

Equations (16)--(21) are the exact topology boundary.  Increasing maximum-grade cost retains
cofinal labels only by becoming discrete.  Summable inverse-label mass is non-discrete and has
the exact common radical, but makes cofinal private atoms converge to zero.  This is not a
universal no-go for all locally convex structures; it proves that one provenance norm cannot
simultaneously supply the two required behaviors in these canonical scalarizations.  A viable
mixed topology needs additional source/target seminorms or vector-valued provenance, not a
renaming of either \(p\) or \(q\).

## 6. Coordinate-seminorm positive survivor

The required vector-valued provenance exists canonically at source level.  For every
\(m\in\Lambda\), define
\[
 p_m(x)=
 \begin{cases}
  1,&m\in\operatorname{src}(x),\\
  0,&m\notin\operatorname{src}(x).
 \end{cases}
 \tag{22}
\]
Support subadditivity and negation invariance give
\[
 p_m(x+y)\le\max(p_m(x),p_m(y)),
 \qquad
 p_m(-x)=p_m(x),
 \tag{23}
\]
so every \(p_m\) is a non-Archimedean additive-group seminorm.  Its kernel is not merely
described abstractly:
\[
 \boxed{\quad
 \ker p_m
 =
 \mathcal F_{\Lambda\setminus\{m\}}.
 \quad}
 \tag{24}
\]
Consequently
\[
 \boxed{\quad
 \bigcap_{m\in\Lambda}\ker p_m
 =
 \mathcal F_\varnothing.
 \quad}
 \tag{25}
\]
Thus the full coordinate family separates the transverse quotient.  Private atoms have exact
Kronecker coordinate matrix
\[
 p_m(H_n)=\delta_{mn}.
 \tag{26}
\]

The finite support shadow
\[
 \mathbf p(x)=(p_m(x))_{m\in\Lambda}\in\mathbb R^{(\Lambda)}
 \tag{27}
\]
has support exactly \(\operatorname{src}(x)\), is unchanged by adding a common-field observable,
vanishes exactly on \(\mathcal F_\varnothing\), and satisfies
\(\mathbf p(H_m)=e_m\).  It is deliberately not claimed to be additive or to encode
coefficients.

For \(m_n=n+12\), every fixed coordinate eventually vanishes:
\[
 p_m(H_{m_n})\longrightarrow0
 \qquad(m\text{ fixed}).
 \]
Hence
\[
 \boxed{\quad
 \mathbf p(H_{m_n})=e_{m_n}
 \longrightarrow0
 \quad\text{in the product coordinate topology}.
 \quad}
 \tag{28}
\]
Equations (25)--(28) resolve the apparent scalar conflict.  A Hausdorff separating provenance
family can detect every label exactly while a cofinal sequence attenuates in every fixed
coordinate.  Algebraic nonannihilation is pointwise in the family; uniform scalar lower bounds
are neither necessary nor compatible with the intended non-discrete topology.

## 7. Scalar-homogeneity wall

The coordinate survivor is not yet a locally convex complex topology.  For every \(a\in\mathbb C
\setminus\{0\}\),
\[
 \operatorname{src}(ax)=\operatorname{src}(x),
 \qquad
 p_m(ax)=p_m(x),
 \qquad
 \mathbf p(ax)=\mathbf p(x).
 \tag{29}
\]
This exact scale invariance conflicts with absolute homogeneity.  Formally:
\[
 \boxed{
 \begin{aligned}
 &\nexists\text{ complex seminorm }r
   \quad\forall x,\ r(x)=p_m(x),\\
 &\nexists\text{ complex-linear }\lambda:
   \mathcal F_\Lambda\to\mathbb C
   \quad\forall x,\ |\lambda(x)|=p_m(x).
 \end{aligned}}
 \tag{30}
\]
Scalar \(2\) already proves both contradictions on \(H_m\): the left side must double while
\(p_m(2H_m)=p_m(H_m)=1\).

There is a stronger topology-independent statement.  Equip \(\mathcal F_\Lambda\) with any
topology for which complex scalar multiplication is continuous.  Then
\[
 \boxed{\quad p_m:\mathcal F_\Lambda\to\mathbb R
 \text{ is discontinuous.}\quad}
 \tag{31}
\]
Indeed the scalar path \(a\mapsto aH_m\) has \(p_m(0)=0\) and \(p_m(aH_m)=1\) for every
\(a\ne0\).  Along \(a_n=2^{-n}\), continuity would force the same real sequence to converge to
both zero and one.

This kills a second tempting but invalid completion strategy.  The exact coordinate gauges
cannot themselves be defining seminorms of a nuclear complex vector space, nor continuous
observables on one.  Canonical support must be transported as an algebraic stratification;
homogeneous coefficient, Meyer, and Hodge seminorms must be constructed separately.

## 8. Private hypertranscendence and the finite coefficient-rank wall

The full differential-independence theorem forces more than the scale-invariance obstruction.
Let
\[
 \mathcal F_{\widehat m}:=
 \mathcal F_{\Lambda\setminus\{m\}}
\]
be the deletion field generated by the common zeta mode and every private shell except \(m\).
Restricting the algebraically independent full jet family to the complement of the order-zero
jet \((m,0)\) gives
\[
 \boxed{\quad H_m\text{ is transcendental over }\mathcal F_{\widehat m}.\quad}
 \tag{32}
\]
In particular, for every \(c\in\mathbb C\),
\[
 \boxed{\quad H_m^2-cH_m\notin\mathcal F_{\widehat m}.\quad}
 \tag{33}
\]
Indeed, membership would make \(H_m\) a root of the nonzero polynomial
\(X^2-cX-(H_m^2-cH_m)\in\mathcal F_{\widehat m}[X]\), contradicting (32).

This gives an exact zero-set obstruction which (30) did not establish.  If a complex-linear
functional \(L:\mathcal F_\Lambda\to\mathbb C\) had
\[
 L(x)=0\quad\Longleftrightarrow\quad p_m(x)=0,
\]
then \(L(H_m)\ne0\).  Taking
\(c=L(H_m^2)/L(H_m)\) makes \(L(H_m^2-cH_m)=0\), whereas (33) and the exact deletion-field
kernel of \(p_m\) give \(p_m(H_m^2-cH_m)=1\).  Hence
\[
 \boxed{\quad
 \nexists L:\mathcal F_\Lambda\to_{\mathbb C}\mathbb C
 \text{ linear with }\ker L=\mathcal F_{\widehat m}.
 \quad}
 \tag{34}
\]
The quadratic argument extends to the entire positive power orbit.  For any complex vector space
\(V\) and complex-linear \(L:\mathcal F_\Lambda\to V\) with exact deletion kernel,
\[
 \boxed{\quad
 \bigl(L(H_m),L(H_m^2),L(H_m^3),\ldots\bigr)
 \text{ is complex-linearly independent.}
 \quad}
 \tag{35}
\]
Indeed, a finite relation \(\sum_{n\ge1}a_nL(H_m^n)=0\) places
\(\sum_{n\ge1}a_nH_m^n\) in \(\mathcal F_{\widehat m}\).  Treating that element as the constant
coefficient produces a polynomial relation over \(\mathcal F_{\widehat m}\), which (32)
forbids unless every \(a_n=0\).  Therefore
\[
 \boxed{\quad
 \dim_{\mathbb C}V<\infty
 \ \Longrightarrow\
 \nexists L:\mathcal F_\Lambda\to_{\mathbb C}V
 \text{ linear with }\ker L=\mathcal F_{\widehat m}.
 \quad}
 \tag{36}
\]
Thus replacing the discontinuous \(0/1\) gauge by any finite-rank homogeneous coefficient packet
cannot preserve even its zero set.  Exact linear kernel detection forces infinite coefficient
rank.  This remains a no-go, not a construction of the required infinite-dimensional arithmetic
target.

## 9. Route L consequence

The complete relative Boolean lattice now carries a canonical observable-level provenance
functor.  This sharpens source fidelity:

- “has some finite shell expression” is no longer enough;
- a proposed arithmetic comparison should transport the unique least support, not a
  target-selected presentation;
- common current and private transverse channels are intrinsically separated by empty versus
  singleton support;
- differentiation cannot create private arithmetic incidence ex nihilo;
- any comparison collapsing distinct singleton supports fails a concrete invariant before
  topology, Hodge positivity, or spectral decomposition is considered.

The previously constructed rank-one pointwise-Xi comparison collapses all such support data.
Thus its failure is now expressible as loss of a canonical invariant, rather than only informal
label blindness.

This does not construct the relevant coefficient complex or its comparison.  It supplies an exact
source-provenance obligation, rules out the formerly proposed tactic of refining the
increasing-grade norm, and supplies the exact source coordinate family which the arithmetic
comparison must transport algebraically, not install as continuous complex seminorms.

## 10. Hostile audit

- **Not finite-support theorem renamed.** Existence of some finite \(C\) does not imply a unique
  least \(C\).  Exact arbitrary meets are essential to prove that intersection (2) still generates
  \(x\).
- **Not syntax support.** Support is defined from field membership, so it is independent of the
  chosen expression for \(x\).
- **Not vacuous bottom support.** Private generators are formally proved absent from the common
  bottom and have exact singleton support.
- **No false equality under addition.** Only union upper bounds are asserted, allowing
  cancellation.
- **The topology overclaim was killed, not hidden.** The increasing-grade quotient norm is
  formally discrete.  It is retained only as an exact provenance gauge.
- **Not arbitrary weighting.** The choice \(2^{\gamma}\) is one monotone normalization of the
  canonical grade, and \(2^{-m}\) is one summable normalization of the canonical labels.  No
  uniqueness of either scalarization is claimed.
- **Not a universal topology no-go.** The theorem compares two explicit norms and proves the
  exact nonexistence of a uniform \(p\le Cq\) bound.  It does not classify arbitrary Fréchet or
  nuclear seminorm families.
- **Coordinate family is not a coefficient realization.** The vector \(\mathbf p(x)\) records
  canonical support only.  It is generally nonlinear because cancellation can reduce support;
  no cup, trace, flow, Hodge form, or Meyer coefficient is fabricated from it.
- **Not a locally convex topology by assertion.** Exact support coordinates are formally
  discontinuous for every compatible complex topological-vector-space topology.  Their role is
  algebraic stratification, not homogeneous analytic seminorms.
- **No coefficient-rank overclaim.** Private hypertranscendence proves that every exact-kernel
  complex-linear realization has an infinite independent power image.  It excludes all
  finite-dimensional targets, but neither constructs nor classifies infinite-dimensional
  coefficient realizations.
- **Coordinatewise null does not mean erased.** Every cofinal atom has a different exact active
  coordinate and is nonzero, even though every fixed coordinate eventually vanishes.
- **Cofinal escape is literal.** The non-discrete norm contains an explicit sequence of nonzero
  private-shell quotient classes converging to zero; this is not inferred from suggestive
  language about completion.
- **Not a Hodge or RH theorem.** No positivity, spectral real-part statement, or arithmetic
  relevant-complex comparison is assumed.
- **No computation.** The construction is lattice-theoretic and differential-algebraic.

## 11. Novelty audit

The complete relative Boolean field embedding and existential finite-support theorem are the
immediate updated-paper inputs.  The new claim is the observable-level invariant extracted from
their combination:

1. intersection of all presentations is itself a presentation;
2. that intersection is finite;
3. it is characterized by the biconditional (4);
4. it obeys the provenance calculus (5)--(8);
5. largest indispensable label gives exact least-stage law (9), exhaustive filtration (10), and
   max calculus (11);
6. the grade produces the exact-common-radical non-Archimedean seminorm (12)--(13) and honest
   transverse quotient norm (14)--(15);
7. the increasing-grade quotient topology is discrete (16);
8. dyadic support mass gives a second exact-common-radical quotient norm (17)--(19), with an
   explicit nonzero cofinal null sequence and non-discrete topology (20);
9. no fixed Lipschitz constant controls increasing grade by dyadic mass (21);
10. label coordinates form non-Archimedean seminorms with exact deletion-field kernels (22)--(24)
    and joint common radical (25);
11. private atoms form the exact coordinate basis (26)--(27), whose cofinal sequence converges
    coordinatewise to zero (28);
12. nonzero complex scaling preserves canonical support and every provenance coordinate (29);
13. no complex seminorm or scalar linear coefficient realizes an exact label gauge (30);
14. every exact label gauge is discontinuous in every compatible complex-vector topology (31);
15. every private generator is transcendental over its deletion field (32);
16. every quadratic defect \(H_m^2-cH_m\) retains label \(m\) (33);
17. no complex-linear scalar coefficient has zero set equal to exact absence of label \(m\) (34);
18. every exact-kernel complex-linear comparison has a linearly independent positive power
    image (35);
19. hence every finite-dimensional complex coefficient target fails exact label detection (36).

Repository search found no prior canonical least-support construction for these complete Riemann
shell fields.  The underlying lattice principle is elementary; priority claim is restricted to
its exact realization on this shell differential-field system.  Specialist priority review
remains necessary.

## 12. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/RelativeShellCanonicalProvenanceSupport.lean`.
- `GaloisForLFunctions/RHTower/RelativeShellCanonicalComplexityFiltration.lean`.
- `GaloisForLFunctions/RHTower/RelativeShellProvenanceUltrametric.lean`.
- `GaloisForLFunctions/RHTower/RelativeShellSummableProvenanceTopology.lean`.
- `GaloisForLFunctions/RHTower/RelativeShellProvenanceCoordinateTopology.lean`.
- `GaloisForLFunctions/RHTower/RelativeShellProvenanceScalarHomogeneityWall.lean`.
- `GaloisForLFunctions/RHTower/RelativeShellPrivateHypertranscendenceCoefficientWall.lean`.

Capstones:

1. `relativeShellObservableSupport_mem`;
2. `mem_relativeShellSubsetDifferentialField_iff_support_subset`;
3. `relativeShellObservableSupport_finite`;
4. `exists_unique_relativeShellObservableSupportFinset`;
5. `relativeShellObservableDeriv_support_subset`;
6. `relativeShellCommonObservable_support`;
7. `relativeShellMultiplierObservable_support`.
8. `relativeShellObservableGrade_le_iff_mem`;
9. `relativeShellObservableGrade_add_le`;
10. `relativeShellObservableGrade_mul_le`;
11. `relativeShellObservableDeriv_grade_le`;
12. `relativeShellMultiplierObservable_grade`;
13. `iSup_relativeShellInitialDifferentialField`.
14. `relativeShellProvenanceSize_eq_zero_iff`;
15. `relativeShellProvenanceSize_add_le_max`;
16. `relativeShellProvenanceNonarchSeminorm_kernel`;
17. `relativeShellTransverseNonarchNorm`;
18. `relativeShellTransverseNonarchNorm_multiplier`;
19. `relativeShellTransverseNormedAddCommGroup_discrete`;
20. `relativeShellSummableProvenanceMass_eq_zero_iff`;
21. `relativeShellSummableTransverseAddGroupNorm`;
22. `relativeShellCofinalMultiplier_tendsto_zero`;
23. `relativeShellSummableTransverseNormedAddCommGroup_not_discrete`;
24. `no_uniform_increasingGrade_le_dyadicProvenance`;
25. `relativeShellLabelCoordinateSeminorm`;
26. `relativeShellLabelCoordinateSize_kernel`;
27. `relativeShellLabelCoordinateSize_joint_kernel`;
28. `relativeShellProvenanceVector_support`;
29. `relativeShellProvenanceVector_multiplier`;
30. `relativeShellProvenanceVector_cofinal_tendsto_zero`;
31. `relativeShellObservableSupport_smul`;
32. `relativeShellProvenanceVector_smul`;
33. `no_complexSeminorm_eq_relativeShellLabelCoordinateSize`;
34. `no_complexLinearFunctional_norm_eq_relativeShellLabelCoordinateSize`;
35. `not_continuous_relativeShellLabelCoordinateSize`;
36. `relativeShellMultiplier_transcendental_over_complement`;
37. `relativeShellMultiplier_quadraticDefect_not_mem_complement`;
38. `no_complexLinearFunctional_exact_relativeShellLabelKernel`;
39. `relativeShellLabel_exactKernel_powerImages_linearIndependent`;
40. `no_finiteDimensional_complexLinearMap_exact_relativeShellLabelKernel`.

Direct `lake env lean` and targeted module build pass.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, project `axiom`,
`opaque`, `unsafe`, RH premise, or numerical computation is used.

## 13. Exact survivor

Construct the actual relevant coefficient complex and prove that its arithmetic source
restriction preserves canonical provenance support through the finite rational-Witt stages,
secondary regulator, cup/trace maps, and literal Meyer realization.  Support preservation must be
an algebraic stratification theorem, because the exact support gauges cannot be continuous in a
complex topological vector space.  Independently construct complete nuclear homogeneous
coefficient/Meyer/Hodge seminorms, prove their common analytic radical equals the actual closed
middle-boundary space, and prove the comparison never maps an active algebraic support stratum
into that radical.  The target cannot be finite-dimensional if one coefficient map is required
to have an exact deletion kernel: it must carry the infinite independent power family (35).
Its coefficient structure must retain enough multiplicative information to distinguish the
polynomial cancellation families behind (33)--(36).  The topology must remain compatible with
cofinal attenuation and literal-Meyer Xi decay.  Mere pointwise Xi nonerasure or injectivity on a
chosen presentation is insufficient.
