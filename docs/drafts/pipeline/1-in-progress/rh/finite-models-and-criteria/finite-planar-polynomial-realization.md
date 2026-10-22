# Polynomial realization of finite planar cover completions

- **ID:** FINITE-PLANAR-POLYNOMIAL-REALIZATION-20261009
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; algebraic rigidity sublemma proved on paper
- **Parent:** `xi-capped-surface-uniformization.md`
- **Statement:** Every finite connected two-mark covering with a simply connected capped surface and one exterior end admits a polynomial realization preserving its oriented peripheral monodromy.

## Why this remains the same target

The actual Xi completion already has its analytic atlas, simple connectedness, and planar-image rigidity. The normalized-exhaustion compactness theorem is now Lean checked. The proposed finite-exhaustion construction still lacks both finite planar completions of actual compact portions and polynomial realizations of those completions. This card attacks realization; it does not replace either missing construction by a premise in an unconditional Xi theorem.

## Corpus audit and attack verdict

The actual corpus search for polynomial critical values finds finite-critical-value composition lemmas, the explicit two-mark polynomial approximation, and critical-point interpolation. The latter only prescribes selected critical points and does not control all critical values or peripheral monodromy. A targeted finite-tree realization search supplied no applicable theorem. These searches are limited evidence, not an absence certificate. No web sources used; external novelty unverified. **BRIDGE:** the following proposed algebraic construction is useful only if its exact topological realization obligation is also discharged.

Candidate mechanism: parameterize monic centered degree-d polynomials by ordered critical points with sum zero and a constant term. Map these parameters to their ordered critical values. Prove this map proper using its weighted homogeneity and zero-fiber rigidity. Over distinct critical values, polynomial variations evaluate at distinct critical points, producing an invertible evaluation map. Properness plus connectedness could give global path lifting and realization. The still-open monodromy obligation is substantial: surjectivity of the critical-value map alone does not select an arbitrary planar covering. A braid-action or equivalent explicit reconstruction must identify its prescribed monodromy, including collision limits to exactly two marked values.

Potential failure of a naive argument: critical-value assignments forget monodromy, and a limiting polynomial may merge branches in an uncontrolled way. Neither parameter surjectivity nor an unlabelled limiting critical-value set suffices for the statement. The first exact algebraic lemma below is independent of these unresolved steps.

## Zero critical-value rigidity [PROVED HERE on paper]

Over an algebraically closed field of characteristic zero, let p be a nonconstant polynomial. If every root of p′ is a root of p, then p has exactly one distinct root. In particular, if p is monic and its next-to-leading coefficient is zero, then p=X^d, where d=degree p.

Proof. Let S be the finite set of roots of p, and m(a)>0 the multiplicity of a∈S. Since p splits, ∑_{a∈S}m(a)=d. Since every derivative root lies in S, splitting p′ gives ∑_{a∈S}ord_a(p′)=d−1. The checked characteristic-zero root-multiplicity derivative theorem gives ord_a(p′)=m(a)−1 for every a∈S. Adding one at each root therefore gives d=(d−1)+|S|. Since d>0, |S|=1. Let a be this sole root. The checked factorization by roots gives p=leadingCoeff(p)(X−a)^d. If p is monic, its next coefficient is −d a, by the checked monic next-coefficient power formula. Centering and characteristic zero force a=0. This proves p=X^d, with all multiplicities accounted for; the constant-polynomial case is excluded explicitly.

This is the exact zero-fiber input for the proposed properness construction. It does not by itself prove properness or polynomial realization.

## Remaining construction obligations

1. **Formalized:** construct the actual finite-dimensional ordered critical-point parameter map, its homogeneous powered-constant version, and zero-fiber rigidity.
2. **Formalized:** properness of both the homogeneous map and the genuine additive-constant map; see `../../../3-formalized/ordered-critical-value-properness.md`.
3. **Local inverse and global surjectivity formalized:** `../../../3-formalized/ordered-critical-value-local-inverse.md` and `../../../3-formalized/ordered-critical-value-surjectivity.md`. Covering, unique path lifting, and connected total space are formalized; see `../../../3-formalized/ordered-critical-value-covering.md`.
4. Realize prescribed planar peripheral monodromy and control collisions to the two marked fibers.
5. Separately construct compatible finite planar completions of compact portions of the actual Xi surface.

## Log

- 2026-10-09 — candidate and failure modes recorded; zero-fiber rigidity has a complete paper proof from inspected corpus root/multiplicity identities. Lean verification next. No unconditional polynomial realization or RH result claimed.

## Homogeneous properness mechanism [PROVED HERE on paper]

Let E and F be real normed vector spaces, with E a proper metric space. Let H:E→F be continuous, positively homogeneous of an integer degree d>0, and suppose H(x)=0 implies x=0. Then H is proper. More precisely, there is c>0 such that c‖x‖^d≤‖H(x)‖ for every x.

Proof. The unit sphere in E is compact. On it the continuous function ‖H(·)‖ is strictly positive, because no point of norm one is zero. The inspected compact strict-lower-bound theorem supplies c>0 below all these values; it also handles the empty-sphere case. For x≠0, put r=‖x‖ and y=r⁻¹x. Then ‖y‖=1 and H(x)=r^d H(y), giving the claimed inequality. At x=0 it is immediate since d>0. For a prescribed bound A, choose R=max(1,A/c). If ‖x‖>R, then ‖x‖^d≥‖x‖ and ‖H(x)‖≥c‖x‖^d>A. Thus H tends to the cocompact filter, by the inspected norm criterion. Continuity and the proper-map characterization make H proper. This is a finite-dimensional parameter compactness mechanism, independent of any spectral or energy argument.

For application to critical values, a possible way to use ordinary homogeneity is to replace the additive constant by w^d. Critical points cᵢ and w then all scale with weight one; the critical values scale with degree d. This parameter change introduces branching at w=0, which must be retained in any local-inverse argument. Only the generic mechanism above has a complete proof at this point; the actual parameter map, its scaling, and its zero-fiber identification still require construction.

## Actual ordered critical-value map [PROVED HERE on paper]

For each n≥0 put d=n+2 and take parameter space E=C^n×C, with coordinates (c,w). Define the d−1 ordered critical positions a₀=−∑cᵢ and a_{i+1}=cᵢ. Their sum is zero. Set Q_c(X)=∏_{j=0}^{d−2}(X−aⱼ), and let A(Q) be the inspected coefficientwise polynomial antiderivative with constant term zero. Define P_{c,w}(X)=d A(Q_c)(X)+w^d. Define H(c,w)=(P_{c,w}(aⱼ))_{j=0}^{d−2}. Then H:E→C^{n+1} is continuous, is homogeneous of degree d under simultaneous scalar dilation of c,w, has H⁻¹(0)={0}, and is proper.

Proof of polynomial normalization. Q_c is monic of degree d−1. The checked antiderivative theorem gives P′=dQ_c; evaluating the antiderivative at zero gives P(0)=w^d. Thus P has degree d and is monic: its derivative has degree d−1 and leading coefficient d, while the checked characteristic-zero derivative leading-coefficient identity gives leadingCoeff(P′)=d leadingCoeff(P). The coefficient of X^{d−2} in Q_c is −∑aⱼ=0, by the checked product coefficient theorem. The derivative coefficient identity then gives (d−1) times the coefficient of X^{d−1} in P equal to zero. Characteristic zero and d≥2 force this coefficient to vanish, so P is centered.

Proof of continuity. The degree of Q_c is always d−1, so A(Q_c) is the finite sum over 0≤k≤d−1 of Q_c.coeff(k)X^{k+1}/(k+1). Every coefficient of Q_c is a finite sum of products of the continuous linear functions aⱼ; the inspected finite-product Vieta formula makes this identity exact. Evaluating that finite sum at aⱼ and adding w^d uses only sums, products and fixed nonzero denominators, hence H is continuous.

Proof of homogeneity. For any nonzero scalar t, aⱼ(tc)=t aⱼ(c). The two polynomials P_{tc,tw}(tX) and t^dP_{c,w}(X) have identical derivatives: the product of their d−1 critical factors contributes t^{d−1}, and differentiating tX contributes the final factor t. Their values at zero are both t^d w^d. Their difference therefore has zero derivative and zero constant term, hence is zero by the checked characteristic-zero constant-polynomial theorem. Evaluating at each critical position yields H(tc,tw)=t^dH(c,w). Positive real t suffices for properness.

Proof of zero-fiber rigidity. Suppose H(c,w)=0. Every root of P′ is one of the aⱼ, since d≠0 and Q_c is the product of those linear factors. Therefore every derivative root is a root of P. The proved monic-centered critical-zero rigidity gives P=X^d. Every aⱼ is a root of P by H=0, so aⱼ^d=0 and aⱼ=0; hence c=0. Evaluating at zero gives w^d=0, hence w=0. Conversely P_{0,0}=X^d by its derivative and constant term, so H(0,0)=0. The parameter space is finite-dimensional and proper, and the codomain is normed. The proved homogeneous properness mechanism now applies.

This proves the properness input for the specified map, with no monodromy conclusion hidden in it. Surjectivity, local covering away from collisions, prescribed monodromy, and actual finite planar completion still require their own proofs. The w^d parametrization is branched at w=0; it is not a global local coordinate on the space of polynomial constants.

## Remove the artificial constant-coordinate branching [PROVED HERE on paper]

Let B(c,b) be the same ordered critical-value map with polynomial dA(Q_c)+b, using the actual additive constant b. The map T(c,w)=(c,w^d) is continuous and surjective, by the inspected algebraically closed field root-existence theorem, and H=B∘T. B is continuous by the same finite coefficient formula as H. The inspected `isProperMap_of_comp_of_surj` theorem therefore makes B proper. Equivalently, B⁻¹(K)=T(H⁻¹(K)) for compact K, so compactness descends through T. This removes w=0 branching from the map used for the subsequent local-inverse argument; it does not assert any Jacobian theorem yet.

- 2026-10-09 — `PolynomialCriticalZeroFiber.lean` and `HomogeneousProperMap.lean` production leaf builds, all five public axiom audits, and final actual-source checks pass. Their use in the concrete critical-value map is now being checked; all remaining realization obligations stay open.

## Local inverse at distinct critical positions [PROVED HERE on paper]

For the additive-constant map B, if all ordered positions aⱼ(c) are distinct, its complex differential is invertible. Consequently B is a local homeomorphism there by the inspected finite-dimensional inverse function theorem. Distinct critical values imply distinct positions, so this suffices on the preimage of the distinct-value configuration space. This statement is stronger than requiring distinct critical values at the local-inverse stage.

Proof. The coefficient formula already used for continuity shows that B and every coefficient of P=dA(Q_c)+b are complex polynomial functions of the parameters. Hence they are complex smooth. Fix a tangent vector (u,v), and let δaⱼ be the corresponding linear variations of the critical positions. Let δP be the polynomial obtained by differentiating each coefficient of P in this parameter direction. Monicity and centering make the top two coefficient variations vanish, so deg δP≤d−2 (including δP=0). Its constant term is v. Differentiating the finite coefficient identity P′=dQ commutes with the polynomial derivative and gives

δP′=−d∑ⱼ δaⱼ∏_{k≠j}(X−a_k).

At the j-th critical value, the parameter chain rule gives (DB·(u,v))ⱼ=δP(aⱼ)+P′(aⱼ)δaⱼ=δP(aⱼ). Suppose DB·(u,v)=0. The polynomial δP of degree at most d−2 then has d−1 distinct roots aⱼ, so the inspected root-count bound forces δP=0. Evaluate its derivative identity at aⱼ. All summands except j vanish, yielding 0=−d δaⱼ∏_{k≠j}(aⱼ−a_k). The product and d are nonzero, so δaⱼ=0 for every j. The last n positions are the original independent coordinates, so u=0. The constant coefficient of δP is v, so v=0. Thus DB is injective. Domain and codomain both have complex dimension n+1, so DB is bijective and, in finite dimension, a continuous linear equivalence. The inspected complex smooth inverse function theorem gives the claimed local coordinate.

Formal obligations are the exact coefficientwise parameter-derivative adapter, the chain-rule identity at a critical position, the finite root count, and the finite-dimensional equivalence. All have explicit finite algebraic/analytic proofs above; no uniformization or polynomial realization is used. Global realization still requires the configuration-space and monodromy steps.

- 2026-10-09 — actual ordered critical-value properness is complete: three modules, 37 declarations, production leaf builds, standard-only axiom audits, and final actual-source checks pass. The local-inverse proof above is the next active formalization; prescribed monodromy and actual finite planar completion remain unresolved.

- 2026-10-09 — actual local inverse is complete: production build, all 30 standard-only public axiom audits, and final actual-source check pass. The full surjectivity argument is recorded in `../../../3-formalized/ordered-critical-value-surjectivity.md`; prescribed monodromy and finite Xi completions remain unresolved.

- 2026-10-09 — critical-value surjectivity complete: two modules, 11 explicit declarations, production leaf builds, standard-only public axiom audits, and final actual-source checks pass. All ordered tuples, including collisions, are realized. The next exact continuation target and full paper proof are on `../../../3-formalized/ordered-critical-value-covering.md`; prescribed monodromy remains required.

- 2026-10-09 — regular critical-value covering complete: two modules, 20 declarations, all builds, standard-only axiom audits and final-source checks pass. Actual parameter monodromy is transitive on every regular fiber. Collision-fiber finiteness and endpoint convergence are next on `../../../3-formalized/ordered-critical-value-collision-fibers.md`; prescribed polynomial monodromy remains unresolved.

- 2026-10-09 — collision-fiber and endpoint control is fully audited: five modules, 23 declarations, all production builds, standard-only axiom audits and final-source checks pass; see `../../../3-formalized/ordered-critical-value-collision-fibers.md`. Every actual critical-value fiber is finite, and continuous parameter curves have unique endpoints when their values converge. Next: `../../../3-formalized/polynomial-root-square-continuation.md`. Prescribed polynomial monodromy and actual finite planar completions remain open.

- 2026-10-09 — actual polynomial root transport is fully audited: three modules, 29 declarations, all builds, standard-only axiom audits and final-source checks pass; see `../../../3-formalized/polynomial-root-square-continuation.md`. Both boundary routes agree as bijections of actual root fibers, including deformations with critical-value collisions away from the chosen target loop. Next: `../../../3-formalized/ordered-critical-value-collision-path-lifting.md`, constructing the parameter curve through a terminal collision. Prescribed planar monodromy and finite Xi completions remain open.

- 2026-10-09 — actual terminal-collision path lifting is fully audited: two modules, three declarations, all builds, standard-only axiom audits and final-source checks pass; see `../../../3-formalized/ordered-critical-value-collision-path-lifting.md`. Every value path regular before its final time lifts uniquely to a closed parameter path through its collision. Next combinatorial construction: `../../../3-formalized/tree-factorization-hurwitz-transitivity.md`. Actual meridian exchanges and prescribed polynomial monodromy remain open.

- 2026-10-09 — abstract Hurwitz transitivity is fully audited: five modules, 41 explicit declarations, 45 standard-only axiom checks (including four constructors), all production leaf builds and final-source checks pass; see `../../../3-formalized/tree-factorization-hurwitz-transitivity.md`. Every two minimal transposition factorizations of the same full cycle are connected by adjacent product-preserving moves. Actual polynomial branch inertia, exterior monodromy and geometric realization of those moves remain required. Next: construct analytic power coordinates at actual polynomial roots.

- 2026-10-09 — actual simple-branch monodromy is fully audited: eight modules, 21 explicit declarations, all production builds, standard-only axiom audits and final-source checks pass; see `../../../3-formalized/polynomial-local-power-monodromy.md`. For every actual parameter with distinct critical values, a positive circle around each value exchanges exactly two actual roots and fixes all others. Local coordinates, whole-fiber control, the circle and its lifts are constructed. Next: `../../../3-formalized/polynomial-covering-monodromy-identification.md`, matching this transport to native covering monodromy. Exterior monodromy, meridian-product geometry, Hurwitz exchanges and finite Xi completions remain open.

- 2026-10-09 — native polynomial monodromy identification is fully audited: two modules, nine explicit declarations, both builds, all standard-only axiom audits and final-source checks pass; see `../../../3-formalized/polynomial-covering-monodromy-identification.md`. Root-loop transport equals native covering monodromy with unchanged orientation, respects based homotopy, and each constructed positive simple-critical circle is a native transposition. Next: `../../../3-formalized/polynomial-exterior-cycle.md`. Exterior-cycle paper proof also exposes a primitive-coordinate rigidity law deriving degree-many sheets without a finiteness assumption. Remaining meridian-product geometry and Hurwitz exchanges stay explicit.

- 2026-10-09 — actual exterior polynomial monodromy is fully audited: four modules, eleven explicit declarations, twelve standard-only axiom reports and four empty final actual-source checks; see `../../../3-formalized/polynomial-exterior-cycle.md`. For every parameter, including critical-value collisions, a constructed positive large circle acts as one full cycle on exactly n+2 actual covering sheets. Next: `polynomial-rectangle-meridian-product.md`, constructing the meridian-product relation by rectangular strip cancellation and avoiding homotopies. Geometric Hurwitz exchanges, prescribed realization and finite Xi completions remain open.

- 2026-10-09 — seven geometry modules are fully audited (40 declarations): exact strip-boundary products in covering monodromy, actual rectangle/circle and rotating-basepoint homotopies, native monodromy intertwining, and preservation of transpositions/full cycles. Certificates: `../../../3-formalized/path-strip-boundary-product.md` and `../../../3-formalized/rectangle-circle-loop-geometry.md`. Active `polynomial-rectangle-meridian-product.md` now isolates two needed interface strengths: arbitrarily small local transposition circles and an exterior radius explicitly exceeding every critical-value norm. Both have closed paper proofs extracted from their earlier constructors; scratches are prepared. Actual strip instantiation, geometric Hurwitz moves, prescribed realization and finite Xi completions remain open.
