# Properness of the actual ordered critical-value map

- **ID:** ORDERED-CRITICAL-VALUE-PROPERNESS-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); realization bridge
- **Parent:** `../1-in-progress/finite-planar-polynomial-realization.md`
- **Statement:** For every n, the concrete map from n independent critical positions and one additive constant to n+1 ordered polynomial critical values is proper.

The theorem constructs the polynomial and proves properness unconditionally for every parameter dimension. It does not yet realize prescribed covering monodromy or provide an exhaustion of the actual Xi surface. External novelty is unverified; no web or numerical experiments were used.

## Zero critical-value rigidity [PROVED HERE on paper]

Over an algebraically closed field of characteristic zero, let p be a nonconstant polynomial. If every root of p′ is a root of p, then p has exactly one distinct root. In particular, if p is monic and its next-to-leading coefficient is zero, then p=X^d, where d=degree p.

Proof. Let S be the finite set of roots of p, and m(a)>0 the multiplicity of a∈S. Since p splits, ∑_{a∈S}m(a)=d. Since every derivative root lies in S, splitting p′ gives ∑_{a∈S}ord_a(p′)=d−1. The checked characteristic-zero root-multiplicity derivative theorem gives ord_a(p′)=m(a)−1 for every a∈S. Adding one at each root therefore gives d=(d−1)+|S|. Since d>0, |S|=1. Let a be this sole root. The checked factorization by roots gives p=leadingCoeff(p)(X−a)^d. If p is monic, its next coefficient is −d a, by the checked monic next-coefficient power formula. Centering and characteristic zero force a=0. This proves p=X^d, with all multiplicities accounted for; the constant-polynomial case is excluded explicitly.

This is the exact zero-fiber input for the proposed properness construction. It does not by itself prove properness or polynomial realization.

## Homogeneous properness mechanism [PROVED HERE on paper]

Let E and F be real normed vector spaces, with E a proper metric space. Let H:E→F be continuous, positively homogeneous of an integer degree d>0, and suppose H(x)=0 implies x=0. Then H is proper. More precisely, there is c>0 such that c‖x‖^d≤‖H(x)‖ for every x.

Proof. The unit sphere in E is compact. On it the continuous function ‖H(·)‖ is strictly positive, because no point of norm one is zero. The inspected compact strict-lower-bound theorem supplies c>0 below all these values; it also handles the empty-sphere case. For x≠0, put r=‖x‖ and y=r⁻¹x. Then ‖y‖=1 and H(x)=r^d H(y), giving the claimed inequality. At x=0 it is immediate since d>0. For a prescribed bound A, choose R=max(1,A/c). If ‖x‖>R, then ‖x‖^d≥‖x‖ and ‖H(x)‖≥c‖x‖^d>A. Thus H tends to the cocompact filter, by the inspected norm criterion. Continuity and the proper-map characterization make H proper. This is a finite-dimensional parameter compactness mechanism, independent of any spectral or energy argument.

The application below replaces the additive constant by w^d to obtain ordinary homogeneity. Critical points cᵢ and w all scale with weight one, and the critical values scale with degree d. Properness then descends to the genuine additive-constant map, removing this auxiliary branching from later local-inverse work.

## Actual ordered critical-value map [PROVED HERE on paper]

For each n≥0 put d=n+2 and take parameter space E=C^n×C, with coordinates (c,w). Define the d−1 ordered critical positions a₀=−∑cᵢ and a_{i+1}=cᵢ. Their sum is zero. Set Q_c(X)=∏_{j=0}^{d−2}(X−aⱼ), and let A(Q) be the inspected coefficientwise polynomial antiderivative with constant term zero. Define P_{c,w}(X)=d A(Q_c)(X)+w^d. Define H(c,w)=(P_{c,w}(aⱼ))_{j=0}^{d−2}. Then H:E→C^{n+1} is continuous, is homogeneous of degree d under simultaneous scalar dilation of c,w, has H⁻¹(0)={0}, and is proper.

Proof of polynomial normalization. Q_c is monic of degree d−1. The checked antiderivative theorem gives P′=dQ_c; evaluating the antiderivative at zero gives P(0)=w^d. Thus P has degree d and is monic: its derivative has degree d−1 and leading coefficient d, while the checked characteristic-zero derivative leading-coefficient identity gives leadingCoeff(P′)=d leadingCoeff(P). The coefficient of X^{d−2} in Q_c is −∑aⱼ=0, by the checked product coefficient theorem. The derivative coefficient identity then gives (d−1) times the coefficient of X^{d−1} in P equal to zero. Characteristic zero and d≥2 force this coefficient to vanish, so P is centered.

Proof of continuity. The degree of Q_c is always d−1, so A(Q_c) is the finite sum over 0≤k≤d−1 of Q_c.coeff(k)X^{k+1}/(k+1). Every coefficient of Q_c is a finite sum of products of the continuous linear functions aⱼ; the inspected finite-product Vieta formula makes this identity exact. Evaluating that finite sum at aⱼ and adding w^d uses only sums, products and fixed nonzero denominators, hence H is continuous.

Proof of homogeneity. For any nonzero scalar t, aⱼ(tc)=t aⱼ(c). The two polynomials P_{tc,tw}(tX) and t^dP_{c,w}(X) have identical derivatives: the product of their d−1 critical factors contributes t^{d−1}, and differentiating tX contributes the final factor t. Their values at zero are both t^d w^d. Their difference therefore has zero derivative and zero constant term, hence is zero by the checked characteristic-zero constant-polynomial theorem. Evaluating at each critical position yields H(tc,tw)=t^dH(c,w). Positive real t suffices for properness.

Proof of zero-fiber rigidity. Suppose H(c,w)=0. Every root of P′ is one of the aⱼ, since d≠0 and Q_c is the product of those linear factors. Therefore every derivative root is a root of P. The proved monic-centered critical-zero rigidity gives P=X^d. Every aⱼ is a root of P by H=0, so aⱼ^d=0 and aⱼ=0; hence c=0. Evaluating at zero gives w^d=0, hence w=0. Conversely P_{0,0}=X^d by its derivative and constant term, so H(0,0)=0. The parameter space is finite-dimensional and proper, and the codomain is normed. The proved homogeneous properness mechanism now applies.

This proves the properness input for the specified map, with no monodromy conclusion hidden in it. Surjectivity, local covering away from collisions, prescribed monodromy, and actual finite planar completion still require their own proofs. The w^d parametrization is branched at w=0; it is not a global local coordinate on the space of polynomial constants.

## Remove the artificial constant-coordinate branching [PROVED HERE on paper]

Let B(c,b) be the same ordered critical-value map with polynomial dA(Q_c)+b, using the actual additive constant b. The map T(c,w)=(c,w^d) is continuous and surjective, by the inspected algebraically closed field root-existence theorem, and H=B∘T. B is continuous by the same finite coefficient formula as H. The inspected `isProperMap_of_comp_of_surj` theorem therefore makes B proper. Equivalently, B⁻¹(K)=T(H⁻¹(K)) for compact K, so compactness descends through T. This removes w=0 branching from the map used for the subsequent local-inverse argument; it does not assert any Jacobian theorem yet.

- 2026-10-09 — zero-fiber rigidity, homogeneous properness, and their application to the actual ordered critical-value map pass all Lean checks listed below.


## Lean certificate

Three modules are wired into `HTGeometry.lean`: `PolynomialCriticalZeroFiber.lean` (3 explicit public declarations), `HomogeneousProperMap.lean` (2), and `OrderedCriticalValueMap.lean` (32). All three production leaf builds pass; all 37 public axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`; final `lake env lean` checks of all three actual source files pass with empty logs. The decisive concrete theorem is `GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap.isProperMap_valuesWithConstant`.

The checked family is monic and centered of fixed degree n+2. Properness rules out escaping parameters while the ordered critical values remain in a compact set, including collision limits. The still-open local-inverse, configuration-space, prescribed-monodromy, and actual finite-completion obligations stay on the parent card.

Index refresh passed (`/tmp/hgt-critical-map-index.log`). Global authoritative lint reports two unrelated unreachable modules, `RHTower.CCMSymmetricDecreasingGroundStateRH` and `RHTower.WeilLogShiftTailComparison`; no own-module or forbidden-declaration error (`/tmp/hgt-critical-map-lint.log`).
