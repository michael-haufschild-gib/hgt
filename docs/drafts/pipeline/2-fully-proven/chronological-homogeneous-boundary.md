# A single physical boundary controls every homogeneous observation norm

**Status:** formalized in seven leaves, 66 declarations (46 theorems, 20 definitions), all individually built, wired, and axiom-audited. Derived from the physical retraction and faithful coordinates (u,c). The weighted approximation problem is classical in form; priority for this chronological reduction is unestablished.

## Radial representation by a realized edge

For g=(a,b,c,d,e) in the physical section, write h=a−e and u=c(1−h²)/4. All gaps are nonnegative and sum to one. Hence

`c+|h|≤c+a+e≤1`.

When c>0, put C=1−|h| and q=c/C. Then 0<C≤1 and 0<q≤1. The realized edge probe E(C)=(1−C,0,C,0,0) has coordinates

`c_E=C`, `u_E=L(C)=C²/2−C³/4=C(1−(1−C)²)/4`.

Since (1−C)²=h², the original coordinates are exactly

`(u,c)=q(u_E,C)`.

The Lean construction uses C=1−|h| and q=c/C uniformly. If C=0 then c=0, and total real division gives q=0; if c=0<C, q=0 again. Both coordinate identities hold at these corners. This represents every observation coordinate pair by a retracted physical edge probe. It does not identify every original five-gap probe with an edge probe; polynomial observation depends only on (u,c).

## Exact norm reduction

Let P∈ℝ[u,c] obey P(qu,qc)=q^kP(u,c) for a natural weight k. Its physical value at g is q^k times its value at E(C). Since 0≤q≤1, its absolute value is bounded by that edge value. Conversely every E(C) is a physical probe. Thus

`sup_(g physical) |P(u(g),c(g))| = max_(0≤C≤1) |P(L(C),C)|`.

The right side attains its maximum because the edge profile is a polynomial on a compact interval. Weight zero consists of constants and satisfies the same conclusion; for positive weight the origin contributes zero.

## Higher-weight recovery as a concrete weighted minimax problem

At weight k≥1, the missing class is u^(k−1)c. The available homogeneous polynomials in A=ℝ[u,c²,c³] have all degree-k monomials except u^(k−1)c. Write a residual as c^k R(u/c), where R has degree at most k and its coefficient of r^(k−1) is one. The exact recovery error is therefore

`max_(0≤C≤1) C^k |R(C/2−C²/4)|`.

Equivalently put r=C/2−C²/4, which maps [0,1] bijectively to [0,1/4], with C=1−√(1−4r). The error becomes

`max_(0≤r≤1/4) (1−√(1−4r))^k |R(r)|`.

This derives the weighted approximation problem from the actual retraction geometry. It supplies a concrete route to higher-weight recovery constants; no formula or asymptotic for those constants is claimed here. The already proved weight-one minimax calculation is its first case.

## Lean coverage and next obligations

All displayed reductions are formal. The source leaves, under `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor`, are:

- `CubicRadialCoordinates`: physical coordinates equal those of a contracted realized edge, including zero corners.
- `CubicHomogeneousBoundary`: half-flow eigenspaces, full homogeneity, radial domination, continuity, and a physical edge maximum.
- `CubicHomogeneousNorm`: actual supremum equals the attained edge supremum; seminorm laws and zero kernel.
- `CubicHomogeneousCoordinates`: explicit linear equivalence of weight k with ℝ^(k+1), its dimension, and the single coefficient excluded by the cusp.
- `CubicWeightedProfile`: dehomogeneous polynomial, degree bound, exact edge value, and equality of physical and weighted norms.
- `CubicWeightedRecovery`: the actual missing observation u^k c, exact residual constraint, and equality of all possible recovery errors with the coefficient-constrained polynomial error set.
- `CubicWeightedInterval`: both inverse coordinate identities and interval bounds, then the exact error set for weight (1−√(1−4r))^k on [0,1/4].

The final theorem is `cubicHomogeneousRecoveryErrors_interval`; its natural parameter k describes weight k+1, so no positive-degree premise is needed. Every new declaration was audited by scratch `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` occur. Exact audit summary: `/tmp/chronological-homogeneous-audit-summary.txt`. Index refresh and authoritative global lint passed.

The [coefficient-duality paper](chronological-weighted-coefficient-duality.md) identifies the unique optimal residual at every positive weight through a classical weighted Chebyshev polynomial. That optimizer theorem, positive optimal gaps, and their root-sum formula remain to formalize. Higher-weight explicit constants and asymptotics remain open. No canonical Hilbert completion is claimed.

For comparison, [Novello–Schiefermayr–Zinchenko, §2](https://arxiv.org/html/2508.08449v1) treats weighted existence, uniqueness, and alternation with weights allowed to vanish. The abstract weighted minimax mechanism supplies no novelty by itself.
