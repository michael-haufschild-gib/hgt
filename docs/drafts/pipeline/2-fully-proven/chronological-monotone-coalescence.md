# Monotone coalescence and sparse pairing probes

**Status:** pointwise coalescence is now formalized and audited in Lean, including preservation of every initially zero gap. The physical section, strong deformation retraction, diamond homeomorphism, and exact readout loss are now formalized and audited. The full cubic norm formula, product unit ball, norm laws, and physical maximum attainment are now formalized and audited in CubicPairings, CubicArcNorm, CubicNorm, and CubicNormLaws (51 declarations). Corpus searches for `multiaffine` found no declarations; ordered-simplex hits concern integration. No priority claim is established. Affinity in one variable and convexity of its absolute value are classical mechanisms.

## Pointwise coalescence theorem

Let F be any finite real linear combination of oriented perfect-pairing products on 2d ordered endpoints, with d≥1. For every nonnegative gap probe g, there is a nonnegative gap probe h such that:

- h and g have the same total variation;
- `|F(h)|≥|F(g)|`;
- no two adjacent gaps of h are both nonzero;
- h has at most d nonzero gaps.

In particular, monotone capacity can be computed on this finite union of sparse faces. This is pointwise domination; its proof requires no existence theorem for a maximizing configuration.

## Proof

Each endpoint occurs in exactly one chord of every pairing. Holding all other endpoint positions fixed, its coordinate occurs in exactly one linear factor of each product. Therefore F is affine in that coordinate, for arbitrary coefficients and orientations.

Suppose two adjacent nonnegative gaps u,v are both positive. Let L,R be the endpoints on either side of their shared endpoint. Their distance is u+v. Moving the shared endpoint to L replaces the gaps by (0,u+v); moving it to R replaces them by (u+v,0). All other gaps remain unchanged. The original coordinate lies between L and R, so affinity expresses its response as a convex combination of the two merged responses. The triangle inequality implies that at least one merged response has absolute value at least the original.

Choose that merge. Both merged probes remain nonnegative and have the same sum of gaps, hence the same variation. Exactly one formerly active gap disappears. Repeating whenever adjacent active gaps remain must terminate, because the nonnegative integer number of active gaps strictly decreases at each step.

At termination, the support is an independent set in the path of 2d−1 physical gaps. At most d vertices of that path can be nonadjacent: group its first 2d−2 vertices into d−1 adjacent pairs, followed by its final vertex. This proves the support bound and all asserted properties.

The reverse inclusion of sparse probes in all probes is immediate; pointwise domination proves equality of the corresponding suprema. The usual compactness of the nonnegative unit simplex and continuity of F also give a maximizing sparse probe, if attainment is desired separately.

## Full five-generator monotone norm

Write the five noncrossing generators on gaps (a,b,c,d,e) as

`ace`, `ad(c+d+e)`, `be(a+b+c)`, `Sbd`, `Sc(b+c+d)`,

with coefficients (A,B,C,D,E) and S=a+b+c+d+e. For the path of five gap indices, the maximal nonadjacent supports are exactly `{0,2,4}`, `{0,3}`, `{1,3}`, `{1,4}`. Hence coalescence reduces the monotone norm to these four faces.

| Support | Restricted response on the unit simplex | Capacity |
|---|---|---|
| `{0,2,4}` | `c(Aae+Ec)` | `J(A,E)` below |
| `{0,3}` | `B ad²` | `4|B|/27` |
| `{1,3}` | `D bd` | `|D|/4` |
| `{1,4}` | `C b²e` | `4|C|/27` |

On the first face, fixing c leaves `ae∈[0,(1−c)²/4]`. Absolute response is convex in ae, so a maximum occurs at ae=0 or ae=(1−c)²/4. The first case is bounded by |E|, already attained at c=1 in the second case. Thus, putting

\[
J(A,E)=\max_{0\le t\le1}\left|\frac A4t(1-t)^2+Et^2\right|,
\]

we obtain the exact formula

\[
\boxed{M(A,B,C,D,E)=\max\left(J(A,E),\frac{4|B|}{27},
\frac{4|C|}{27},\frac{|D|}{4}\right).}
\]

The maxima of xy² and x²y on x+y=1 are 4/27, attained at (1/3,2/3) or its reverse; xy has maximum 1/4. These follow by one-variable differentiation or elementary factorization. All four faces are actual monotone probes, proving both inequalities in the displayed capacity formula. The entire monotone unit ball is therefore the product of the two-dimensional J-ball and three intervals. J is a norm: evaluation at t=1 forces E=0 in its kernel, and then t=1/3 forces A=0.

The coalescence theorem and full capacity formula are formalized. Explicit case formulas for the scalar maximum J and the signed five-generator capacity remain open here.

## A norming complex that retracts to a ring

On the unit simplex, the sparse norming set is the independence complex of the five-vertex path: one filled triangle `{0,2,4}` and three additional edges `{0,3}`, `{1,3}`, `{1,4}`. This is a classical combinatorial complex, not a new topological object.

Its explicit deformation

\[
H_t(g)=(g_0+t g_2/2,\ g_1,\ (1-t)g_2,\ g_3,\ g_4+t g_2/2),
\quad 0\le t\le1,
\]

preserves nonnegativity, sum one, and every adjacent-product condition `g_i g_(i+1)=0`. For example, `(g₀+t g₂/2)g₁=0` follows from the original conditions at edges 01 and 12; the other three conditions are equally immediate. It starts at the identity, ends in the subcomplex g₂=0, and fixes that subcomplex throughout.

The endpoint subcomplex is a four-edge cycle. The map `(g₀,g₁,0,g₃,g₄)↦(g₀−g₁,g₃−g₄)` identifies it with the diamond boundary `|x|+|y|=1`; its continuous inverse uses the positive and negative parts of x and y. Thus H is a strong deformation retraction onto a ring-shaped one-dimensional complex. The homotopy type is classical: [Przytycki–Silvero, Proposition 3.6](https://arxiv.org/pdf/2305.18648) gives the general path formula; their path parameter counts edges, so this case has parameter four.

This retraction preserves the B,C,D observations and annihilates the A,E observations at t=1. Indeed, whenever g₂ is positive the adjacent coordinates g₁,g₃ vanish; when g₂=0 the retraction fixes the point. The retained norm is precisely the three-interval factor above, and the lost observation space is exactly the two-dimensional J-factor, whose curved boundary was already identified in the earlier work.

This gives a concrete limitation of topology as a proxy for observation: the homotopy-equivalent cycle loses an entire normed subspace. The positive survivor is the exact norm decomposition and the explicit lost subspace. The unit norm ball itself remains convex; it is the sparse probe complex that retracts to a ring. CubicRetraction, CubicDiamond, and CubicObservation now prove the actual homotopy, homeomorphism, and exact readout restriction kernel. The intermediate maps H_t need not preserve the five-dimensional observation space, so no such stronger claim is made.

## Exact Lean target

**Formalized:** `EndpointAffinity.lean` proves the arbitrary-gap bridge and endpoint-update affinity. `GapTransfer.lean` proves adjacent transfer identities. `MonotoneMerge.lean` proves nonnegativity, variation preservation, strict support reduction, and a response-improving merge choice. `Coalescence.lean` iterates by strong induction and proves the support bound. All four final leaf builds and 39 declaration axiom audits passed.

SparseCapacity and UnitCapacity now identify the exact supremum on the physical sparse cone and on its unit section. CubicFaces and CubicRealization now prove the actual face classification; CubicNorm proves the exact five-generator norm formula. The implementation retains a terminal unused coordinate and proves that every initially zero coordinate stays zero. The topological spectrum must use the 2d−1 physical-gap complex, rather than the 2d-coordinate auxiliary complex; their topology differs. Terminal-gap deletion and the supremum bridges now formalize this distinction.

Keep general pointwise coalescence separate from maximum attainment and the cubic face classification. No computation is needed for this proof.
