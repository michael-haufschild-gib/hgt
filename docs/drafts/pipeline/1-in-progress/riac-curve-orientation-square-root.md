# Square-root bounds for actual curve orientation counts

- **ID:** RIAC-curve-orientation-square-root
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md)
- **Statement:** Construct actual orientation-cover counts for odd-degree hyperelliptic curves and prove square-root-scale cancellation using the already derived Stepanov bound, with no assumed Weil-circle input.

## Arithmetic objects

Let `F` have odd cardinality `q`, and let `f∈F[X]` be squarefree of odd
degree `m`. Over the actual extension `E/F` of degree `n!`, use
`C(E)={(x,y):y²=f(x)} ⊔ {∞}` with coordinate Frobenius.

Let `B_n` count Frobenius-stable `S_n`-orbits of `C(E)^n`. Let `A_n` count
stable orbits of `C(E)^n×{±1}` for the action
`σ·(x,ε)=(σ·x,sign(σ)ε)`, with Frobenius fixing the sign coordinate.
Both counts are defined from finite arithmetic sets, independently of a
Möbius sum. The second construction retains the two orientation labels in
degrees zero and one; using `Alt_n` subgroup orbits there would lose them.

## Target comparison and bound

Write `α_i` for the actual reciprocal roots of the hyperelliptic L-polynomial.
The proposed coefficient identity is

`A_n−B_n = [t^n] (1+t)(1+qt) ∏_i(1+α_i t)⁻¹`.

Signed cycle counting should derive it from the actual extension counts
`#C(F_(q^d))=q^d+1−Σ_i α_i^d`. For a fixed `n`, only cycle lengths
`1≤d≤n` occur; each divides `n!`. The [actual fixed-point comparison](../3-formalized/riac-hyperelliptic-fixed-points.md)
is formalized for these lengths. It is not asserted for all iterates in
the finite ambient field.

The existing Stepanov theorem proves `|α_i|≤√q` without assuming that `f`
splits. A product-of-geometric-series bound would then give

`|A_n−B_n| ≤ (2q+2)(n+1)^(m−1) q^(n/2)`.

For fixed curve this is the RH scale `Oε((q^n)^(1/2+ε))`. The general
hyperelliptic coefficient identity and its actual-count interpretation remain
open. The concrete elliptic case below is formalized.

## Inputs and obligations

1. Actual finite curve point sets and coordinate Frobenius are constructed
   in [HyperellipticFixedPoints.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/HyperellipticFixedPoints.lean). The general
   [orientation action and quotient](../3-formalized/riac-orientation-quotient-counts.md)
   are formalized.
2. The cover-minus-base identity with signed transporter mass is formalized
   for every finite equivariant action; instantiate it on the actual curves.
3. The fixed-field comparison and actual root-power-sum count are
   formalized for every permutation cycle length.
4. The [determinant realization](../3-formalized/riac-orientation-determinant.md)
   is formalized: `A_n−B_n=[t^n]det(1+tP_φ)` and
   `Tr(P_φ^d)=#Fix(φ^d)`. The remaining coefficient comparison must
   identify this determinant with the displayed rational generating
   function through degree `n`, using the actual trace values.
5. Instantiate the derived Stepanov bound and audit the resulting inequality.

The [actual elliptic divisor branch](../3-formalized/riac-elliptic-squarefree-divisor-cancellation.md)
uses existing closed places and their proved Euler product to construct a
concrete nonzero square-root-scale calibration directly.

For its orientation comparison,
[FiniteFieldEllipticClosedPoints.lean](../../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/FiniteFieldEllipticClosedPoints.lean)
already identifies points over a closed place with its residue-field
embeddings. [Frobenius transitivity on these actual fibres](../3-formalized/riac-elliptic-frobenius-orbits.md)
is now formalized, including actual projective points and infinity.
The [stable-configuration comparison](../3-formalized/riac-elliptic-stable-orientation.md)
is now formalized. Full point support and closed-place support identify
stable `n`-point subsets with all degree-`n` squarefree divisors. Their
actual Frobenius sign is `(-1)^(n + number of closed places)`, including
singletons. Thus their geometric signed sum satisfies
`J_n=(-1)^n(E_n−O_n)` and `|J_n|≤8(n+1)²(√3)^n`.

The [elliptic quotient comparison](../3-formalized/riac-elliptic-orientation-quotients.md)
is also formalized: `A_n−B_n=J_n`. Signed transporter counting proves it
directly: collisions cancel by an odd swap, each injective tuple has its
support's Frobenius sign, and each `n`-point support has `n!` orderings.
Thus the original cover and base counts satisfy
`|A_n−B_n|≤8(n+1)²(√3)^n`, with all arithmetic inputs discharged.

Verified source inputs:
[HyperellipticRiemannHypothesis.lean](../../../../formal/GaloisForLFunctions/RHTower/HyperellipticRiemannHypothesis.lean)
provides `norm_rootEnum_le`, `extHyp_eq_neg_sum_pow` and `card_points_eq`.
The [existing curve receiver model](../../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheReceiverOfACurveIsAdmittedAboveTheZeroWidth.lean)
provides coefficient estimates but explicitly assumes its root bounds and
makes no claim about actual curve points. Those model assumptions must be
discharged by the actual hyperelliptic inputs above.

## Boundary

This is a nonzero signed-count calibration at the square-root scale.
Constants and polynomial losses depend on the curve; no uniform-genus
estimate or integer-cutoff transfer follows. The governing integer target
remains `Σ_p index_p(N)=1−M(N)`.

The general ramified-orbit framework is classical:
[Gadish](https://arxiv.org/html/1703.01710v2).
Symmetric-power zeta identities are treated by
[Huang](https://arxiv.org/abs/1707.03479).
The displayed general hyperelliptic identity remains a proposed deduction;
the concrete elliptic comparison and bound above are formalized.
