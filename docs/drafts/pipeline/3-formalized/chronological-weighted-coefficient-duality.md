# Every homogeneous recovery is controlled by a weighted Chebyshev polynomial

**Status:** fully formalized and axiom-audited. Positive optimal gaps, attainment, the sharp missing-coefficient bound and the graded quotient norm were already formal; the general weighted Chebyshev optimizer, simultaneous coefficient duality, the equality case, uniqueness of the normalized optimizer, and the root-sum formula for the graded gap are now Lean theorems too. They rest on a new general weighted-minimax theory built for this card, `formal/GaloisForLFunctions/HTGeometry/WeightedMinimax/` (six leaves), since neither mathlib nor the corpus contained any equioscillation, alternation or weighted-Chebyshev result. 95 new declarations, every one audited to depend only on `propext`, `Classical.choice` and `Quot.sound`; umbrella wired; authoritative lint passed. Higher-weight explicit constants and asymptotics remain open research and are not part of this card. No novelty claim for these approximation principles.

## Exact statement

For k≥1 set I=[0,1/4], W(r)=1−√(1−4r), and

`N_k(R)=max_(r∈I) W(r)^k |R(r)|`, `deg R≤k`.

Let T_k be the monic degree-k polynomial minimizing N_k, and put t_k=N_k(T_k). For every j=0,…,k,

`|coeff_j R| ≤ (|coeff_j T_k|/t_k) N_k(R)`.

Every coefficient of T_k is nonzero. Equality for a nonzero R forces R to be a scalar multiple of T_k. Consequently the unique minimizer with coeff_j R=1 is T_k/coeff_j T_k.

For chronological recovery of the missing class u^(k−1)c, j=k−1. If ρ₁,…,ρ_k are the roots of T_k, then

`δ_k = t_k/(ρ₁+⋯+ρ_k) > 0`.

The unique optimal residual is T_k/coeff_(k−1)T_k under the proved homogeneous coordinate correspondence. These are approximation-polynomial roots; no identification with zeta zeros is asserted.

## Proof

W is continuous, zero at 0, and positive on (0,1/4]. Thus N_k is a norm on the finite-dimensional space of degree-at-most-k polynomials. A monic minimizer exists and has positive norm. The weighted alternation theorem supplies k+1 points

`0<x₀<⋯<x_k≤1/4`, `W(x_i)^k T_k(x_i)=(-1)^(k−i)t_k`.

The endpoint 0 cannot be extremal because its weighted value is zero. The k sign changes give k distinct roots strictly between these points, hence in (0,1/4).

Use the Lagrange polynomials

`ℓ_i(r)=∏_(h≠i)(r−x_h)/∏_(h≠i)(x_i−x_h)`.

For every coefficient index j, the numerator coefficient has sign (-1)^(k−j) and positive magnitude: it is an elementary symmetric sum of strictly positive nodes. The denominator has sign (-1)^(k−i). Therefore coeff_j ℓ_i has sign (-1)^(i−j) and is nonzero.

Interpolation gives coeff_j R=Σ_i coeff_j(ℓ_i)R(x_i). Hence

`|coeff_j R| ≤ N_k(R) Σ_i |coeff_j ℓ_i|/W(x_i)^k`.

For T_k, all terms in that coefficient sum have the same sign (-1)^(k−j), so equality holds. Dividing the equality for T_k by t_k yields the stated coefficient bound. Equality for another nonzero R requires every node value to saturate its norm bound with the same prescribed alternating signs. Its values are therefore a common scalar multiple of those of T_k. Interpolation forces the same polynomial identity. The coefficient constraint fixes that scalar, proving uniqueness. Finally monicity and the positive roots give coeff_(k−1)T_k=−Σ_iρ_i.

## Direct compactness proof of a positive attained gap

There is a shorter dependency route for existence and positivity, before alternation. Give the finite-dimensional homogeneous space H_k its proved physical norm. The residuals with missing coefficient one form a nonempty closed affine hyperplane F: its coefficient map is linear, hence continuous in finite dimension. Intersect F with the closed ball whose radius is the norm of the missing monomial. This is nonempty and compact, so the norm attains a minimum there. Every residual outside that ball has at least as large a norm. The minimizer cannot be zero because its fixed coefficient is one. Its norm is therefore strictly positive. This proves existence and positivity without yet identifying or proving uniqueness of the minimizer.

## The graded quotient norm exposed by the positive gap

Let λ_k be the coefficient of u^(k−1)c on H_k and S_k=ker λ_k=A∩H_k. This coefficient is onto, so H_k/S_k is canonically a real line. If δ_k is the attained positive recovery gap, homogeneity gives the sharp inequality

`δ_k |λ_k(P)| ≤ ‖P‖_physical`.

For nonzero λ_k(P), divide P by that coefficient and use the normalized-residual minimum; the zero case is immediate. Scaling a minimizing normalized residual attains this bound at every prescribed coefficient. Representatives of one quotient class have exactly the same coefficient. Their norm infimum, including its attainment, is therefore

`‖[P]‖_(H_k/S_k)=δ_k |λ_k(P)|`.

This is the standard quotient norm from the physical homogeneous norm. The full ungraded normalization quotient still has zero uniform separation; it must not be assigned this norm without constructing the graded topology. This calculation requires no optimizer uniqueness and is a direct positive survivor of the unrestricted-recovery obstruction.

## Dependencies, comparison, next work

The physical boundary and exact recovery reduction are in [homogeneous boundary](chronological-homogeneous-boundary.md). [Novello–Schiefermayr–Zinchenko, arXiv:2508.08449v1, §2, Theorem 2.2](https://arxiv.org/html/2508.08449v1) supplies weighted existence, uniqueness, and alternation, allowing a weight that vanishes at an endpoint. The coefficient bound above follows by the displayed classical Lagrange argument; it should not be advertised as a new general theorem.

CubicHomogeneousMetric, CubicGradedRecovery, CubicGradedCoefficient, and CubicGradedDefect formalize the direct compactness route and quotient-norm consequence: 36 declarations, all final-built and axiom-audited. The quotient is presented as equality of missing coefficients; Lean proves this relation is exactly difference by an available cusp observation. Its norm is defined as the infimum of physical representative norms, then proved to equal δ_k|λ_k| and to be attained. Lean indexes these positive weights by k−1.

## Formal route for the optimizer theorem

The classical alternation input is now built from scratch, in general form, under
`formal/GaloisForLFunctions/HTGeometry/WeightedMinimax/`. For a continuous weight `v ≥ 0` on
`Icc a b` whose positivity set is infinite (`IsWeight`), `wsup v a b R = sup_[a,b] v·|R|` is attained
and is a genuine norm on each `Polynomial.degreeLT ℝ (n+1)`; properness of that finite-dimensional
norm gives a minimizer with any single coefficient prescribed (`exists_coeffSet_minimizer`).

`exists_alternating_extreme_chain` is the alternation theorem: the monic degree-`n` minimizer has
`n+1` extreme nodes at which it alternates in sign. Its proof replaces the classical greedy
block construction by three shorter steps. First, `exists_wsup_lt_of_sign_match`: if some `g` of
degree `< n` has the sign of `T` at every extreme point then `T − εg` is strictly better, so a
minimizer admits no such `g`. Second, strict separation (`geometric_hahn_banach_point_closed`)
turns that into `0 ∈ closure (convexHull (signed weighted moment vectors of the extreme points))`,
and the corpus's `exists_atomic_of_mem_closure_convexHull` in
`HTGeometry/FiniteAtomicCubature.lean` — Carathéodory in coordinates — upgrades the closure point
to a genuine finite convex combination. Third, `exists_sign_realizing` realizes any finite sign
pattern by a polynomial whose degree is the number of sign changes, so a vanishing combination
forces at least `n` alternations.

`roots_finset_of_alternating` then extracts `n` distinct roots, one strictly inside each gap, all
in `(0,1/4)` once the weight vanishes at the left endpoint. `prod_X_sub_C_coeff_sign` proves that
every coefficient of a monic product of linear factors with positive roots is nonzero with
alternating sign, which is exactly the Haar property of `{deg ≤ n, coeff j = 0}` on the positive
half-line (`coeff_ne_zero_of_positive_roots`). De la Vallée Poussin comparison at the `n+1` nodes
gives `coeff_mul_wsup_le`, the sharp bound `|coeff_j R|·‖T‖ ≤ |coeff_j T|·‖R‖`. Uniqueness comes
from `exists_extremeSet_card`: a minimizer with `coeff j = 1` has at least `n` extreme points,
because otherwise `exists_sign_realizing_coeffKer` — the unconstrained realizer corrected by a
multiple of the polynomial vanishing at all the nodes — supplies an improving perturbation inside
the hyperplane `coeff j = 0`. Averaging two minimizers and applying the Haar property gives
`coeffSet_minimizer_unique`, hence `coeffSet_minimizer_eq`: the unique minimizer with
`coeff j = 1` is `T / coeff_j T`, with value `‖T‖ / |coeff_j T|`. `eq_const_mul_of_coeff_eq` is the
equality case, and `coeff_pred_eq_neg_sum_roots` identifies `coeff_{n−1} T = −Σρ_i`.

`ChronologicalTensor/CubicChebyshevOptimizer.lean` discharges every weight hypothesis for
`W(r) = 1 − √(1−4r)` on `[0,1/4]`: `cubicIntervalWeight_isWeight` and, at positive exponent,
`cubicIntervalWeight_pos` (the weight vanishes exactly at the left endpoint). The capstone
`cubicGradedRecoveryGap_eq_rootSum` states the card's conclusion for the already formalized gap:
there is an optimizer `T` of degree `k+1` with `k+1` distinct roots in `(0,1/4)` and
`T = ∏(X − ρ_i)`, such that `cubicGradedRecoveryGap k = ‖T‖ / Σρ_i`, and every normalized residual
attaining the gap equals `T / coeff_k T`.

The [graded Hilbert completion](chronological-graded-hilbert-defect.md) is also formalized. Higher-weight
explicit constants and asymptotics remain open research.
