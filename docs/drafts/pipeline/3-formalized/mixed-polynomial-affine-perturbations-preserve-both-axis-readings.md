# Mixed polynomial affine perturbations preserve both axis readings

- **ID:** MIXED-AFFINE-POLYNOMIAL
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** For `g=(a,b)∈Aff(ℚ)`, the Hermitian kernel `K(g)=i(1−a⁻²)b²` has negative index exactly three. Adding it to Haar preserves both axis readings and has index three, but gives unbounded mixed coefficients.

## Mathematical purpose

This disproves a decomposition of every finite-index Haar-successor kernel as a positive affine kernel plus a slope kernel. On each fixed slope, such a decomposition is bounded in the translation coordinate; the displayed perturbation is quadratic and unbounded. It does not contradict the continuous-dilation conjecture: the unchanged Haar dilation reading is discontinuous.

## Dependency-closed paper proof

Inversion gives `K(g⁻¹)=−K(g)=conj(K(g))`. Both axis readings vanish: `K(1,b)=K(a,0)=0`.

For `g_j=(a_j,b_j)`, the Gram entry is `i(a_j⁻²−a_k⁻²)(b_k−b_j)²`. Set

`A=(a⁻²,a⁻²b²,−2a⁻²b)`, `B=(b²,1,b)`.

The entry equals `i Σ_r(conj(A_r(g_j))B_r(g_k)−conj(B_r(g_j))A_r(g_k))`. Adding the three feature squares of `A−iB` leaves the six positive squares of `A` and `B`. Hence `κ(K)≤3`.

Use translations `b=0,1,2` on slopes `a=1,2`. Their Gram matrix is `H=[[0,3iD/4],[−3iD/4,0]]`, where `D=[[0,1,4],[1,0,1],[4,1,0]]`. The inverse of `D` is `R=(1/8)[[−1,4,1],[4,−16,4],[1,4,−1]]`. The coefficient map `c↦(Rc,ic)` satisfies `M*HM=−(3/2)I`, giving three negative directions. Thus `κ(K)=3`.

Conjugating the six affine points by dilation `N+1` multiplies the polynomial Gram matrix by `(N+1)²`. Haar coefficients have norm at most one. Dividing the combined Gram matrix by `(N+1)²` therefore gives a sequence converging to `H`. Index semicontinuity preserves its three negative directions. Haar positivity supplies the reverse bound, so `κ(haarState+K)=3`.

Haar is real-valued. At slope two the combined state's imaginary part is `3b²/4`, so its norm is unbounded as integer `b` grows. A positive affine kernel `p` satisfies `|p(g)|≤p(1)`, while a slope kernel is constant on this family. Their sum cannot equal the constructed state.

## Scope and positive content

The two axis readings do not determine finite negative index: Haar has index zero and the constructed state has index three. The explicit completion and negative subspace identify the mixed polynomial contribution exactly. This is the positive structural content of the failure of positive-plus-slope decomposition. No claim about the prescribed Weil reading is made.

## Lean verification

`AdelicKreinGeometry/Haar/MixedPolynomialPerturbation.lean` proves:

- `isHermKernel_mixedQuadraticKernel` and `negIndex_mixedQuadraticKernel`;
- `haarMixedQuadraticState_hasIntegerSuccessor` and `haarMixedQuadraticState_dilation`;
- `negIndex_haarMixedQuadraticState`;
- `haarMixedQuadraticState_unbounded_on_fixed_slope` and `haarMixedQuadraticState_not_positive_add_slope`.

Direct leaf check passed. Transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
