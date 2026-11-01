# Actual Mayer operator: Fredholm determinant and spectral equivalence

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).
- **Input:** [order-zero nuclear expansion](gauss-mayer-renormalized-nuclear-expansion.md).

For the actual regularized Gauss–Mayer operator `L(w)` on the Banach algebra
`A({|z−1|≤3/2})`, fix `Re w>0`, `w≠1`. There is an entire function of the
spectral variable `λ`, constructed from its actual Cauchy coefficients, with

`D(w,0)=1`,

`D(w,λ)=0 ↔ I−λL(w) is not invertible`.

For `λ≠0`, this is equivalent to existence of a nonzero disc-algebra
function `f` satisfying `L(w)f=λ⁻¹f`. No spectral occurrence is assumed.

## Explicit realization and approximation

Set `r=9/8`, `s=6/5`, `R=32/25`, `η=15/16`, and `C=C(w,r)` from the
nuclear-expansion theorem. For the actual Cauchy coefficients `αⱼ,R` and
monomials `eⱼ(z)=(z−1)^j`, put

`φⱼ=s^j αⱼ,R`, `yⱼ=s^(−j)L(w)eⱼ`.

The bounded maps

`Q:A(D)→ℓ²`, `Qf=(φⱼ(f))ⱼ`,

`J:ℓ²→A(D)`, `Jx=Σⱼxⱼyⱼ`

satisfy `JQ=L(w)`. The Hilbert realization `M=QJ` is nuclear and has matrix

`Mᵢⱼ=φᵢ(yⱼ)=s^(i−j)αᵢ,R(L(w)eⱼ)`,

with `|Mᵢⱼ|≤Cη^iη^j`. Let `M_N` be its first `N×N` block. Then

`D(w,λ)=lim_N det(I−λM_N)`

and, with `S₁=(1−η)⁻¹`,

`|det(I−λM_N)−D(w,λ)| ≤ |λ| C S₁ exp(|λ| C S₁²) η^N/(1−η)`.

The corresponding finite rank-one operator is exactly the previously
certified Taylor approximation: `Σⱼ<N φⱼ⊗yⱼ=Σⱼ<N αⱼ,R⊗L(w)eⱼ`.

## Proof

Cauchy estimates and the local operator estimate give
`‖φⱼ‖≤η^j`, `‖yⱼ‖≤Cη^j`. Both families are norm-summable. Express `Q` as
`Σⱼ φⱼ⊗δⱼ` and `J` as `Σⱼ evⱼ⊗yⱼ`, using the unit coordinate vectors
and norm-at-most-one coordinate evaluations on `ℓ²`. These series converge
in operator norm. Coordinate evaluation gives the displayed formulas, and
the certified Cauchy expansion gives `JQ=L(w)`. The synthesis map is nuclear;
bounded composition makes `M=QJ` nuclear. Its entries obey the stated
geometric bound, hence are square-summable.

The corpus's geometric matrix determinant construction gives the entire
finite-block limit and explicit error. To connect it to the global spectral
determinant, let `K(i,j)=Mᵢⱼ` and `t=ΣⱼMⱼⱼ`, an absolutely convergent sum.
The finite identity

`det(I−λM_N)=det₂(I−λM_N) exp(−λ tr M_N)`

passes to the limit. Finite regularized determinants converge to the global
Hilbert–Carleman determinant, and `tr M_N→t`, so

`D(w,λ)=entireDet₂(K,λ) exp(−λt)`.

The coefficient kernel reconstructs precisely `QJ`, as both operators agree
on every coordinate vector. The exponential factor never vanishes. The
existing global determinant theorem therefore gives
`D(w,λ)=0 ↔ QJ` has eigenvalue `λ⁻¹` for `λ≠0`.

For every `μ≠0`, a nonzero eigenvector `x` of `QJ` maps under `J` to a
nonzero eigenvector of `JQ`: if `Jx=0`, then `μx=QJx=0`. Conversely `Q`
transfers nonzero eigenvectors of `JQ` to `QJ`. This proves the exact
source eigenvector criterion. Compactness of `L(w)` and the Banach Fredholm
alternative identify that criterion with failure of invertibility of
`I−λL(w)`. At `λ=0`, both sides are settled by `D(w,0)=1`.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerFredholmDeterminant.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm`.

- `synthesis_comp_analysis`, `matrixOf_hilbertOperator`, `toOperator_kernel`:
  actual source factorization and coordinate realization.
- `nuclear_hilbertOperator`, `geomDecay_matrix`: nuclearity and entry bounds.
- `finite_factor_eq_approximation`: actual finite Taylor operators.
- `determinant_eq_entireDet2`, `differentiable_determinant`, `determinant_zero`.
- `determinant_eq_zero_iff_eigenvector`, `determinant_eq_zero_iff_not_isUnit`.
- `determinant_approximation_error`: explicit finite determinant error.

Final direct `lake --old env lean` check passed. All nine public theorem
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import is wired; no umbrella build was run.

## Scope

This closes the actual-operator/global-determinant bridge using a fixed
Cauchy realization. Geometric matrix determinants and the Hilbert spectral
theorem are reused. No literature-novelty claim is made.

The Selberg/scattering identity, dependence on the parameter `w`, and
source-specific exclusion of off-critical resonances remain separate
obligations. The totalized value at `w=1` is not a removal of the analytic
pole. No RH conclusion follows from the determinant's existence.
