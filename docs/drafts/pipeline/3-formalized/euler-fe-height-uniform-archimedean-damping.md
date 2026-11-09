# Height-uniform archimedean Gaussian renormalization

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport theory: joint height and damping control.

## Theorems

For `A(s)=1/s+Γℝ′/Γℝ(s)` and its actual Gaussian Mellin–Barnes transform
`A_y(s)` on any positive contour abscissa,

`|A_y(s)−e^(−y)A(s)| ≤ y e^(−y)/Re(s)`, for `y>0`, `Re(s)>0`.

This removes all height dependence from the damping error. It gives uniform
convergence of the renormalized archimedean current on every whole half-plane
`Re(s)≥σ₀>0`, allowing height to escape arbitrarily while damping tends to zero.
The existing estimate for `A_y−A` contains `y|s−2|` and gives no such control.

At fixed `y,σ>0`, `sup_t |A_y(σ+it)−zA(σ+it)|<∞` holds exactly
when `z=e^(−y)`.

## Proof

Use the proved absolutely convergent trivial-zero expansions. One incomplete
Mellin recursion, with `E(y,a)=∫₁∞e^(−yu²)u^(a−1)du`, gives

`A_y(s)−e^(−y)A(s)=Σ_{n≥0} 2y E(y,−s−2n)/(s+2n+2)`.

For `Re a<0`, direct integration gives `|E(y,a)|≤e^(−y)/(−Re a)`.
For `σ=Re(s)>0`, the summands therefore have norms at most
`2ye^(−y)/[(σ+2n)(σ+2n+2)]`. Its first `N` terms sum to
`ye^(−y)[1/σ−1/(σ+2N)]`. Passing through the existing convergent expansion
gives the stated bound; `e^(−y)≤1` gives uniform convergence on `Re s≥σ₀>0`.

For uniqueness, the same uniform error leaves
`(e^(−y)−z)A(s)` for any other scalar `z`. A proved vertical logarithmic lower
bound gives
`Re A(σ+it)≥log(t/2)/2−3/t−log π/2` for `t≥4`. Thus `|A(σ+it)|` is
unbounded, and the triangle inequality forces `z=e^(−y)`.

## Scope

This is the archimedean part of the actual Gaussian explicit formula. It does
not supply the still-needed uniform bound for the complete nontrivial-zero
field, prime-return times, or height replication. Formalization:
`EulerFETransportTheory/TheArchimedeanDampingErrorIsUniform.lean`.

## Lean declarations and audit

- `hasSum_archimedeanDampingError`: the full convergent correction series.
- `norm_archimedeanDampingError_le`: the uniform bound.
- `tendstoUniformlyOn_archimedeanDampingError`: convergence on whole half-planes.
- `archimedeanDampingError_bounded_iff`: unique scalar normalization.

Direct `lake --old env lean` checking passes. All four transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
