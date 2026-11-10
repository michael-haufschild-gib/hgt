# The global adelic Green kernel is a positive covariance

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; the weighted global Green source and actual finite-configuration energy.
- **Statement:** The constructed minimal Green kernel for `Σ_p p⁻²A_p` is symmetric and strictly positive definite on every finite set of distinct actual adelic vertices. Finite Dirichlet inverses increase to that same kernel.

## Proof [PROVED HERE]

On a finite configuration `F`, the actual precision matrix is
`M_F=λI−K_F`, where `K` is the summable weighted adjacency kernel.
The proved energy gap makes `M_F` positive definite, hence invertible.
For real charges `u`, put `v=min(u,0)` coordinatewise. Nonnegative
adjacency and `v≤u`, `v≤0` give
`Q_F(v)≤Σ_F v M_Fu`. If `M_Fu≥0`, the right side is nonpositive.
Strict positivity of `Q_F` forces `v=0`, so `u≥0`. Applying this to
the inverse columns proves their nonnegativity and, by subtraction,
comparison for all real charges.

Extend each inverse column by zero outside `F`, including when its
source lies outside `F`. Write this kernel as `G_F(x,y)`. Its compressed
source is `δ_x` on `F`. The existing barrier `B_x` satisfies
`M_FB_x≥(λ−A)B_x≥δ_x`, because its omitted values are nonnegative.
Comparison gives `0≤G_F≤B_x`. If `F⊆E`, then
`M_FG_E=δ_x+Σ_{E\F}K G_E≥δ_x` on `F`; comparison gives `G_F≤G_E`.
The same argument bounds every `G_F` by the existing global `G`.

For fixed `x,y`, the directed net `G_F(x,y)` therefore converges to
`V(x,y)=sup_F G_F(x,y)≤B_x(y)`. The proved barrier domain makes
`V(x,·)` and every `G_F(x,·)` belong to the actual adjacency domain.
For each prime, the neighbour sum is finite and passes to the limit.
The summable prime majorant `p↦p⁻²A_pB_x(y)` then passes the limit
through the whole adjacency series. Eventually `y∈F`, so the finite
source equations give `(λ−A)V_x=δ_x`. Global minimality gives `G≤V`;
the previous comparison gives `V≤G`, proving `G=V`.

Every finite inverse is symmetric, hence so is its extension and its
limit. On any fixed finite charge set `S`, eventually `S⊆F`; positive
definiteness of `M_F⁻¹` makes its quadratic form on those charges
nonnegative. Finite sums commute with the pointwise limit, proving
positive semidefiniteness of the full `G`.

For strictness, let `q=Σ_{x,z∈S}f(x)G(x,z)f(z)=0`, and put
`u(y)=Σ_{x∈S}f(x)G(x,y)`. Positivity applied on `S∪{y}` to
`f+tδ_y` gives `0≤2t u(y)+t²G(y,y)` for every real `t`.
Since the already proved diagonal satisfies `G(y,y)>0`, choosing
`t=−u(y)/G(y,y)` forces `u(y)=0`. Finite linear combinations of the
proved convergent Green source equations give `(λ−A)u=1_Sf`.
Thus `f=0` on `S`, proving strict positivity for every nonzero finite
charge. This avoids an unjustified strict-positivity limit argument.

## Lean

Namespace: `GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen`.

- `TheDirichletGreenKernelsOfTheAdelicCarrier.lean`:
  `precisionMatrix_posDef`, `precision_maximum`, `dirichletGreen_source`,
  `dirichletGreen_symm`, `dirichletGreen_nonneg`, `dirichletGreen_le_barrier`,
  `dirichletGreen_mono`, `dirichletGreen_quadratic_nonneg`.
- `TheGlobalAdelicGreenKernelIsAPositiveCovariance.lean`:
  `green_eq_iSup_dirichlet`, `tendsto_dirichletGreen`, `green_symm`,
  `greenEnergy_nonneg`, `greenPotential_inDomain`, `greenPotential_source`,
  `greenEnergy_pos_iff`.

Both modules pass plain `lake --old env lean` checks without warnings.
All twelve printed dependency audits contain only
`[propext, Classical.choice, Quot.sound]`. Both modules are imported by
the programme umbrella.

## Boundary

This concerns the specified weighted finite-place operator. It does not
identify Weil's form or evade the accepted invariant-gluing obstruction.
