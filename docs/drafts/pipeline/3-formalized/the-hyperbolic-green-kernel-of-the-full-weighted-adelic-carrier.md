# The hyperbolic Green kernel of the full weighted adelic carrier

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; actual weighted finite-place Green theory and the hyperbolic radial Green equation.
- **Statement:** The standard-branch operator-valued radial Green kernel for
  `(Δ_ℍ³−3/4)+(λ−Σ_p p⁻²A_p)` on `ℍ³×V`, with its unit Newtonian source
  and canonical nonlocal Robin operator is constructed unconditionally. Here `V` is the actual restricted
  adelic vertex carrier and `λ=Σ_p 2p⁻²√p`.

## Kernel

Let `A=Σ_p p⁻²A_p` on counting `ℓ²(V)`, and put
`B=(λ+1/4)I−A`. The operator-valued radial kernel is

`K(r)=exp(−r√B)/(4π sinh r)`.

Its radial equation is
`K″+2 coth(r)K′=(B−I)K`, its Newtonian coefficient is `I`,
and its finite part at `r=0` is `−√B/(4π)`.
Thus coupling finite places to the hyperbolic fibre produces a
square-root Robin operator, rather than an independently chosen diagonal.

## Analytic construction

The actual bounded self-adjoint adjacency on `ℓ²(V)` satisfies
`‖A‖≤λ`, despite divergent constant-function rows. For a positive
restricted product `h`, the corpus proves `Ah≤λh`; symmetry supplies
the matching column control. Weighted Schur estimates on finite
sections give the operator without a countability premise.
Then `B≥(1/4)I`. A contraction constructs its positive square root while
preserving the entrywise positivity needed for the Green kernel.

### Hilbert-space construction

For finite input and output sets `S,T`, weighted Cauchy–Schwarz gives
`|Σ_{z∈S} K(y,z)f(z)|² ≤ λh(y) Σ_{z∈S} K(y,z)f(z)²/h(z)`.
Sum over `T`, interchange the finite sums, and apply the symmetric row
bound to obtain `Σ_{y∈T}|A(1_S f)(y)|² ≤ λ²Σ_{z∈S}f(z)²`.
Thus each matrix column lies in counting `ℓ²(V)`, finite-column synthesis
extends with norm at most `λ`, and symmetry passes through the dense
finite charges. Nonnegative matrix entries preserve nonnegative charges.

The extension retains the original prime sum: a local neighbour set has
`p+1` distinct vertices, so its Cauchy–Schwarz bound gives
`|p⁻² A_p f(y)| ≤ 2p⁻³ᐟ²‖f‖₂`. These bounds are summable over primes.
The sum of the local evaluation functionals therefore converges in operator
norm and agrees with the extension on the dense finite charges, hence
everywhere. This removes a possible domain substitution in the coupling.

Lean verified in `TheWeightedAdelicAdjacencyOnSquareSummableCharges.lean`:
`finite_adjacency_square_bound`, `adjacencyOperator_norm_le`,
`adjacencyOperator_nonneg`, `adjacencyOperator_symmetric`,
`chargeSpace_inDomain`, `adjacencyOperator_apply`.
Plain check passes; all six axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`.

### Positive square root by contraction

Put `a=√(λ+1/4)`, `b=a−1/2`. On the closed operator-norm ball of
radius `b`, the map `F(R)=(A+R²)/(2a)` preserves the ball because
`λ+b²=2ab`, and contracts with constant `b/a<1` because
`R²−Q²=R(R−Q)+(R−Q)Q`. Starting at zero, its iterates are self-adjoint
and preserve nonnegative charges. Their norm limit has the same properties.
The fixed-point identity gives `S=aI−R`, `S²=(λ+1/4)I−A`, and
`⟨Sf,f⟩≥(1/2)‖f‖²`.

For `r≥0`, `exp(−rS)=exp(−ar) exp(rR)`. The exponential series preserves
nonnegative charges and has norm at most `exp(−ar+r‖R‖)≤exp(−r/2)`.
This proves the intended positivity and decay without confusing positive
quadratic forms with nonnegative matrix entries. The square-root construction
is Lean verified in `ThePositiveSquareRootOfTheAdelicPrecision.lean`:
`rootRemainder_norm_le`, `tendsto_rootStep_iterate`,
`rootRemainder_nonneg`, `rootRemainder_symmetric`,
`hyperbolicRoot_coercive`, `hyperbolicRoot_squared`.
Plain check passes; all six axiom audits contain only standard Lean axioms.
The exponential and Green-kernel consequences are Lean verified in
`TheHyperbolicGreenKernelOfTheWeightedAdelicCarrier.lean`:
`hyperbolicEvolution_nonneg`, `mixedGreen_norm_le`,
`mixedGreenEntry_symm`, `mixedGreenEntry_nonneg`, `mixedGreen_radial`,
`tendsto_mixedGreen_source`, `tendsto_mixedGreen_flux`,
`tendsto_mixedGreen_robin`, `tendsto_mixedGreenEntry_collision`.
The plain check passes; all ten printed axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`.

### Archimedean collisions

The Newtonian coefficient is the identity matrix on the adelic vertices.
Hence for distinct vertices `x≠y`, the limit at archimedean distance zero
is finite: `−S(x,y)/(4π)=R(x,y)/(4π)≥0`. This value must define the kernel
at such collisions; substituting `r=0` into Lean's totalized quotient would
give the wrong value. Only equal adelic vertices retain the Newtonian pole.
The full diagonal finite part is `−S(x,x)/(4π)`.

### Finite Dirichlet sections

Let `P_F` restrict charges to a finite set `F⊂V`, and `A_F=P_FAP_F`.
The same ball and contraction constant `q=b/a<1` construct `R_F` from
`T↦(A_F+T²)/(2a)`. Its iterates are supported in `F×F`, as is their
norm limit. Hence `S_F=aI−R_F` satisfies `S_F²=a²I−A_F`; on `F` this
is the actual finite Dirichlet precision. Compression `P_FSP_F` does
not supply this square-root identity.

The coordinate projections converge strongly to the identity by the
unconditional sum of the coordinate charges. Uniform operator bounds
then give strong convergence of every fixed contraction iterate.
The uniform error `‖R_F−R_{F,n}‖≤bqⁿ`, and its infinite-carrier counterpart,
pass this convergence to the fixed points. Polynomial convergence and
the summable exponential majorant pass it to `exp(−rS_F)` for each `r`.
Thus the finite Dirichlet Green entries and their Robin finite parts
converge to the stated full-carrier entries, independently of exhaustion.
This passage is Lean verified in
`TheFiniteDirichletSectionsRecoverTheHyperbolicGreenKernel.lean`:
`tendsto_sectionRemainder`, `sectionRemainder_supported`,
`sectionHyperbolicRoot_squared`, `sectionHyperbolicRoot_coercive`,
`tendsto_dirichletEvolution`, `tendsto_dirichletMixedGreen_robin`,
`tendsto_dirichletRegularizedEntry`. The plain check passes without warnings;
all seven printed axiom audits contain only standard Lean axioms.

The kernel retains the actual prime sum, the radial differential equation,
unit source coefficient and flux, Robin limit, symmetry, and spatial decay.
Entrywise positivity is proved through the exponential series. Finite-section
convergence includes the Robin values at zero archimedean distance.

## Boundary

This is the specified weighted operator on the full mixed carrier.
The verified Green statement is the radial operator equation with its
Newtonian normalization and flux; no Bochner-integral inverse on the full
hyperbolic function space is asserted.
It does not identify Weil's form: the accepted invariant-gluing
obstruction remains in force. The archimedean standard branch and
Weil's alternative branch must remain distinguished.
