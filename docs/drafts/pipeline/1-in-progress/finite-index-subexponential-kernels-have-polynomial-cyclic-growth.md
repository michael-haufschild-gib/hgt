# Polynomial cyclic growth from finite negative index

- **Stage:** 1-in-progress.
- **Type:** CONJECTURE; not counted.
- **Source:** B9 in `docs/reports/review-3110/route-obstacles.md`.
- **Target:** Every Hermitian kernel on any group, with negative index at most
  `r` and subexponential growth on each cyclic subgroup, has cyclic growth
  `O((n+1)^(2r))`.

## Completed foundation

A normalized negative column frame has length at most `r`. Choose one of
largest length `m`. A negative vector orthogonal to it would extend the
frame, so its orthogonal complement is nonnegative. Cauchy–Schwarz and
column nondegeneracy make that complement definite. Projection
`v ↦ v + Σ B(eᵢ,v)eᵢ` splits the column form into `H₀ × ℂ^m`, `m≤r`.

Every algebraic form-isometry `T` on this product is bounded. Its inverse
restricted to the negative factor, `U(x)=T⁻¹(0,x)`, is automatically
continuous. For `b=(Tv).2`, the identity `B(Ub,v)=-⟨b,b⟩` gives
`‖b‖≤2‖U‖‖v‖`. Preservation of the square bounds the positive coordinate.
Thus translations extend to a dense, injective column realization in
`Completion H₀ × ℂ^m`, preserving the form and group law.

Formalized in HKT `Index/NegativeColumnFrames`, `FiniteNegativeDirections`,
`NegativeFrameHilbertSpace`, `CompletingFiniteNegativeIsometries`, and
`CompletedFrameRepresentation`. Capstone axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`; umbrellas are wired.

HTGeometry `WeakContractionBall` proves weak compactness and convexity of
contractive finite-column operators, and joint continuity of evaluation
for weak columns and a finite-dimensional input. HKT
`Index/ContractionGraphImages` proves that an isometry maps every such graph
onto another contraction graph: its negative projection is injective,
hence invertible. Both modules pass Lean and axiom audits.

## Remaining bridge

Restrict the kernel to `Multiplicative ℤ` and let `T` translate by one.
The transformed-graph equation
`T(Ax,x)=(B D(A)x,D(A)x)` is closed in the product of contraction balls.
HTGeometry `continuous_of_isClosed_graph`, from
`ConstitutiveInvariantPositivityKMSWall`, turns this into a continuous
action. The weak Hilbert fixed-point theorem gives an invariant maximal
nonpositive graph. `Index/InvariantNegativeGraph.lean` passes its direct
Lean check and axiom audit.

`Index/NonpositiveFiniteIndexEigenvector.lean` formally extracts a nonzero
nonpositive eigenvector when `m>0`; its axiom audit is clean. Each negative
coordinate of the completed cyclic orbit is a finite sum of translates
of the original kernel; preservation of the square then bounds its full
norm subexponentially in both time directions. Density and nondegeneracy supply a column `eₐ` with `B(w,eₐ)≠0`;
translating its integer orbit preserves the subexponential bound.
Writing `f(z)=B(w,T^z eₐ)`, invariance gives
`conjugate(λ) f(z+1)=f(z)`. Hence
`f(-n)=conjugate(λ)^n f(0)` and
`f(n)=(conjugate(λ)⁻¹)^n f(0)`.
HKT `coeff_eq_zero_of_norm_le`, with one node and any growth rate strictly
between `1` and that node's modulus, excludes modulus greater than one in
both formulas. Thus `|λ|=1`.

Now `(T-λ)v` is orthogonal to `w`. Every strictly negative finite-dimensional
subspace `V` of this orthogonal space satisfies `dim V+1≤m`: adjoining `w`
gives an injective nonpositive family `V × ℂ → H × ℂ^m`, whose negative
projection is injective. To check independence, pair a vanishing linear
combination with its `V` component; strict negativity kills that component,
then `w≠0` kills its scalar coefficient. This includes null `w`.
`Index/FiniteNegativeIndexDrop` and `Index/FiniteNegativeCoefficients`
formalize this dimension loss and its transfer to orbit-kernel negative
index; both pass Lean and standard-axiom audits.

Consequently the filtered coefficient
`q(n)=2k(n)-λk(n-1)-conjugate(λ)k(n+1)` has index at most `r-1`.
Fixed translates preserve subexponential growth. Induction bounds `q` by
degree `2(r-1)`. Since `q(n)=-conjugate(λ) Δλ² k(n-1)`, two unit-modulus
discrete integrations give degree `2r`. Index zero is the bounded
positive-definite case. No invariant-subspace, spectral, or orbit-growth
premise may remain in the kernel theorem.

## Novelty audit

Corpus searches found the index-one quadratic boundary, finite column
repairs, and forward special spectral formulas, but no general finite-index
polynomial growth or unitary-filter index-drop theorem. Records:
`/tmp/hgt-finite-index-growth-novelty.json`,
`/tmp/hgt-nonpositive-orthogonal-index-drop-corpus.json`,
`/tmp/hgt-unitary-filter-index-drop-corpus.json`.
Further audit is required before acceptance.
