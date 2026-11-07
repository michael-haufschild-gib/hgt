# Complex Euclidean weak-gradient Hilbert space

- **ID:** complex-euclidean-weak-gradient-graph
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Distributional gradient equations on complex `L²(ℝ³)` define a closed weak-gradient operator with dense domain and a complete Hilbert graph. Its mass embedding is injective with dense range.

Embed `L²` injectively into tempered distributions. The equations
`∂ⱼ u=gⱼ` define the kernel of a continuous linear map on
`L²×L²(ℂ³)`, hence a closed subspace. Zero mass gives zero gradient by
injectivity into distributions. Schwartz functions satisfy the equations
by integration by parts and are dense in `L²`, giving a dense mass range.
The Hilbert product norm restricts to
`‖u‖H¹²=‖u‖₂²+Σⱼ‖∂ⱼu‖₂²`.

Lean: `MetaplecticMobiusDescent/Sobolev/ComplexWeakGradientGraph.lean`,
`euclideanWeakGradient_closed`, `euclideanH1Embedding_injective`,
`euclideanH1Embedding_dense`, and `euclideanH1_norm_sq`.
Direct source and transitive axiom audits passed; only `propext`,
`Classical.choice`, and `Quot.sound`.

Adapted from OpenAI `MeanSquare/SourceTransfer.lean` using mathlib's
Schwartz density and tempered-distribution embedding. This graph is a
local analytic input to quotient energy localization.
