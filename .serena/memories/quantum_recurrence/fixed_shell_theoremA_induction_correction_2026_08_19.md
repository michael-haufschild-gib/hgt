# Fixed-shell Theorem A: the induction step is an intersection, not a propagation

Correction to the plan in `goal/five-card-stage3-plan-2026-08-19`, item (a).

The uncoupled layer-split spectrum is `E_α ± z/2`, so the old gap `E_β − E_α` occurs **twice**,
once inside each layer.  Distinct nonzero ordered gaps therefore **never** hold for the uncoupled
extension, for any split field `z`.  Do not try to propagate `hgap` through the uncoupled split.

The coupling breaks the degeneracy.  The correct induction step:

1. the leaf-extended architecture has a dense, residual, full-measure maximally projective set —
   `PhysicallyRealizedTensorTreeSystem.tracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`
   (`HTGeometry/TracelessLocalHamiltonianGenericityLaw.lean`);
2. maximal projective rank gives simplicity and distinct nonzero ordered gaps —
   `MaximallyProjectiveEnergy.injective`, `maximallyProjectiveEnergy_orientedGap_injective`;
3. endpoint completeness holds at some small nonzero coupling —
   `eventually_forall_layerGerm_endpoint_ne_zero`
   (`HTGeometry/LayerGermEndpointCompleteness.lean`) — and is an **open** condition —
   `eventually_forall_layerReducedTransition_ne_zero`;
4. a nonempty open set meets a dense set, so the extended witness exists.

Remaining work for that step is only to state 1–3 in the same parameter space, not a new
genericity argument.

Base case is already closed: `HTGeometry/BellEndpointCompleteBasis.lean`,
`exists_endpointComplete_twoQubit_witness` — a maximally entangled orthonormal basis is endpoint
complete because `reducedTransition ψ φ = reshape φ * (reshape ψ)ᴴ` and every Bell reshape is
`2^{-1/2}` times a unitary.
