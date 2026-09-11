# Hilbert causal inversion on the full right half-plane

Stage: 3-formalized.

For every existing `CauchyBoundedHilbertMap H`, its original `causalDatum` admits every positive exponential damping in Bochner L² on the positive time ray. Its Bochner Laplace transform is absolutely convergent at every Re(w)>0 and equals the given analytic vector there.

Let Q_s be the Hilbert Fourier inverse of the original frequency line s>0. Existing scalar Hardy coherence gives, for every continuous linear probe, exp(−st)Q_1(t)=exp(−t)Q_s(t). Both vector sides belong to L². Existing Bochner probe totality proves the vector identity without a separability premise. Cancelling exp(−t) identifies exp(−st)causalDatum(t) with Q_s(t) almost everywhere. Damping at half the requested positive real frequency and Cauchy–Schwarz prove absolute vector Laplace convergence. Scalar Hardy inversion then identifies the actual vector transform.

Module: [HilbertHalfPlaneFullCausal.lean](../../../../formal/GaloisForLFunctions/HTGeometry/HilbertHalfPlaneFullCausal.lean). New public API in `GaloisForLFunctions.HTGeometry.CauchyBoundedHilbertMap`: `causalDatum_memLp_pos`, `causalDatum_integrable_rightHalfPlane`, `causalDatum_laplace_rightHalfPlane`.

The exact proof passed combined scratch checking and its standalone exact leaf build with cached dependencies. The module is wired into `HTGeometry.lean`; no umbrella build or axiom-print check ran. The HB application constructs the required analytic-map data from its actual complete source and original inverse in [the physical causal Green-band theorem](hb-physical-causal-green-band.md).

Final formal lint passed with existing large-file warnings. Module imports and local report links were verified. All owned checks completed; temporary audit and scratch files were removed. No owned Lean process remains.
