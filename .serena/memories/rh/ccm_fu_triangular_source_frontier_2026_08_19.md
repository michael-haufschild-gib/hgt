# CCM-FU triangular source frontier (2026-08-19)

Formalized in `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilThirdGradeCesaroAnchoredMoment.lean`:

- `ccmGuinandWeilThirdGradeCesaroTriangularWeight H h = (32 / h^3) * (1 - h/H)`.
- `hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight`: derivative is exactly `-ccmGuinandWeilThirdGradeCesaroErrorKernel H h` away from zero.
- `ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_primePolarTriangularWindow`: for `0 < b <= H`, anchored signed moment equals literal `ccmGuinandWeilPrimePolarWeightedWindow b H` tested against moving triangular weight. Prime and polar channels stay coupled before completed-error scalarization.

Verification:
- scratch `lake env lean /tmp/ccm_triangular_scratch.lean` passed;
- targeted source check passed;
- exact module build passed;
- `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`.
- global lint still fails only on pre-existing/unrelated umbrella reachability errors.

Scientific frontier: requested uniform bound is not proved. It implies RH through existing anchored-moment receiver. Exact remaining theorem is uniform control of the literal moving triangular prime-polar window. Generic FU inversion, Xi-Hurwitz orientation packets, cubic-prime ell2/Hilbert evaluation, and outgoing quantile transport were hostily audited and rejected: respectively non-generative, target-extracted, loses zero-clock half-density, and simply re-encodes the same signed discrepancy. Any successful producer must act on the joint finite prime-polar source at the moving triangular test and annihilate off-critical exponential modes; separate absolute estimates cannot work.