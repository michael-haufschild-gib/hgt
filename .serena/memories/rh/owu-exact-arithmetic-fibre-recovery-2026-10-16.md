# OWU: exact arithmetic-fibre recovery — formalized 2026-10-16

New modules in formal/GaloisForLFunctions/RHTower:
- OddSectorInteriorTraceCoordinates
- OddSectorInteriorTraceRepair
- OddSectorSmoothFormDensity
- OddSectorExactFibreRecovery

Main unconditional structural result: RHTower.OddSector.exists_exact_fibre_recovery. For every positive aperture a and every actual complete odd form source u, there is a sequence of single smooth odd sources with compact support strictly inside (-a,a). Every source has exactly u's arithmetic trace at ALL integer lags. Its autocorrelation converges pointwise to u's profile and its literal Weil energy converges to u's energy. This is profile/energy recovery, not convergence of chosen purified source vectors in form norm.

Mechanism: odd projection of the dense smooth interior form core; finite strict active lag set log n < 2a (including vanishing diameter traces); both signed isolated coordinate rays constructed inside the same arbitrary aperture; positive finite repair with coefficients tending to zero; exact same-window odd purification. No continuity of a spectral-factor selection is assumed.

exists_smooth_blind_unit_recovery gives exact blindness and unit physical norm at every step. exists_blind_minimizer_without_relaxation_gap proves the smooth blind unit infimum equals an attained complete blind odd minimum, for every positive aperture. Removes the nonlinear exact-smoothing/relaxation gap. It DOES NOT prove the common minimum nonnegative, construct a global positive arithmetic source, remove the slit cut, or prove RH.

All four modules passed foreground lake --old env lean -j 1 <module> checks without warnings; wired into RHTower.lean without an umbrella/full build. Scratch #print axioms audit of all 39 public declarations: only propext, Classical.choice, Quot.sound. No added axioms, proof holes, numerical experiments or heartbeat increases. Compiled artifacts current; owned scratch cleaned.

Global lint --check-generated remains blocked by seven unrelated concurrent unwired MobiusDivisor/PaperTheta modules and generated-index drift. Indexes regenerated after the last lint check; do not claim a full repository lint pass.

Paper proof and exact audit details: docs/drafts/pipeline/3-formalized/owu-exact-arithmetic-fibre-recovery-2026-10-16.md.

An earlier shifted twisted-arc attempt remains OPEN CORE: multiplying the spectral square by frequency squared changes M² to M²(M−1/4); existing arc boundary conditions do not justify the proposed positive resolvent transport. No no-go or route retirement was proved.
