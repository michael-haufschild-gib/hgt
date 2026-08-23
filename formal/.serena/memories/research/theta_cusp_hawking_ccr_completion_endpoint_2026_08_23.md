# Theta-cusp Hawking CCR completion endpoint (2026-08-23)

[CORPUS] Added `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovCCRCompletionEndpoint.lean` and imported it from `formal/GaloisForLFunctions/RHTower.lean`.

[LITERATURE] Exact/perturbative moving-mirror sources distinguish the Born beta block (sum-frequency Fourier data, first order) from alpha (identity/difference-frequency sector). Bosonic CCR first requires beta exchange symmetry; beta-beta-adjoint is absorbed by gain at second order. Relevant primary sources: Obadia--Parentani, arXiv:gr-qc/0103061; weak-nonstationary DCE formulas in Akhmedov et al., EPJC 2022; Good et al., arXiv:2103.07374 on moving-mirror Gaussian channels.

[VERIFIED] New Lean endpoint proves:
- `thetaCuspHawkingBornPairKernel p q = 2 i p q XiC(p+q)`, agrees with literal real-frequency moving-mirror Born variation, and is symmetric under mode exchange.
- For every real coupling lambda and every complex continued frequency z, beta=lambda*thetaCuspBalancedHawkingBornAmplitude(z), number N=norm(beta)^2, and gain=sqrt(1+N) give exact CCR `gain^2-norm(beta)^2=1`.
- Full Nambu signed Hermitian form is preserved for arbitrary input amplitudes, not only basis normalization.
- Pure Gaussian anomalous covariance saturates `norm(M)^2=N(N+1)`.
- Dark frequencies are identity/vacuum fibres at every coupling.
- RH iff every unit-coupling identity fibre lies on real physical-frequency sheet.

[FALSIFIED] Bare pointwise CCR/Gaussian purity cannot be RH producer: exact completion exists unconditionally at every complex continuation frequency, including any hypothetical off-line dark frequency. This sharpens the earlier Born/port mismatch and QEI wall.

[OPEN CORE] Needed producer is a continuum, source-causal analytic colligation coupling distinct frequencies and identifying its alpha/beta blocks with theta Weil even/odd packet channels. Pointwise squeeze completion is too local and non-holomorphic in z; do not claim it is full moving-mirror continuum scattering.

Verification:
- direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovCCRCompletionEndpoint.lean`: clean.
- targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBogoliubovCCRCompletionEndpoint`: passed.
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- full `scripts/formal_tools.py lint` sees endpoint reachable but fails on unrelated pre-existing unreachable modules: `RHTower.XiLocalZeroDensity`, `HTGeometry.CriticalSheetLabelInertiaOrbit`, `HTGeometry.CriticalSheetLabelInertiaOrbitAction`, `HTGeometry.RationalCharacterApproximation`.

See prior memories `mem:research/theta_cusp_hawking_qei_endpoint_2026_08_23`, `mem:research/theta_cusp_hawking_backreaction_passivity_endpoint_2026_08_23`, `mem:research/theta_cusp_hawking_partner_instability_endpoint_2026_08_23`, and `mem:research/theta_cusp_hawking_wigner_smith_winding_endpoint_2026_08_23`.