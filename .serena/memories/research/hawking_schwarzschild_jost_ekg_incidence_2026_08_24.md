# Hawking Schwarzschild Jost/EGK incidence result (2026-08-24)

Stationary source-faithful result:
- New module `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSchwarzschildJostIncidenceNoGo.lean`.
- Schwarzschild real-axis Evans/Wronskian normal form `W=-2 i w cosh(eta)e^{i phase}` is nonzero for real `w != 0`.
- Theta divisor `alpha=w+ia` uses `w` as physical frequency and `a` as source tilt, not complex black-hole frequency.
- Source-dressed response vanishes at every Xi divisor while Evans denominator remains nonzero: scattering/source zero, not QNM pole.
- Exact real-axis optical identity is incoming = reflected + horizon flux.
- QNM/direct/branch-cut field energy contains pairwise interference; no positive orthogonal pole+cut identity follows from Teukolsky contour deformation.
- Existing `ThetaCuspHawkingQNMBranchCutCompletionEndpoint.lean` comments now label its pole+cut norm ansatz as falsified physical identification/conditional algebra.

Nonlinear EKG survivor:
- New module `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingEKGCubicTriadIncidenceNoGo.lean`.
- At every divisor `alpha=w+ia` and every `delta>0`, exists `epsilon>0` with `2 epsilon<delta` such that triad `(w+2epsilon, epsilon, -epsilon)` obeys `nu1-nu2+nu3=w` and all three exact tilted theta amplitudes are nonzero although target amplitude is zero.
- Proof uses isolated Xi zeros plus `XiC(i a)>0` throughout divisor strip.
- Therefore EKG cubic kinematics can fill every theta dark sector, RH-blind. Remaining actual dynamics is precise radial/angular second-order Teukolsky overlap zero/nonzero/sign; KMS/passivity cannot supply it.

Verification:
- Direct `lake env lean` and exact targeted `lake build` passed for both new modules.
- New theorem axiom audits show only `propext`, `Classical.choice`, `Quot.sound`.
- No umbrella build, no git.