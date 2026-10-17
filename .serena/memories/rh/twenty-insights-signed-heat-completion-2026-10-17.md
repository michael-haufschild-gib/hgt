# Fourth contribution completed after goal clearance

The user cleared the original twenty-insight goal, then asked to finish unfinished work. The scope was explicitly stated as completing contribution 4 (signed Gaussian heat orientation). That scope is finished. Do not resume the remaining sixteen research packages without a new request.

Authoritative card: docs/drafts/pipeline/1-in-progress/tt-la-th-hcf-hj-twenty-insights-2026-10-17.md. Four completed contribution packages, 113 audited public declarations, eleven Lean modules. Prior checkpoint: `mem:rh/twenty-insights-parity-transport-2026-10-17`.

## Exact mathematical result

For actual centered Xi points z_q and Deninger orientation epsilon_q=sign(Re z_q), the complex Gaussian integral gives z_q/sqrt(pi) times integral_R exp(-z_q^2 t^2) dt = epsilon_q, without RH. Define A_N by the same signed integral restricted to [-N,N], acting diagonally on the full multiplicity-exact ell2 carrier. The source height gap and sector estimate give Re(z_q^2)>=2 and |z_q|^2<=2 Re(z_q^2). The Gaussian tail estimate yields ||A_N-D||<=2 exp(-N^2), hence operator-norm and strong convergence to the involutive FE-orientation isometry D.

A_N reverses pure functional-equation parity. For the canonical odd Hurwitz vector u, V_N=A_N u is even, tends to the canonical even witness Du, and Q(V_N) tends to -E. Off RH, every sufficiently large cutoff has strictly negative Weil energy. Eventual nonnegativity on this one explicit sequence is equivalent to RH. This is one insight package; do not count corollaries separately. It constructs a spectral heat operation, not arithmetic source positivity or an arithmetic test-function realization.

## Files and verification

- formal/GaloisForLFunctions/RHTower/ComplexSignedGaussianHeat.lean: 8 declarations; exact complex signed Gaussian formula and uniform tail bound.
- formal/GaloisForLFunctions/RHTower/XiSignedHeatOrientation.lean: 11 declarations; actual Xi specialization, uniform gap/error, Hilbert cutoff, parity reversal.
- formal/GaloisForLFunctions/RHTower/XiSignedHeatOrientationConvergence.lean: 15 declarations; bounded operators, operator-norm convergence, explicit even witnesses and energy consequences.

All three narrow `lake --old build +Module:olean` builds passed. Final individual `lake env lean` checks all passed with no owned module warnings. All 34 declarations checked via /tmp `#print axioms`; only propext, Classical.choice, Quot.sound. No axioms, sorry, admits, unsafe, heartbeat increases, numerical experiments, external research, full builds, or umbrella builds were added/run. RHTower umbrella imports each new module once. Index generation and git diff --check passed. Final formal lint exited 1 with 17 unrelated unreachable-module errors: OddSectorImaginaryZeroMorseBound and 16 HTGeometry modules including SymbolicTransferOperator. No lint error concerns any of the eleven owned completed modules.

The failed-route card docs/drafts/pipeline/5-failed/heat-even-hurwitz-target-parity-obstruction-2026-10-17.md now records this explicit signed-heat construction as the stronger positive survivor of the raw-even-target approximation obstruction. Other agents' changes and frontier map preserved. No commit or push performed.