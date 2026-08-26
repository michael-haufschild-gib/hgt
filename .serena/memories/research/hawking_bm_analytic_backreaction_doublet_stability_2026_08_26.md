# BM analytic backreaction doublet stability (2026-08-26)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMAnalyticBackreactionDoubletStability.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean`.

Result: the requested local nonlinear horizon/boundary exclusion is false. Let the returned determinant be the exact physical BM Jost determinant plus coupling times the complete gauge-fixed causal total angular period. Each negative-branch BM target has an analytic QNM root branch with velocity equal to the previously computed nonzero total-period pole velocity. For an off-line Xi divisor, reflected and Schwarz-conjugated branches remain distinct near zero coupling.

Stronger result: arbitrary jointly analytic all-order corrections of form `c^2 * higher(c, omega)` preserve both root branches and their local separation. Thus no regular perturbative Einstein–Teukolsky completion sharing the computed first nonlinear coefficient can forbid the resolved doublet. Exclusion requires leaving this regime: finite-coupling exceptional-point collision, loss of analyticity/simple-root Fredholm structure, branch escape through spectral boundary/infinity, or a global admission/finite-energy law. Existing bifurcate-beat and Hedenmalm summability criteria are equivalent to criticality/RH; corpus lacks a source-faithful Einstein evolution theorem establishing them.

New declarations:
- `d4BMXiGaugeFixedTotalPeriodTargetNumeratorMinus`
- `d4BMXiGaugeFixedTotalPeriodReturnedJostMinus`
- `d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostMinus`
- `exists_d4BMXiGaugeFixedTotalPeriodReturnedJostPoleBranchMinus`
- `exists_d4BMXiGaugeFixedTotalPeriodPartnerPoleDoubletStable`
- `exists_d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostPoleBranchMinus`
- `exists_d4BMXiGaugeFixedTotalPeriodAllOrderPartnerPoleDoubletStable`

Verification: targeted Lean compile passed. All four new theorems use only `propext`, `Classical.choice`, `Quot.sound`. `formal_tools.py lint` still exits 1 only on pre-existing unrelated unreachable modules; new module is reachable and has no forbidden declarations. Temporary sources and generated oleans removed. No git, docs, cards, endpoint ledger, or frontier ledger touched.

Literature audit: BM exact simple roots (hep-th/0609028), AIME adds modes (2112.11168), Warnick horizon-regular semigroup QNMs remain complex/discrete (1306.5760), Green et al. nonlinear QNM pairing/coupling (2210.15935). None supplies local root annihilation.