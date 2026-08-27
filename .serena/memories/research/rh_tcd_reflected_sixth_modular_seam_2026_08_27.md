# TCD reflected-sixth modular seam (2026-08-27)

Status: `[NEW] [PAPER-PROVED] [LEAN-PROVED] [GLOBAL C1 OPEN]`.

Corpus-grounded conjecture loop rejected separate complete-source log-jet envelopes, generic positive-mixture closure, and dominant-tail sixth-jet bounds because they erase modular cancellation. Successful pivot retained full self-dual four-state theta ODE through eighth order.

Exact result: for `M = theta_3(i)`, `R = pi*M^4`, `X=R^2`, and complete-source seam jets `f_j`,
`f0^2*(f2*f6-f4^2)+9*f0*f2^2*f4-9*f2^4 = M^4*P_ref(X)`,
where `P_ref(X)=127575/4096-(1828575/16384)X+(6333795/65536)X^2-(7447545/262144)X^3+(397305/262144)X^4-(48411/262144)X^5+(229545/8388608)X^6+(225/1048576)X^7-(375/33554432)X^8`.

New bounded chamber: existing lower bound gives `191/10 < X`; exact `exp(-pi)` upper enclosure plus geometric theta majorant gives `M < 1091/1000`, hence `X < 20`. Expansion about `191/10` proves `P_ref>0` throughout. Odd seam jets vanish, so native reflected-product second-sixth determinant is four times modular invariant. Continuity yields `delta>0` with strict curvature for every `|x|<delta`.

Files:
- `formal/GaloisForLFunctions/HTGeometry/PolynomialODEJetClosure.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaModularDifferentialClosure.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspFullReflectionSixthModularSeam.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- card `docs/drafts/pipeline/1-in-progress/theta-center-mixed-odd-four-point-cusp.md`
- frontier ledger updated.

Key declarations: `modularThetaSixthSeamJetEliminationPair`, `modularThetaReflectedSixthSeamClosure_of_ode`, `thetaCuspFullSource_reflectedSixthSeam_eq_modularClosure`, `thetaCuspReflectedSixthSeamModularPolynomial_source_pos`, `thetaCuspFullSourceReflectionSecondSixthCurvature_zero_pos`, `exists_thetaCuspFullSourceReflectionSecondSixthCurvature_pos_near_zero`.

Audit: direct `lake env lean` passed; targeted leaf `lake build GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthModularSeam` passed; `scripts/formal_tools.py lint` passed; `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`; no stale Lean processes.

Novelty audit: closest primary source Planat--Solé, arXiv:2608.19160, proves different second-level concavity/double-Turan statement and does not state this polynomial/chamber or center-mixed odd wall.

Open core C1b: extend pointwise curvature from seam neighborhood across global radial carrier via modular-flow continuation plus outer atom-pair scale separation; then prove weighted center-mixed mixture/covariance margin. Do not revert to generic mixture closure or separate sixth-log envelopes.