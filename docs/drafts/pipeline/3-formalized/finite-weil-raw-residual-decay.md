# Finite Weil raw residual decay

Status: FORMALIZED. Paper proof and native Lean audit complete.

Sources: local Lean corpus and installed Lean dependencies only. No web, papers, or numerics.
Prior checks: lexical `correction residual` in WeilLogShift finds only the existing
residual mean and covariance identities; scoped source search finds no residual
Lipschitz, slope, or contraction theorem. Existing weak-law increment is fresh.
Compact-space Kantorovich duality cannot directly establish a noncompact Gaussian
transport limit; pursue exact logarithmic curvature instead.

Put n=r+1, A=k+2, E=sum(m_i i), Q=sum(m_i T_i),
F(x)=A(1-A(log(A+x+1)-log(A+x)))-x.
For canonical indices, F(i)=n T_i-i. On [0,r],
F'(x)=A^2/((A+x)(A+x+1))-1 and |F'(x)| <= 2n/A.
Indeed 1-A^2/((A+x)(A+x+1)) equals
x/(A+x) + (A/(A+x))((x+1)/(A+x+1)), bounded by (2x+1)/A <= 2n/A.

E belongs to [0,r]. Centering minimizes weighted quadratic deviation, so
W=sum m_i [n(T_i-Q)-(i-E)]^2
 <= sum m_i (F(i)-F(E))^2
 <= (2n/A)^2 sum m_i (i-E)^2 = (2n/A)^2 V_index.
This finite inequality holds for every r,k. At k=2n^2+t, it gives W <= V_index/n^2.
The existing unconditional limit V_index/n -> 1/4 implies W -> 0 for arbitrary t:Nat->Nat.
Cauchy-Schwarz and total mass one then give (sum m_i |n(T_i-Q)-(i-E)|)^2 <= W,
so the raw first-moment mismatch also tends to zero. This strengthens the old
normalized residual W/n -> 0 to convergence before Gaussian scaling.

Plan:
1. Formalize residual profile, derivative, and finite Lipschitz bound.
2. Prove exact finite variance contraction and quadratic-width bound.
3. Close unconditional raw second- and first-moment limits.
4. Native leaf checks, native axiom audit, umbrella wiring, local index and lint.

Final roots must have only structural parameters; no unresolved analytic premises.
No full builds, heartbeat increases, commits, or pushes.


## Formal closure — 2026-10-11

Status: FORMALIZED. Exact proposed finite contraction and both unconditional roots proved.
For arbitrary offsets t:Nat->Nat at k=2(r+1)^2+t(r), the raw centered mismatch
D_i=(r+1)(T_i-Q)-(i-E) tends to zero in weighted mean square and mean absolute error.
No division by sqrt(r+1) is required. The finite statement is
W <= (2(r+1)/(k+2))^2 V_index for every r,k; on the quadratic family,
W <= V_index/(r+1)^2. The existing V_index/(r+1) -> 1/4 closes the new limit.
The first-moment root follows from the exact finite Cauchy-Schwarz bound gap^2 <= W.

Files under formal/GaloisForLFunctions/RHTower:

- WeilLogShiftResidualSlope.lean: residual profile, canonical-index identity, derivative,
  slope bound, interval Lipschitz bound (5 declarations).
- WeilLogShiftResidualContraction.lean: mean interval, profile variance identity,
  unconditional finite contraction and quadratic-width bound (4 declarations).
- WeilLogShiftRawResidualDecay.lean: raw mean-square root, absolute-gap definition,
  nonnegativity, squared and square-root bounds, raw first-moment root (6 declarations).

Verification: all three final native leaf builds passed with empty logs. Native
final audit checked all 15 public declarations (2 definitions, 13 theorems) and
20 explicit API haves. Axioms are only propext, Classical.choice, Quot.sound.
Metadata found no issues; seven direct imports fresh, five incoming imports audited,
exactly one umbrella import per leaf, no duplicate authored declaration identifiers.
Both convergence roots appear in the refreshed local index. Scoped git diff --check passed.
No full or umbrella builds, heartbeat changes, commits, pushes, web, external papers,
or numerical experiments.

Operational correction: an early leaf build was accidentally started while the
API scratch check remained live. That leaf's owned PID was terminated and its
exit143 and process absence verified before replacement; subsequent builds were sequential.
The final slope source uses explicit derivative normalization and ring_nf for the
canonical-index identity; its earlier informational ring diagnostic is gone.

Artifacts: /tmp/hgt-raw-residual-{api.lean,api.log,metadata.py,metadata.json,
declarations.json,incoming-imports.txt,final-audit.lean,final-audit.log,
roots-search.json,lint.log,close.py}; per-leaf /tmp/hgt-WeilLogShift*.log.

Global formal lint: 13 errors and 367 warnings, all outside the three new leaves.
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMPolarOddPrimeJumps
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzCompactCharacter
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzEnergyDomain
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzPowerRegularization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzSourceIdealBridge
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzWallApproach
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilLogDensityLockRigidity
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiGaussianHeatHankelPolynomialHorizon
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.DanskinPerturbationBound
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.FejerNearLattice
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular
- error: proof debt: formal/GaloisForLFunctions/RHTower/CCM/CCMPolarOddPrimeJumps.lean:104: sorry (theorem ccmPolarOddSource_eq_core_add_atoms)
