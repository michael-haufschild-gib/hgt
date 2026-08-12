# Mass-shifted strict-frontier Christoffel source wall (2026-08-12)

## Result
Formalized an admission-sensitive, source-first arithmetic law in
`formal/GaloisForLFunctions/RHTower/XiShiftedStrictFrontierChristoffelSourceWall.lean`.
At an occupied strict frontier `y0 = tau_(n+1)`, with `d=n+1`, the next canonical admitted
norm vanishes while the preceding actual adaptive source stays strictly positive. Freezing the
terminal monic null flag `c` and comparing it with moving canonical admission gives exact
Pythagorean variational minimization:
`Q_v(c) = N_(d+1)(v) + <R_v,R_v>_v >= N_(d+1)(v)`.
The corpus integral-Lipschitz theorem and `Q_y0(c)=0` imply
`N_(d+1)(v) <= W(c) (v-y0)`. Consequently the intrinsic completed source wall
`Wall_d(v)=S_d(v)/(16*N_(d+1)(v))` dominates a positive multiple of
`1/(v-y0)` and is not interval-integrable on any nontrivial right interval.

False RH forces cofinally many such strict rungs. Lean proves:
`RH <-> not XiShiftedCofinalNonintegrableChristoffelSourceWallPhase` and
`RH or XiShiftedCofinalNonintegrableChristoffelSourceWallPhase`.
This is a phase equivalence, not an RH proof.

## Conjecture loop
- Next norm killed at strict frontier: proved.
- Previous source also collapses: falsified; Jacobi lower bound keeps it positive.
- Arithmetic analyticity contradicts wall: falsified; pole comes from endogenous next-admission completion, not literal numerator.
- Fixed frozen null packet linearly majorizes moving next norm: proved.
- Existing recession/secant budgets make completed quotient finite-action: falsified; they control numerator only.
- Universal finite nonzero simple-pole residue: falsified as universal route; delayed first contact may yield flatter norm collapse. Reciprocal lower domination is robust.

## Exact remaining open theorem
Prove exact adaptive Christoffel-completed arithmetic producer is locally finite-action/admissible
at every positive mass. This would contradict strict-frontier nonintegrability and exclude occupied
strict frontiers. Do not substitute an orientation map, fixed linear reporter, external schedule,
or numerator-only budget.

## Files
- `formal/GaloisForLFunctions/RHTower/XiShiftedStrictFrontierChristoffelSourceWall.lean`
- `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3.692--9.3.698
- `docs/drafts/pipeline/3-formalized/mass-shifted-strict-frontier-christoffel-source-wall.md`
- wired in `formal/GaloisForLFunctions/RHTower.lean`

## Verification
Direct `lake env lean` and targeted
`lake build GaloisForLFunctions.RHTower.XiShiftedStrictFrontierChristoffelSourceWall` pass.
Axiom audit of main linear-collapse, nonintegrability, and RH-phase capstones reports only
`propext`, `Classical.choice`, and `Quot.sound`. Repo lint's nonzero exit was due unrelated
concurrent unwired modules / existing large-file warnings; it did not flag this wired module.
External novelty remains unverified; generic norm-ratio blow-up is bridge/classical material.