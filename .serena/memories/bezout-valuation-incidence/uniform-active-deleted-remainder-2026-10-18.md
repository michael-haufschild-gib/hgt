# Uniform active-deleted compensated remainder (2026-10-18)

Problem 4 strict interior contraction for all positive damping remains open. User cleared the goal and requested completion of started Lean work, wiring, docs, then pause; closeout is complete. Do not mark complete on auxiliary results. No hgtl7, RH work, numerical experiments, new axioms/open analytic premises, heartbeat increases, full/umbrella builds, README writes, commit or push. Use the live Lean corpus before new code.

## Completed new leaf
`formal/GaloisForLFunctions/BezoutValuationIncidence/UniformActiveDeletedCompensatedRemainder.lean`, 250 lines, SHA256 `3107e7af3a1b51c7d8ca18b4ec2b1f2d97e5e035aa4e188eb1ec8e9d5a551f02`. Imported once in area umbrella. Original source `lake --old env lean -j 1 -o ... -i ...` exited 0, session 21412, no diagnostics. Final scratch audit 18267 exited 0: all five public closures standard `propext`, `Classical.choice`, `Quot.sound`, plus 30 mathlib name probes. No heartbeat change. Index 11333 passed; indexed capstone verified via research. Lint 59443 exit 1: sole error package-root placement `TransHorizonIncidenceMechanics.lean`, 381 existing warnings, no owned finding.

Public APIs: `summable_pmPowerDampedMobius_logWeight`, `summable_pmShiftedExponentSecondCoeff_logWeight`, `exists_pmPowerDampedDivisor_harmonic_compensated_bound`, `exists_pmShiftedExponentProduct_harmonic_compensated_bound`, `exists_pmActiveDeletedCovarianceDiagonal_compensated_bound`, in BVI namespace. Last gives for every epsilon>0 an unconditional C>=0 with |actual active-deleted diagonal - shifted covariance * H_comp| <= C for all T.

Mechanism: existing shifted coefficient bound by d(n)n^-epsilon and existing divisor-square/log-square summability imply actual coefficient log moments. Reuse existing uniform divisor-harmonic theorem. Expand (F_e-rho)(F_(1+e)-rho), retain rho^2(H-H_comp), and bound terminal average by (1+|rho|)^2. Actual H_comp(T)=H_T-2T/(T+1), and H-H_comp in [0,2].

Card: `docs/drafts/pipeline/3-formalized/bvi-uniform-active-deleted-compensated-remainder-2026-10-18.md`. Certificate and raw logs `logs/bvi-uniform-active-deleted-2026-10-18-*`. Twenty-three search outputs archived, including exhaustive 130-hit logWeight query. Existing CoprimeDirichletDivisorProduct.summable_logWeight_dconv assumes input log moments and does not discharge actual arithmetic moments. Eight reused APIs independently axiom-audited (18588). Thirty completed scratch/search files hash-verified and removed.

## Follow-up completed; research paused
The full uniform residual |2 M_int+2 c_int H_comp-E|<=C is now formalized in `UniformRenormalizedInteriorEnergyRemainder.lean`. Card: `docs/drafts/pipeline/3-formalized/bvi-uniform-renormalized-interior-energy-remainder-2026-10-18.md`. This is not strict contraction. The exact equivalence to bounded actual energy is formalized, but neither side is asserted.

The adjacent estimate reuses the bounded fields from PMAdjacentDivisorCorrelation, the existing sharp unit CRT defect, public divisor-average identity, and two successive truncations. No RHTower visibility edits or replacement counting theorem were needed. Quantitative truncation, positive power rate, compensated Abel bound, predecessor remainder, and final residual are all complete, audited, wired, indexed, and documented. Latest certificate: `logs/bvi-uniform-interior-remainder-2026-10-18-manifest.json`; final summary in `mem:bezout-valuation-incidence/compensated-abel-next-proof-plan-2026-10-18`.

All old scratch/search processes are terminal and owned temporary files archived/removed. Do not resume old handles. Further research paused at user request.
