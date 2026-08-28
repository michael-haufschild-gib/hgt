SC hard-frontier result (2026-08-28).

User constraint: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is read-only; this work did not edit it.

New Lean module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalFinitePortStokesCapacity.lean`

Main declarations:
- `sigNeg_le_of_finiteOnePortSumPullback`: sum of k one-port quadratic carriers has negative index <= k after arbitrary linear pullback.
- `sourceZeroHorizontalSharedReservoir_twoOrientation_finitePort_obstruction`: an off-line source packet and reflection cannot both factor through k one-port sums when k < m-1.
- `GlobalPuiseuxWittFinitePort.not_both_sourceZeroHorizontal_orientations_land_in_finiteGlobalWitt`: specialization to k copies of any coefficient-generated global Stokes Witt carrier.
- `GlobalPuiseuxWittFinitePort.xiOffLineFiniteGlobalWittPortExhaustion`: for every off-line Xi fibre and finite k, an injectively prime-labelled packet of size k+2 defeats all k-port global Witt landings.

Mathematical meaning:
- Earlier one-port SC obstruction is not repaired by any fixed finite direct sum, finite matrix enlargement, or finite Pontryagin negative index.
- Off-line source reflection forces negative-port demand to grow without bound with packet size.
- Surviving SC object must have genuinely unbounded/infinite negative index before orientation selection, or abandon finite sums of one-port quadratic landings.
- This does not prove RH and does not construct the required infinite-index source-selected positive sector.

Conjecture loop:
1. Boundary annihilation conjecture falsified by corpus: actual Xi theta eigenmode boundary flux is nonzero off line and equals transverse charge times positive root energy.
2. Finite-port absorption conjecture falsified by exact inertia growth.
3. Unbounded-port classification paper-proved and Lean-proved.

Card:
`docs/drafts/pipeline/5-failed/sc-finite-port-stokes-capacity-exhaustion.md`

Verification:
- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalFinitePortStokesCapacity.lean` passed.
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalFinitePortStokesCapacity` passed (leaf only).
- Module wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built.
- Four capstone `#print axioms` outputs are exactly `[propext, Classical.choice, Quot.sound]`.
- Forbidden-declaration scan and scoped diff check clean.
- Corpus index/search resolves theorem.
- Full check_axioms.sh was updated 356->360 but an attempted full run was externally SIGTERM'd after about 140s with no output; prior 356 audit was green and the 4 new capstones were separately verified.
- Lint detects new module as reachable; it still fails only on unrelated concurrently unwired modules.
- No Lean/Lake processes from this task remain. A foreign concurrent process on XiCenteredRealShiftDiagonalExtractor was observed and deliberately not killed.