# RHTower area umbrella is GREEN (2026-08-07 06:20)

`lake build GaloisForLFunctions.RHTower` → **17315 jobs, exit 0**.
`lake build GaloisForLFunctions.HTGeometry` → 15307 jobs, exit 0.

First complete area audit of the session. It validates all eleven modules added here in situ, with no
cross-module name collisions.

## Collisions fixed to get there (all were pre-existing, none mine)

1. `RHTower.norm_natCast_cpow` — duplicated in `ZetaVerticalLineBound` and
   `PeriodicLSeriesRightAsymptotics`. Both were wrappers of mathlib's
   `Complex.norm_natCast_cpow_of_pos`; deleted the copy in the lighter file and called mathlib.
2. `RHTower.setIntegral_Ioi_comp_add_right` — real-valued in `ComplementaryPacketCofinalIsometry`,
   complex-valued in `EulerHedenmalmMobiusStokesInverse`. Renamed the committed real one to
   `setIntegral_Ioi_zero_comp_add_right` (it is the `L = 0` case of the existing primed variant).
3. `RHTower.deningerExtendByZero` — committed `def` in `DeningerExtendByZero`, new `theorem` in
   `DeningerFineLifting`. Renamed the theorem to `deningerFineAction_extendByZero`.
4. `RHTower.deningerExtendFun` — alternating-form extension in `DeningerResidueSequence` (committed,
   8 occurrences) versus scalar-function extension in `DeningerDolbeaultFine` (modified, 31
   occurrences). Renamed the committed smaller one to `deningerExtendAlternating`.

Pattern: every collision was two genuinely different lemmas sharing a generic name, invisible to
`lake env lean <file>`. Rename in whichever file is NOT in flight, and prefer deleting a duplicate
outright when mathlib already has the statement.

## Remaining lint errors (not mine, do not fix)

`DeningerCalderonWittCrossPrimeSingularCorona` and `RouteRTwoThreeGammaSingularCoronaProducer` are
untracked, written ~04:09–04:15, and not in the umbrella. Wiring in another session's untracked
in-flight modules risks breaking the umbrella that is now green; leave them to their owner. The three
`stale generated file` errors follow from the same churn.
