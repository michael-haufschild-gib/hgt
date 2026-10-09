# Bounded mixed-sign first probe does not imply potential convergence

Status: RETIRED — obstruction and positive interpolation survivor formalized.

## Rejected receiver

Deduce local signed-potential summability from boundedness of the m=2 actual
probe at positive integer cutoffs, without controlling either local one-sided
moment. Even exact zero at every such cutoff does not suffice.

## Formal obstruction

`RHTower.exists_zero_firstProbe_with_divergent_excess_and_deficit` constructs
coefficients with Q_2(k+1)=0 for every natural k, but nonsummable excess,
deficit, and signed potentials at log 2. This is stronger than a lower bound
alone: both upper and lower integer-cutoff bounds hold.

The construction begins with reciprocal paired-kernel weights. Consecutive
lift coordinates leave an untouched integer between them; its positive-excess
potential term stays exactly one. Signed spikes at the lift coordinates set
the desired probe values while exact finite support protects earlier values.
The local-deficit upper-bound criterion excludes summable deficit as well.

## Strongest positive survivor

`RHTower.exists_weilLogShiftFirstProbe_interpolation` realizes any prescribed
real tail history while fixing an initial coefficient head and every off-lift
coordinate. `RHTower.weilLogShiftFirstProbe_surjective` records surjectivity of
the entire integer-cutoff history map. Moreover every prescribed history has
a realization with divergent excess and signed potentials, by
`RHTower.exists_weilLogShiftFirstProbe_history_nonsummable`.

Paper proof: dependency-closed, only local Lean corpus.
Lean status: five public theorems and one definition compile; all six axiom
audits contain only `[propext, Classical.choice, Quot.sound]`.
Source: `formal/GaloisForLFunctions/RHTower/WeilLogShiftFirstProbeInterpolation.lean`.
Umbrella/API wired. Global lint has seven unrelated unwired modules, listed on
`../3-formalized/weil-logshift-first-probe-interpolation.md`.

Second-pass audit extracted arbitrary exact interpolation, rather than only a
bounded counterexample. Both the survivor and obstruction are formalized.
No claim about intervening real cutoffs, all probe indices simultaneously,
external novelty, or an RH proof.

Follow-up: boundedness also fails to control moments on the injective recovery
mesh, despite that mesh determining every visible coefficient. The exact ±1
counterexample and adaptive positive survivor are recorded in
[the recovery-mesh no-go](weil-logshift-bounded-recovery-moment-control.md).
