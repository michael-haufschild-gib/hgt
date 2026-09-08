# CCM-FU: repaired envelope controlled by a different parent successor

## Exact result

At cutoff 17, let P={3,5,7}, S=P+11, E=S+2, B=Q_empty. The closed
Lean theorem `mobiusDivisorSeventeen_repair_certificate` proves:

- Psi(P)+1/20 <= B;
- B+1/200 <= Psi(S);
- 2 is the unique least-energy available choice from S;
- Psi(E)+1/200 <= Q_S;
- Q_P+1/100 <= Q_E;
- Q_(P+13)+1/50 <= Q_(E+13).

The forced state exits admission and the greedy repair restores it. Each
repaired energy increases relative to its matching parent state. Nevertheless
both repaired branches are below Q_S, which was already included in Psi(P).
Thus the full envelope decreases despite both matching-energy increases.

This refutes inherited contraction of the prescribed pair, including its
version applied only to forced exits from admission. Its positive survivor
is the strict complete-envelope bound using a different original successor.
It proves neither general greedy repair nor an exhaustive prime order or RH.

## Dependency-closed source proof

The only nonzero retained coordinates at P are empty, {2}, {11}, {13}:

`a=K_1-K_3-K_5-K_7+K_15`,
`b=-K_2+K_6+K_10+K_14`, `c=-K_11`, `d=-K_13`.

Here every K is the literal unsigned divisor Abel channel at 17. Squarefree
support and exact prime-factor identities establish this full field; the
terminal channel and every nonsquarefree channel vanish. No source coordinate
or unprocessed prime is discarded.

The reused logarithm-series inequalities, harmonic Euler-constant correction
and rational square-root enclosures prove
`-.402<=a<=-.401`, `.076<=b<=.078`, `-.125<=c<=-.124`,
`-.080<=d<=-.079`, and `.360<=B<=.365`. Signed interval products retain
the complete divisor defect at every Abel step.

Literal mergers give all current and successor energies. In particular
Q_S=(a+c)^2+b^2+d^2, Q_E=(a+c+b)^2+d^2,
Q_(S+13)=(a+c+d)^2+b^2, and Q_(E+13)=(a+c+b+d)^2.
Squaring the analytic intervals bounds every comparison in the certificate.
After S the only available primes are 2 and 13, so the minimum proof checks
every alternative; after E the only available prime is 13.

## Lean sources and validation

- `formal/GaloisForLFunctions/RHTower/DivisorTwentyTwoAnalyticBounds.lean`:
  two new source theorems for the four-coordinate profile and original
  diagonal at 17, reusing its existing analytic certificate machinery.
- `formal/GaloisForLFunctions/RHTower/MobiusDivisorSeventeenRepair.lean`:
  full source identification, every energy formula, all alternatives and
  the closed repair certificate.
- New module is imported by `GaloisForLFunctions.RHTower`.

Scratch checks and exact `lake env lean` module emission passed for both proof
phases. The audit of exactly the three new declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`. The new leaf is wired into
its umbrella, and the generated indexes were refreshed.

`scripts/formal_tools.py lint --check-generated` passes, with existing
large-file warnings. No umbrella build was run. The previously identified
`lake build` packaging audit remains pending because it expands broad stale
prerequisites; targeted kernel checks do not assert packaging completion.

The [RunPod diagnostic](../2-fully-proven/computations/ccm-fu-repair-inherited-contraction-2026-09-08/README.md)
exposed the witness. Its numerical data supply no Lean premise. The actual
proof derives its rational bounds from analytic inequalities and exact
arithmetic. Only new declarations are included in the axiom audit.

## Remaining arithmetic target

A general repair proof must bound every repaired successor by the original
budget. Comparing it with its matching original state is too strong. This
witness shows that an already admitted different successor can supply the
bound. Producing such comparisons uniformly across changing cores, all
overlapping fibres and all cutoffs remains open.
