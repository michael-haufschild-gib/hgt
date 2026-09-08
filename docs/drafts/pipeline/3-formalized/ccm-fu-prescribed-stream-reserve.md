# CCM-FU: linear helper cost for a prescribed prime stream

- Stage: 3-formalized.
- Type: [BRIDGE], derived from the actual two-coordinate source cone.
- Full chain: actual divisor source → renewable signed reserve → exhaustive prime selection → uniform O(M) signed Abel bound → RH.
- Result: bounded-quotient prescribed streams have linear helper cost, uniform prefix control and a final complete successor-envelope decrease.
- RH status: open. The main fixed-positive-weight complete-path candidate is unchanged; this result addresses the successor-envelope route.

## Exact result

There are fixed integers b ≥ 15 and K, and H > 0, such that for every
C > 0 there are A, C' > 0 with the following property. Put
M = 14(b+1)N and let Q be the actual coupled-two source-window capacity.
Let P contain every prime below fifteen except two, omit two, and leave
the source windows unused initially. Assume its complete successor envelope
Psi(M,P) ≤ C M².

For any distinct prescribed prime list t, every p in t must satisfy
p < M, p not in P, p ≥ 15 and floor(M/p) ≤ 14. If

    (K+1)|t| + ceil(A sqrt(M)) ≤ Q−1,

there is a distinct list l containing t as an order-preserving sublist,
using only t and source-window primes, with exactly

    |l| = (K+1)|t| + ceil(A sqrt(M)).

Every prefix L of l satisfies both

    |sum_{p in L} sqrt(p) I_0(M,p,P)|
      + |sum_{p in L} sqrt(p) I_2(M,p,P)| ≤ H sqrt(M),
    Psi(M,P union L) ≤ C' M².

The endpoint satisfies

    Psi(M,P union l) + M ≤ Psi(M,P).

Here I_0 and I_2 are the literal interpolated divisor fibres at remaining
labels empty and {2}, evaluated at the initial P. The exact batch identity
transfers their fixed-source sums to the changing core P union L.
All prescribed primes and helpers are fresh; prescribed relative order
is retained. No source window is assumed untouched after an insertion.

For all sufficiently large N, the simpler fixed-fraction condition

    2(K+1)|t| ≤ Q−1

implies the displayed total-capacity condition. The threshold is uniform
in P and t. This discharges the frozen fixed-fraction target.

## Obstacle removed

The earlier prescribed-prime theorem spent O(sqrt M) helper primes on
each prescribed insertion. Repeating it could not process a stream whose
length is comparable to window capacity. The new construction spends K
helpers per prescribed insertion and only one O(sqrt M) reserve payment
for the entire stream. Its cardinality proof includes prescribed primes
that fall inside the helper windows, as well as every consumed helper.

## Dependency-closed paper proof

The existing literal source geometry supplies b and positive c,d. Every
normalized packet v_p = (sqrt(p) I_0, sqrt(p) I_2)/sqrt(M) has product norm
at most B=9. After excluding any set of cardinality below Q−1, the
remaining source contains a packet with z dot v_p ≤ −c ||z|| for every
planar z. Every source packet also contributes at least dM to each of the
two removed-square reserves.

Write r(z)=sqrt(z_1²+z_2²). Since r(z) ≤ 2||z|| and the packet coordinates
are bounded by B, an inward step has

    r(z+v)² − r(z)² ≤ −c r(z) + 2B².

With R=4B²/c+2B+c, the resulting radius satisfies

    r(z+v) ≤ max(R, r(z)−c/4).

For r(z) ≤ 4B²/c+c, use r(z+v) ≤ r(z)+2B ≤ R. Above that threshold,
comparison of squares gives the stated decrease c/4. Repeated fresh
choices therefore satisfy the same bound with k c/4 after k steps.

Choose K with Kc/4 ≥ 2B. A prescribed packet raises radius by at most
2B; K inward helpers return it to the ball r ≤ R. Induct on the prescribed
list, excluding the entire target list before choosing helpers. At each
recursive call also exclude all already used helpers. The union-cardinality
bound is at most K|t|+|t|, so the stated capacity condition preserves a
fresh inward choice. Every stream prefix has radius at most R+2B,
and its endpoint has radius at most R.

Append n=ceil(A sqrt(M)) fresh inward helpers. Their every prefix remains
inside r ≤ R. Including the preceding stream, each physical two-coordinate
L1 displacement D is at most H sqrt(M), with H=2(R+2B). The exact
successor-envelope batch inequality is

    Psi(M,P union L) + min(reserve_0(L), reserve_2(L))
      ≤ E + 2 sqrt(E) D + D²,
    E = Psi(M,P).

All selected primes have quotient at most fourteen and are at least
fifteen; consequently none acts inside any other selected packet's child
cutoff. The fixed child core contains all child primes except two. These
facts justify that exact arithmetic identity at every prefix, despite
the changing processed core.

Nonnegative reserves, E ≤ CM² and D ≤ H sqrt(M) imply the uniform
prefix ceiling with C'=C+2sqrt(C)H+H². At the endpoint the final n source
helpers alone contribute at least dnM to both reserves. Take

    A=(2sqrt(C)H+H²+1)/d.

Since M≥1, this reserve pays 2sqrt(E)D+D²+M, proving the final decrease.

Finally the existing square-root capacity theorem gives eventually
(2A+2)sqrt(M) ≤ Q−1. The ceiling estimate n < A sqrt(M)+1 and sqrt(M)≥1
imply 2n ≤ Q−1. Together with 2(K+1)|t| ≤ Q−1 this proves total capacity.

## Lean surface

Generic finite planar statements:

- `HTGeometry.planeDisplacementRadius_add_le`
- `HTGeometry.planeDisplacementRadius_inward_step`
- `HTGeometry.exists_planeDisplacement_return_batch`
- `HTGeometry.exists_planeDisplacement_restoring_batch`
- `HTGeometry.exists_planeDisplacement_prescribed_stream`

Actual source interfaces exported from the existing window-repair leaf:

- `RHTower.mobiusDivisorTwoPlanePacket`
- `RHTower.norm_mobiusDivisorTwoPlanePacket_le_nine`
- `RHTower.mobiusDivisorCoupledTwoPool_data`
- `RHTower.exists_mobiusDivisorTwoPlaneWindowGeometry`
- `RHTower.mobiusDivisor_two_plane_repair_error_budget`

Actual stream and fixed-fraction theorems:

- `RHTower.exists_mobiusDivisor_prescribed_stream_repair`
- `RHTower.eventually_mobiusDivisor_prescribed_stream_repair`

## Remaining mathematical obligation

This processes an arbitrary bounded-quotient stream within a fixed
fraction of the available windows. It does not supply an exhaustive prime
order from the empty processed core, renew windows indefinitely, or control
several unbounded remaining quotients. Its initial quadratic envelope bound
is an explicit hypothesis, not an RH conclusion. A full proof must connect
these controlled streams through all quotient ranges, retain one uniform
quadratic budget, and land at the complete signed endpoint. The finite
stream theorem alone does not establish those statements.

No route-independent RH law follows beyond the existing ledger entries;
the new information is specific to source supply and finite selection.

## Scientific method and validation

The frozen target was a derived mathematical bridge. No numerical
experiment was appropriate: the relevant estimates follow from the
existing source cone and exact finite transport. No computation, RunPod
job or computed proof certificate was used.

All three new leaves and the source-interface changes passed scratch
checks and exact foreground `lake env lean` emissions. Finished leaves
are wired into HTGeometry and RHTower. No full or umbrella build was run.
All eleven new or newly public theorems were audited once in a temporary
Lean file. Every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound`; no new axiom or computation-backed certificate occurs.

Generated indexes were refreshed. The single
`scripts/formal_tools.py lint --check-generated` run reported three
unrelated concurrent modules unreachable from their umbrellas:
`RHTower.FokasLenellsCauchyResolvent`,
`HTGeometry.FokasLenellsJumpGeometry` and
`HTGeometry.FokasLenellsSingularPhase`. No changed proof leaf or proof-debt
error was reported. Owned-scope whitespace checks passed.

A scoped Lake package audit remains pending: earlier package planning
expanded prohibited broad dependencies, so that planning was not repeated.
Validation here is scratch checking and exact leaf emission with
`lake env lean`, plus the scoped axiom audit. The frontier map was read only.
All six owned temporary files were removed; every owned Lean process exited.
