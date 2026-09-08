# CCM-FU: forced nonempty-energy growth with full-envelope contraction

- Stage: 3-formalized.
- Type: arithmetic local obstruction and sharp positive replacement bound.
- Main module: `MobiusDivisorTransverseDissipationTrap`.
- Source bounds: `DivisorTwentyTwoAnalyticBounds`.
- Boundary: no RH theorem or uniform complete-path bound is claimed.

## Exact arithmetic theorem

At cutoff M=25 let P={2,7,11,13,17,19,23}. Write Q for actual retained
energy, H for its head, V=Q-H², and Psi for the maximum of Q and all
immediate successor energies. Only primes 3 and 5 remain.

`mobiusDivisorTwentyFive_admitted_transverse_trap` proves unconditionally:

1. `Psi(25,P)+1/5 < Q(25,empty)`.
2. For every available prime p, `V(25,P)+1/500 < V(25,P+p)`.
3. For every available prime p, `Psi(25,P+p)+1/250 < Psi(25,P)`.

Thus a state strictly admitted under the original diagonal can have no
nonempty-energy dissipating next step, even while every next complete
successor envelope strictly contracts. The [retired candidate](../5-failed/ccm-fu-dissipative-envelope-extension.md)
required such a step at every admitted state.

## Analytic source proof

Let K_d denote the actual unsigned dilation channel at cutoff 25.
The four nonzero retained coordinates are exactly

`h = K_1-K_2-K_7-K_11-K_13+K_14-K_17-K_19+K_22-K_23`,
`a = -K_3+K_6+K_21`, `b = -K_5+K_10`, `c = K_15`.

The new theorem `divisorUnsignedDilationChannel_twentyFive_profile_boxes`
proves the rational intervals

`-.75≤h≤-.73`, `.007≤a≤.010`, `.013≤b≤.015`, `.173≤c≤.175`.

The proof expands the finite defining divisor channels and propagates
analytic logarithm, square-root and Euler-constant bounds. Logarithm
bounds use the positive remainder of the existing ratio series;
square-root bounds use rational square inequalities. The Euler-constant
bounds come from the established harmonic-sum remainder estimate.
No numerical certificate is imported. The second new source theorem,
`sum_divisorUnsignedDilationChannel_twentyFive_sq_lower`, proves the
original diagonal is at least 4/5 from its squarefree contributions.

Exact retained-field merger identities give

`Q(P)=h²+a²+b²+c²`,
`Q(P+3)=(h+a)²+(b+c)²`,
`Q(P+5)=(h+b)²+(a+c)²`,
`Q(P+3+5)=(h+a+b+c)²`.

Consequently the V gains are 2bc-a² and 2ac-b², whereas the Q gains
are 2ha+2bc and 2hb+2ac. Rational interval arithmetic proves both
V gains exceed 1/500 and both Q gains are less than -1/250. The final
mergers also lower Q, since h+a and h+b are negative while b+c and
a+c are positive. Hence each of the three relevant envelopes equals
its current Q. Finally Q(P)<3/5 and Q(empty)≥4/5 give strict admission
with margin 1/5. This proves the stated theorem and exhibits payment
by head-square contraction in both complete remaining orders.

## Sharp positive replacement

`min_twoCoordinateNonemptyEnergy_le` proves, for all real a,b,c,

`min((a+c)^2,(b+c)^2) ≤ (3/2)(a²+b²+c²)`.

If a²≤b², subtracting (a+c)² from the right side leaves at least
`(2a-c)²/2`; the other case is symmetric. No sign restriction is needed.
Taking a=b=1 and c=2 gives equality. Accordingly
`twoCoordinateNonemptyEnergy_factor_iff` proves that a factor K works
uniformly for all three coordinates exactly when K≥3/2.

This is a sharp bound on possible forced growth in one two-coordinate
step. It does not bound accumulation along an unbounded number of steps.
The actual arithmetic proof exposes a stronger surviving mechanism:
signed coupling with the head can pay that growth while decreasing the
full energy. A uniform estimate controlling this exchange remains open.

## Validation

Scratch checks and exact foreground `lake env lean` emissions passed for
both changed leaves. All five new public theorems were axiom-audited once
in a temporary file; each uses only `propext`, `Classical.choice` and
`Quot.sound`. No old theorem was re-audited. The new module is wired into
RHTower; no umbrella or full build ran. The finite experiment ran only
on RunPod, and its owned workers and remote files were cleaned up.

Generated indexes were refreshed; `scripts/formal_tools.py lint --check-generated`
passed with existing large-file warnings. Owned-scope whitespace checks
passed. All five owned scratch files were removed, and every owned Lean
process reached terminal exit.

A scoped Lake package audit remains pending: its previously observed
dependency planning required a broad rebuild prohibited by the current
build constraints. That planning was not repeated. The frontier map
remained read only.
