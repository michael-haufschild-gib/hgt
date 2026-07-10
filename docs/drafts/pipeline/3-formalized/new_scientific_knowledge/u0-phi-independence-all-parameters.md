# u0 ⊥ phi_b — All Nonexceptional Quadratic Parameters

- **ID:** u0-phi-independence-all-parameters
- **Stage:** 3-formalized
- **Type:** THEOREM [LEAN]
- **Source cards:**
  - `u0-phi-independence.md` for `b in M \ {0,-2}`
  - `u0-phi-independence-disconnected.md` for `b notin M`
- **Grade:** BRIDGE / native mixed-object theorem

## Statement

For every `b in C` with `b != 0` and `b != -2`, the monomial-fiber Bottcher
`c`-velocity

`u0(z)=sum_{n>=0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`

and the inverse Bottcher coordinate `phi_b(z)` of `f_b(z)=z^2+b` are algebraically
independent over `Qbar(b,z)`.

Equivalently, there is no nonzero polynomial `P in Qbar(b)[z,U,Y]` such that

`P(z,u0(z),phi_b(z))=0`

as germs near infinity.

The excluded parameters are exactly the algebraic Bottcher exceptions in this family:
`b=0` (monomial) and `b=-2` (Chebyshev).

## Proof Assembly

### Connected parameters

For `b in M \ {0,-2}`, see `u0-phi-independence.md`.

The proof uses:

1. `phi_b` extends single-valuedly through the whole basin of infinity `Omega_b`
   because `K_b` is connected and contains the finite critical point.
2. `Omega_b` crosses the unit circle for every `b != 0`; otherwise capacity `1`
   plus connected fullness forces `K_b` to be the closed unit disk, hence `b=0`.
3. The lacunary series for `u0` has the unit circle as a natural boundary by
   Ostrowski-Hadamard.
4. Any positive-degree algebraic relation over `Qbar(b)(z,phi_b)` would continue
   `u0` through a generic crossing point by the algebraic implicit-function theorem.
5. The degree-zero-in-`u0` case would make `phi_b` algebraic over `Qbar(b,z)`,
   forbidden by Becker--Bergweiler for nonexceptional `b`.

### Disconnected parameters

For `b notin M`, see `u0-phi-independence-disconnected.md`.

The only extra issue is that `phi_b` is single-valued on

`Delta_b={G_b>G_b(0)}`

rather than on all of `Omega_b`. The replacement crossing lemma is:

`max_{|z|=1} G_b(z) > G_b(0)`.

Its proof splits into two cases.

1. If `K_b` meets the open unit disk, the Riesz-Jensen formula gives

   `mean_{|z|=1}G_b - G_b(0) = int_{|w|<1} log(1/|w|) dmu_b(w) > 0`.

2. If `K_b` misses the open unit disk, `G_b` is harmonic on the disk and continuous
   on its closure. If `K_b` touches the unit circle, one boundary value is
   `0<G_b(0)`, forcing another boundary value above `G_b(0)` by the mean-value
   property. If `K_b` misses the closed disk, the strong maximum principle gives
   the same strict boundary maximum.

Thus there is `z0` on the unit circle with `z0 in Delta_b`. A path in `Delta_b`
from the infinity germ to a neighborhood of `z0`, avoiding the locally discrete
leading-coefficient and discriminant bad locus, gives the same algebraic-continuation
contradiction with the natural boundary of `u0`.

## Source Boundary

Closest checked sources:

- Nguyen, `Algebraic independence of local conjugacies and related questions in
  polynomial dynamics`, proves algebraic-independence criteria for local conjugacies
  `psi_f` and explicitly states inverse Bottcher-coordinate independence as Question 6.2.
  The present theorem is adjacent to that problem, not covered by it.
- Becker--Bergweiler classify algebraic and differentially algebraic Bottcher functions:
  outside monomial/Chebyshev cases, `phi_b` is not algebraic and is hypertranscendental.
  This kills only the pure `phi_b` side relation.
- The algebraic branch-continuation step is classical algebraic-function theory. The
  source-new part, if no later source-kill appears, is the mixed pair `(u0,phi_b)` and
  the crossing geometry that makes the all-parameter theorem work.

No exact prior result has been found for algebraic independence of the monomial-fiber
Bottcher `c`-velocity `u0` from every nonexceptional quadratic inverse Bottcher coordinate.

## Lean Certificate

The formal statement is

`U0AllNonexceptional.u0_phi_independence_all_nonexceptional_canonical`:

for every `c : ℂ` with `c ≠ 0` and `c ≠ -2`, there is an open, preconnected,
nonempty, infinite carrier `U ⊆ escapeOpen c` on which the actual canonical germ
`Bottcher.phiMero c` and `u0AnSub` satisfy `NoRelation (RatFunc ℂ)`.  This is the
stronger fixed-parameter base field `ℂ(z)`, hence implies the stated
`Qbar(c,z)` conclusion.

The proof is split by parameter topology.

- `U0AllNonexceptional.u0_phi_independence_connected_canonical` uses the
  unconditional global connected Böttcher branch and an aligned escaping radial ray
  to join the canonical far carrier to a unit-circle window.
- `U0AllNonexceptional.u0_phi_independence_disconnected_canonical` proves that the
  escaping critical point is a nondegenerate Green saddle, extracts a first
  unit-circle crossing in `{G_c > G_c(0)}`, and uses the analytic inverse of a
  surjective tower section on a compact Green band.  On the far carrier this inverse
  is literally `bottcherCoord c`, not an auxiliary Kummer root.
- Both cases feed `u0_window_independence_of_transcendental_engine` and the
  unit-circle natural-boundary contradiction.

Formal modules:

- `formal/GaloisForLFunctions/U0/U0AllNonexceptionalConnected.lean`
- `formal/GaloisForLFunctions/U0/U0AllNonexceptionalDisconnected.lean`
- umbrella import: `formal/GaloisForLFunctions/U0.lean`

Verification:

- `lake build GaloisForLFunctions.U0` — PASS
- `scripts/formal_tools.py lint` — PASS
- `#print axioms` for the connected, disconnected, and combined capstones reports
  only `propext`, `Classical.choice`, and `Quot.sound`.

## Significance

This theorem converts the failed `c1 -> 0` descent obstruction in inverse-Bottcher
independence into a positive theorem about a native mixed object. The lacunary
monomial-fiber velocity cannot be finitely algebraically generated from any
nonexceptional quadratic inverse Bottcher coordinate, including disconnected parameters
where the Bottcher domain is constrained by `G_b>G_b(0)`.

In the project vocabulary: the result is not a new algebraic-function theorem; it is a
constraint-side theorem. Finite algebraic dependence would be a continuation machine,
and the source-domain crossing plus natural boundary leaves no crossing-compatible
finite relation.

## Vote State

The connected card had Professor, Haiku, and Wheeler correctness acceptance, with Haiku
and Wheeler explicit novelty/significance votes.

The disconnected card received 4/4 promotion support on 2026-06-24:

- Wheeler: proposed proof and promotion after the Green-crossing lemma.
- Professor: correctness yes and `novel+significant` at bridge grade after repairing
  the boundary-touch case.
- Haiku: correctness yes and `novel+significant` after the repair.
- Turing: correctness yes after independent re-derivation and numerical check; promoted.

## Gates

- [x] 0 -> 1 in-progress: connected/disconnected cases split and proof gaps isolated.
- [x] 1 -> 2 fully-proven: connected proof plus disconnected Green-crossing proof,
  4/4 team vote for the final disconnected gate.
- [x] 2 -> 3 formalized: unconditional canonical theorem compiled, umbrella build
  green, formal lint passed, and axioms checked.
