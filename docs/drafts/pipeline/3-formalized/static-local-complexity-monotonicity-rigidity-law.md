# Static-local complexity monotonicity rigidity law

- **ID:** static-local-complexity-monotonicity-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4) / BRIDGE / NO-GO CLOSURE
- **Status:** `[FORMALIZED] [UNCONDITIONAL] [NOT A PRIORITY CLAIM]`
- **Parent:** `inverse-power-nested-static-local-ramp-return-law.md`

## Exact claims

For the nested inverse-power nearest-neighbour chain, fixed operator-norm resolution
`0 < ε ≤ 1/100`, return period `R_L=2π(L!)^4`, and every laboratory-ramp time

\[
1024\pi ε\le t\le εL/2,
\]

the actual infimal two-qubit-gate complexity satisfies

\[
C^{\rm op}_{L,ε}(0)=C^{\rm op}_{L,ε}(R_L)=0
<C^{\rm op}_{L,ε}(t).
\]

Consequently its restriction to `[0,R_L]` is neither nondecreasing nor nonincreasing. More
sharply, for any ordered codomain with a least element, a nondecreasing function on `[a,b]` whose
right endpoint is least must be identically least; the dual statement holds for a nonincreasing
function whose left endpoint is least. No continuity assumption is used.

For two times `s,t` in the same laboratory window, the actual complexities obey the unconditional
scale-separated comparison

\[
t\ge1024\pi s
\quad\Longrightarrow\quad
C^{\rm op}_{L,ε}(s)\le C^{\rm op}_{L,ε}(t).
\]

This last statement compares the infimal circuit complexities themselves, not only their bounding
envelopes. It does not prove all-pairs monotonicity for arbitrary `s≤t`.

## Paper proof

The empty circuit implements the identity and has zero counted two-qubit gates. Exact return gives
the two endpoint equalities. The ramp lower bound is at least eight because

\[
\frac{t}{128\pi ε}\ge8.
\]

Thus every ramp time has strictly positive complexity. Comparing it to the two zero endpoints
gives a literal rise and a later literal drop. If the history were nondecreasing on the whole
cycle, every intermediate value would be bounded above by its zero right endpoint; if it were
nonincreasing, every intermediate value would be bounded above by its zero left endpoint.

For scale-separated times, the established envelopes give

\[
C^{\rm op}_{L,ε}(s)
\le2\left\lceil\frac{2s}{ε}\right\rceil,
\qquad
\left\lfloor\frac{t}{128\pi ε}\right\rfloor
\le C^{\rm op}_{L,ε}(t).
\]

Since `s/ε≥1` and `t≥1024πs`,

\[
2\left\lceil\frac{2s}{ε}\right\rceil
<\frac{4s}{ε}+2
\le\frac{8s}{ε}
\le\frac{t}{128\pi ε}.
\]

The left side is an integer, so it is at most the floor on the right. Chaining the inequalities
proves the comparison.

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/StaticLocalComplexityMonotonicityRigidityLaw.lean`.

Key declarations:

- `nestedOperatorTwoGateComplexity_return_eq_zero`
- `nestedOperatorTwoGateComplexity_eq_zero_of_cycle_monotone`
- `nestedOperatorTwoGateComplexity_not_monotoneOn_returnCycle`
- `nestedOperatorTwoGateComplexity_not_antitoneOn_returnCycle`
- `nestedOperatorTwoGateComplexity_literal_rise_and_return_drop`
- `nestedOperatorTwoGateComplexity_le_of_scaleSeparated`

Targeted `lake env lean` and targeted module build pass. `#print axioms` for headline declarations
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Project-wide formal lint reports two unrelated pre-existing RHTower umbrella-reachability errors;
this module is umbrella-wired and contains no forbidden declaration.

## Scientific boundary

Brown--Susskind's second-law picture is probabilistic and conjectural for generic dynamics; it is
not a deterministic global monotonicity theorem. Exact recurrence necessarily supplies a later
descent. Present rigidity statement is elementary but removes an ambiguity important for the
paper: a recurrent complexity history can have a certified ramp and actual ordered growth across
large scale separations without being globally monotone.
