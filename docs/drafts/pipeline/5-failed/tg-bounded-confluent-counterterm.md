# TG bounded uncompensated confluent counterterm

- **ID:** TG-C6-BOUNDED-COUNTERTERM
- **Stage:** 5-failed
- **Type:** FALSIFIED candidate, positive survivor formalized
- **Route:** TG

## Candidate and exact obstruction

The complete finite mixed cubic principal coefficient might remain uniformly bounded as
the depth packet grows, allowing a bounded source counterterm before Gamma matching.

`PrimeBurnolCofinalCountertermEscape` disproves that bound at every prime and every grade
with nonzero factor `-visibility*contrast*(visibility²-1/2)`. It also proves the canonical
positive dual synthesis operator's norm tends to infinity. The zero-factor branch is retained
explicitly and concerns only the second-order coefficient.

This retires only the uncompensated bounded-counterterm candidate. TG and joint prime–Gamma
cancellation remain live. The theorem makes no claim about a jointly renormalized operator.

## Positive survivor and second pass

The obstruction exposes exact duality: `Gram(z)=G K^-1 G`, with the dual orthogonal to the
original packet but carrying its radial-jet pairing. Normalizing the ground dual produces
unit vectors converging weakly to zero. Their self-adjoint rank-one projections retain
rank one and norm one while converging strongly to zero.

The second pass strengthened scalar energy divergence to operator-norm divergence and
formalized this source-native escape law. It identifies moving directions that a successful
joint counterleg must control. No new invariant charge is asserted solely from rank one.

Dependency-closed paper proof and successful direct production Lean audit are recorded in
`../3-formalized/tg-confluent-cofinal-counterterm-escape.md`. The separate axiom audit checks
all 25 public theorems, each using only `propext`, `Classical.choice`, and `Quot.sound`.
