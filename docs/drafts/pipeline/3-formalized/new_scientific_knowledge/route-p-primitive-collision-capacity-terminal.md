# Route P primitive collision capacity terminal

- **ID:** `route-p-primitive-collision-capacity-terminal`
- **Label:** P-G176
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ENDPOINT CLASSIFICATION
- **RH used:** no
- **Computation used:** no
- **Parent:** `route-p-primitive-collision-subquantum`

## Conjecture audit

P-G175 left a completed coefficient-faithful trace contraction as Route P's sole exterior gate.
After the strict subquantum estimate, one must distinguish the actual pre-divisor arithmetic map
from its scalar trace-capacity consequence.  Define the latter on every finite packet of actual
strict-right Xi multiplicity copies:

```text
trace C(q_1,...,q_N) <= B_P,
```

where `C` is the full P-G173 non-diagonal collision Gram at the copies' centered horizontal
displacements and ordinates, and `B_P` is the complete P-G174 primitive Euler budget.

Conjecture: this capacity law is not an upstream source theorem.  It is exactly equivalent to RH.

## Proof

Lean first constructs the literal target matrix

```text
routePStrictRightZeroCollisionCubicKernelMatrix q
```

and proves its exact trace

```text
Re trace C(q_1,...,q_N)
  = sum_i 115/[864 (Re lambda_i)^3].
```

If RH holds, `XiRightZeroCopy` is empty, so every such finite packet is empty and its target trace
is zero.  Conversely, failure of RH supplies one strict-right multiplicity copy `q`.  Its
displacement satisfies `0<Re lambda_q<1/2`, hence its singleton trace is at least `115/108`.
P-G175 gives `B_P<115/108`, contradicting the capacity law.  Therefore

```text
RoutePPrimitiveCollisionTraceCapacityLaw <-> RiemannHypothesis.
```

No zero ordering, finite-height verification, numerical estimate, or extra axiom enters.

## New knowledge and anti-theatre audit

P-G175 did more than make a future contraction quantitatively strong.  It moved the scalar
trace-capacity statement all the way to the terminal boundary: asking directly for that inequality
is now exactly asking for RH.  Consequently:

1. no abstract trace-class, Schur, Carleson, or interpolation theorem can be recorded as the
   missing Route-P premise if its only content is this capacity inequality;
2. a genuine advance must construct a named pre-zero arithmetic incidence and prove its
   coefficient action before taking traces;
3. generic Lagrange contour interpolation, reflected joint-depth codiagonalization, finite
   clock-jet cyclic traces, and post-divisor positive-sector selection remain invalid substitutes;
4. the surviving object must break the flat reflection gauge before codiagonalization and then
   imply the terminal capacity law as a derived theorem.

This is project-specific endpoint classification.  No claim is made that the elementary logical
form is a new general theorem outside this corpus.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  RoutePPrimitiveCollisionCapacityTerminal.lean
```

Capstones:

- `re_trace_routePStrictRightZeroCollisionCubicKernelMatrix`;
- `routePPrimitiveCollisionTraceCapacityLaw_iff_riemannHypothesis`.

Scratch compilation and the single missing-module build passed.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  Forbidden-token scan is clean.  Umbrella import
is wired without compiling the umbrella.

## Survivor

Construct a literal pre-zero, coefficient-faithful arithmetic incidence that breaks the reflected
vertex gauge before codiagonalization.  Its target trace-capacity consequence must be proved from
the constructed map, never introduced as a premise.  If no such source mechanism survives the
resolved-gauge audit, Route P is terminalized at P-G176 and work must pivot to another independent
source route.
