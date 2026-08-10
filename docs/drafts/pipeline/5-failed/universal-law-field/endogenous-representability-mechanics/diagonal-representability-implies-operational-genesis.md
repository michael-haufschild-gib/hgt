# Diagonal representability birth implies operational law genesis -- failed

- **Stage:** 5-failed
- **Claim killed:** A source-normal anti-diagonal challenge that is not represented by any current
  evaluator row necessarily changes the current space of legal invisible interventions.
- **Verdict:** [FALSIFIED] [REPRESENTABILITY/OPERATIONALITY CONFLATION]
  [POSITIVE FOUR-CHAMBER SURVIVOR] [SURVIVOR LEAN-CERTIFIED]

## Killing example

For the strict-order evaluator on `Fin n`,

\[
 E_n(i,j)=1\iff j<i,
\]

the row-profile reporter `i -> E_n(i,-)` is injective. Therefore its only invisible intervention is
the identity. Every additional reporter is operationally determined by that row profile and cannot
contract the invisible-intervention doctrine. Nevertheless the complemented diagonal is not any
existing row, by the diagonal theorem.

Thus a challenge may require a genuinely new representer while adding no current semantic
distinction at all.

## Exact killing mechanism

For an evaluator `E` and challenge `c`, operational novelty is not nonmembership in the row image.
It is failure of fibrewise descent:

\[
 E(x,-)=E(y,-)\quad\text{but}\quad c(x)\ne c(y).
\]

Representability asks whether `c` equals one row. Operationality asks whether `c` splits a fibre of
the complete row-profile reporter. These questions are logically independent.

## Strongest positive survivor

ULF-REE-1 classifies the exact exchange and realizes all four chambers on two-state evaluators:

1. represented and operationally effective;
2. represented and operationally inert;
3. unrepresented and operationally effective;
4. unrepresented and operationally inert.

For the anti-diagonal specifically, effectiveness is equivalent to two identical rows having
different diagonal values. The finite diagonal-genesis tower is unrepresented/inert at every stage.

## New insight

Source-normal representer genesis is insufficient for self-revising mathematics. A feedback loop
must separately prove **semantic transport**: which old-invisible intervention becomes illegal.
Conversely an already represented test can still be operationally new. ERM must therefore retain a
two-axis formation grade rather than identify representation with law birth.

## Status

Positive survivor has a dependency-closed paper proof in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/endogenous-representability-mechanics/representation-operational-novelty-four-chamber-and-diagonal-inertness-law.md`.
It is Lean-certified by
`GaloisForLFunctions.HTGeometry.ConstitutiveRepresentationExecutionExchange` and wired into the
Universal Law Field umbrella.
