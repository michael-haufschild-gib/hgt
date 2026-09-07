# CCM-FU: sharp square-root terminal prime ordering

- **Stage:** 3-formalized
- **Type:** unconditional arithmetic support reduction and sharp adaptive terminal ordering
- **Source:** [adaptive original-diagonal ceiling PE4](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** PE4, PE4G, SD1 and RH remain open. This theorem controls a terminal order by its actual endpoints; it supplies neither endpoint's original-diagonal bound.

## Signed scalar ordering

For a real head h, finite signed leaf family c and absorbed subset R of U, retain the exact energy

`E(R)=(h+sum_(p in R)c_p)^2+sum_(p in U\R)c_p^2`.

Absorbing p changes energy by `2*h*c_p`, with h understood as the current head. If an opposite-sign or zero-product leaf remains, choose it; that step contracts energy. If no such leaf remains, every remaining coefficient has the head's strict sign. The remaining scalar energy is bounded by the squared complete sum, and any next leaf is safe below that endpoint. Strong induction on the remaining finite set produces a distinct complete list whose every prefix has energy at most `max(E(empty),E(U))`.

Every complete path contains both endpoints. Hence a complete order below any real ceiling B exists if and only if both endpoint energies are at most B. This is the sharp minimax value, with no coefficient-sign hypothesis and no assumed endpoint bound. The theorem proves existence of an adaptive order; it does not assert that every order or the frozen deterministic greedy policy has this property.

## Literal arithmetic reduction

Let `P_small(M)={p prime : p<M and p*p<M}`. If P contains this set, every active source index d<M has at most one prime factor remaining outside P. Indeed, two distinct remaining primes p,q would have coprime product dividing d. If p<=q, then `M<=p*p<=p*q<=d`; the opposite ordering gives the same contradiction. The strict source support d<M includes the clipped terminal and nonsquarefree zeros through the existing source definition.

Thus every retained label of cardinality greater than one vanishes. Write `h=F_(M,P)(empty)` and `c_p=F_(M,P)({p})` for the actual retained fibres, and let U be all primes below M outside P. Lean proves the exact identities

`Q_(P union R)(M)=(h+sum_(p in R)c_p)^2+sum_(p in U\R)c_p^2`,

`h+sum_(p in U)c_p=S(M)`.

Processing one remaining prime changes only the head and that singleton. No sign is imposed on c_p; the previously proved cofinal orientation reversal is retained. Applying the scalar theorem gives a complete remaining-prime order whose every prefix is bounded by `max(Q_P(M),S(M)^2)`. The canonical choice `P=P_small(M)` yields an unconditional theorem at every cutoff, including empty prime sets.

The exact terminal ceiling criterion is `Q_P(M)<=B and S(M)^2<=B`. In particular, setting B to the original diagonal would still require SD1. Earlier operations with overlapping labels require independent arithmetic control, and reaching this terminal stage under the original ceiling is not proved.

## Lean audit

- `SignedScalarMergeOrder.lean`: one definition and four public theorems, including complete distinct-list witnesses, all-prefix energy control, the exact ceiling equivalence and singleton-support summation.
- `MobiusDivisorSquareRootTerminalOrder.lean`: one definition and ten public theorems, including arithmetic support collapse, exact source/energy identities and the unconditional canonical terminal order.

Both leaves passed scratch checks and foreground `lake env lean <leaf> -o <exact olean>`. All sixteen new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. No numerical premise, added axiom or unproved cancellation assumption enters the results. Both leaves are wired once into `RHTower.lean`; no umbrella or dependency build was run.

The single global lint run reported three unrelated concurrent modules without umbrella imports: `ThetaCuspFactoredReflectionError`, `ThetaCuspSharpFiniteCooling` and `HTGeometry.LogarithmicLaplaceScoreBounds`. Neither new CCM-FU leaf was flagged.
