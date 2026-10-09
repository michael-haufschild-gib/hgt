# BAG complete masked Mellin source

- **Stage:** 3-formalized

Write E_p for the unlabelled local Euler factor, and a_p,b_p,c_p,d_p for
its first, second, third and coincident-first/second response ratios.
The literal distinguished-prime product has, whenever all E_p are nonzero,
its unlabelled product times c_r*(d_p if p=q, else a_p*b_q). Both p!=r
and q!=r remain. This follows by evaluating every local label pattern;
no independent-label replacement is made.

With w_p=log p/p, the complete response is exactly
T=sum_r w_r*c_r*((sum_(p!=r)w_p*a_p)*(sum_(q!=r)w_q*b_q)
  +sum_(p!=r)w_p^2*(d_p-a_p*b_p)).

Let Arow=sum w*a, Brow=sum w*b, Crow=sum w*c. The unrestricted expansion is
T=Arow*Brow*Crow + Crow*sum w^2*(d-a*b)
  - Arow*sum w^2*b*c - Brow*sum w^2*a*c
  + sum w^3*c*(2*a*b-d).

The proposed coefficient3 in the final term was rejected by symbolic
Lean checking. Two is correct: one contribution comes from multiplying
the two exclusions, one from removing the excluded pair correction. The
corrected exact expansion is the positive survivor and is Lean checked.

For P_N=primes<=N, s=1+u/log N,t=1+v/log N, the previously formalized
joint base product tends to a nonzero exponential. Thus it is eventually
nonzero, and every local E_p is eventually nonzero. The final growing
family has no nonvanishing hypothesis. Eventual positive real parts
allow the exact weightedTrace sum/product formula. Consequently the
original criticalCompletedConeEuler equals its entire unlabelled trace
with both original coprime cofactors, times normalization^3*T.

Scratch45020: empty PASS for all local patterns, the masked assembly,
eventual local nonvanishing, actual cofactor-completed family and corrected
full-row expansion. The growing response row limits and normalized
collision decay remain to be formalized; this is not a labelled joint
limit or a physical axes saving.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanMaskedMellinSource` | `criticalLocalMellinBase_eventually_ne_zero`, `criticalWeightedConeEuler_moving_response`, `criticalCompletedConeEuler_moving_response`, `criticalMaskedMellinResponse_expansion`, `criticalCompletedConeEuler_mixed_response` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
