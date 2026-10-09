# BAG actual reciprocal height decay

- **Stage:** 3-formalized

01ax. Paper and production Lean proof COMPLETE.

Let F be the actual selected normalized Gaussian/logarithmic slice and
W_j(p,q,r)=W^(j)(pq/r)/r^j. For every jet orderj, oneC_j>0 bounds
 (1+|a|)(1+|b|)(1+|D|)*
 |integral_r exp(-iD/r)*conj(F(r))*W_j(p,q,r)/((r+ia)(r+ib))|
for ALL relative widthsdelta in(0,1/2), logarithmic parametersh in[0,1],
physicalp,q in[1,2], and reala,b,D. The full integrand is integrable.
Zero frequencies and zero defect are included. The actual height window,
its full derivative jets, selected cutoff and Gaussian/log slice remain.

Proof: full-line integration by parts on smooth support[1,2] gives the
EXACT identity(1+iD)*I=int exp(-iD/r)*(f-deriv(r²f)). The phase derivative
is needed only on the amplitude support, away fromzero; the multiplied
identity also holds atzero. Norms yield(1+|D|)|I|<=10*(L1f+L1f').
Each complex reciprocal multiplier and its height derivative have uniform
product decay onr>=1. All actual window jets are jointly smooth near the
fixed cube; compactness bounds the jet and its height derivative.
Weighted amplitude and derivative norms are therefore <=4C|F| and
12C|F|+4C|F'|. The alreadyaudited actual mass/firstvariation budgets pay
both integrals. No regularity/variation/cancellation bound is assumed.

Source: ChiCubicReciprocalHeightDecay477lines/API3. Complete actualscratch88281
emptyPASS; production9533emptyPASS; finalaxiom44627all3standard3; index96838
PASS/API3/importonce. Lint89133terminal1: five unrelated unreachable modules
VerticalProgressionCutoffSums,VerticalProgressionLatticeSums,
ReciprocalRecoveryFactorization,ReciprocalWorkFusionRigidity,
ReciprocalWorkWeightedCompactness;362warnings,noownederror. Diff checkPASS.
No resource-limit override, numerical experiment or full/umbrella build.

This closes the actual height-action bound needed after tangential IBP.
The complete P/Q identity and full joint admissions remain open, followed
by weightedCS/Tonelli/U5lowstrip and highfrequency energy. Logarithmic
coordinate/Mellin tails, arithmetic moving signed transfer and the full
sharp-action bridge, growing moments and common-height recurrence remain
hard open. This is not an RH proof.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicReciprocalHeightDecay` | `bagCubicReciprocalHeight_uniform_decay` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
