# Off-line zeros force cofinal negative actual-clock response

- **ID:** LI-CLOCK-OFF-LINE-NEGATIVE-RESPONSE
- **Stage:** 3-formalized; independent hostile paper and interface audits PASS; 17 public declarations final
- **Type:** THEOREM; literal actual-source signed consequence
- **Parent:** [finite eta orientation window](../1-in-progress/li-clock-finite-eta-orientation-window.md)

## Exact survivor

Under not-RH, there exist b>0, a finite nonempty packet Q containing every multiplicity copy with maximal |Im(w_q)|=b, a strict complement bound 0<=b2<b, and clocks t_j->infinity such that

`exp(-b*t_j)*F(t_j) -> -b*card(Q)/2 < 0`.

Consequently F(t_j)->-infinity, and eventual nonnegativity of literal F implies RH. Combined with exact growing finite-eta approximation, eventual finite-prefix nonnegativity throughout one admissible window `0<t<=c log(2N+1)` implies RH. No converse is established: RH-conditional F(t)/t->0 does not imply F>=0 or exact finite-prefix signs.

## Dependency-closed paper proof

`exists_liEvenCrossActualClockTopPacket_of_not_rh` in `LiEvenCrossActualClockTopFrequency.lean:142` supplies attained b, complete finite ties Q and strict gap b2. `LiEvenCrossActualClockSineSource.lean:125,141` identifies F with the complete multiplicity-copy sine sum, without factor two or pairing quotient. `XiCanonicalProduct.lean:63` gives W=sum_q|w_q|^2<infinity.

For w=a+/-ib, both signs give exact identity

`exp(-bt)*Re(w sin(tw)) = (a sin(at)-b cos(at))/2 + exp(-2bt)*(a sin(at)+b cos(at))/2`.

Installed `exists_simultaneous_phase_recurrence` (`SimultaneousPhaseRecurrence.lean:29`) chooses arbitrarily late clocks with all phases close to1. Its `bohrChar lambda t=exp(-i lambda t)` convention requires frequencies -a for exp(+iat). Accuracy1/(j+1), thresholdj+1 supplies a cofinal sequence whose top normalized sum tends to -b*card(Q)/2. Recurrence infrastructure already exists and must be reused.

For t>=0, the real-segment sine integral and `|cos(uw)|<=exp(u|Imw|)` give `|w sin(tw)|<=t|w|^2 exp(t|Imw|)`. Complement therefore has norm<=W*t*exp(b2*t); normalized bound W*t*exp(-(b-b2)*t)->0. Preserve factor t|w|, both imaginary signs and every multiplicity copy. Omitting it would require false first-power summability. Negative nonzero limit plus exp(bt_j)->infinity proves unbounded negative height.

## Audit and exact formal closure

Producer paper proof and independent current-source audit PASS every clause. Root spotchecked top/gap theorem and read full installed recurrence proof. Search completed with63125-file inventory, older coverage generation1146246/current1146265, unmeasured semantic coverage and mostly pending/stale compiler candidates; no corpus-wide/public novelty claim.

1. Reuse exact finite-phase recurrence; verify APIs in scratch.
2. Disjoint generic complex-sine imaginary exponential envelope and complete complement bound.
3. Disjoint signed finite top-packet sequence/estimate.
4. Root assembles exact literal normalized negative sequence, cofinal unbounded-below receiver and eventual-nonnegative=>RH consequence. Growing finite-prefix implication follows exact approximation, not a converse positivity premise.
5. Named leaf builds, final exact source and all public axiom audits; no RH premise smuggled into independent estimates.

No route retired; this identifies a signed RH receiver, not an arithmetic producer or RH proof.

## Log

- 2026-09-30 — Recorded dependency-closed independently audited theorem before new Lean. Strongest target includes normalized cofinal negative limit and unbounded negative height; no rational-independence assumption or phase erasure. Implementation pending.

- 2026-09-30 — Disjoint exact formal owners assigned after final eta gate: producer `LiClockSineImaginaryEnvelope.lean`; current-source agent `LiClockFiniteTopSinePacket.lean`; root reserves `LiEvenCrossActualClockNegativeResponse.lean` for literal all-copy assembly and eventual-nonnegative receiver, followed by growing finite-prefix sign implication. Agents started scratch before tree writes; root released writes after index/lint terminal. No new theorem is formal yet.

- 2026-09-30 01:27 UTC — Generic finite top packet (2 public declarations) and complete imaginary-gap envelope (8) passed named, final exact and all-public foundation-only axiom checks; umbrella wiring complete. Root literal assembly (4) passed complete scratch, named build and final exact check with empty diagnostics; all-public axiom audit running. Independent final source/interface audit PASS exact subtype split, full-copy cardinality, normalized negative limit, cofinal response to minus infinity, and eventual-nonnegative RH receiver. Growing-prefix window receiver scratch also passed; its named/final gates remain pending. No window sign or RH proof claimed.

- 2026-09-30 01:32 UTC — FINAL: Four leaves: LiClockFiniteTopSinePacket (2), LiClockSineImaginaryEnvelope (8), LiEvenCrossActualClockNegativeResponse (4), LiEvenCrossActualClockPairedEtaWindowReceiver (3). Exact full-copy normalized limit, cofinal response to minus infinity, eventual-nonnegative RH receiver, and explicit growing finite-prefix window-sign receiver are Lean-closed. Window coefficient needs only c>0 for fixed-clock transfer. Window sign itself remains unproved. Every public declaration passed named build, final exact source and axiom audit, with only [propext, Classical.choice, Quot.sound]. Root spot-check complete; umbrella wiring complete. No growing-window source sign, converse, RH proof or route retirement claimed.

- 2026-09-30 01:37 UTC — Index gate exit0 (/tmp/hgt-li-clock-negative-deflation-index.log), four changed indexed sources. Authoritative lint exit1 (/tmp/hgt-li-clock-negative-deflation-lint.log): exactly19 unrelated unreachable modules, no proof-debt errors; all five new leaves wired. Additional external reachability errors since prior15 gate are DeBruijnTopZeroVelocity, WeilDeviationBumps, WeilDeviationFejerTest and WeilDeviationPacketLimit. No whole-tree green claim.
