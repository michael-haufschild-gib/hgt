# 121 — Gate 4 NO-GO: the parity fork, and the forcing criterion

Verdict (verified at theorem level): the RH₂ assembly route via carrier domination is
dead — structurally, not analytically. This doc records the proven diagnosis, extends
it to the docs 117–120 arc, and recuts the open core as a precise structural spec.

## 1. The proven circularity

- `rhLadder_one_of_carrier_domination` (CarrierWeld.lean:177) reduces RH₂ to one
  clause: `Even zs.length` for a split dominating member.
- `exists_split_domination_of_isolating` and its companion identity
  `(analyticOrderAt xi ρ).toNat = zs.length` prove ANY split dominating member has
  count equal to the vanishing order. The reduction's own docstring states it: "the
  weld re-expresses the rung with no loss: its entire content is the parity of the
  count." The machinery computes `Even (order)`; it does not force it.

## 2. The fork that kills every forcing candidate in the banked machinery

- **Order-linked but steerable**: the per-edge involution exists iff endpoint
  orientations agree, and the orientations are steerable independent of the deck
  class (`endpoint_orientation_no_go`). No discrete traction.
- **Pinned but order-decoupled**: the whole-loop crossing count is unconditionally
  even (`crossings_fluxPaired_of_loop_closed` — it is `2·winding`), for every order.
  `arcWinding_parity_eq_enclosedOrder` computes `(−1)^order`; computing is not
  forcing.

Reflection gives orbit-size divisibility, never individual evenness. The deck
cocycle computes the parity, never constrains it.

## 3. The same knife applied to docs 117–120 (this lane's newest arc)

Every capstone of the selection-principle/canonical-datum arc sits on one prong of
the same fork:

- Arc dictionary, calibration iff, sign observable
  (`deckClass_reflectedRoot_ne_one_iff`): **equivalences** — re-expressions of the
  parity, the sign observable being the sharpest one. Compute, not force.
- The selection weld's two conclusions reproduce the fork exactly:
  reading reversal (`selection_reversal_steerable`) quantifies over ALL member
  values with no class hypothesis — **pinned but parity-decoupled** (it hits
  class-trivial members identically; `deckClass_sweepRoot` pins the class through
  the sweep). And "ξ supplies a global root along the sweep" is
  gluing-**equivalent** to class = 1 — circular as a forcing input. By the arc's own
  rigidity theorem, no member can supply a non-reversing selection; the weld
  constrains rules, never ξ's parity.
- Consequently the doc-120 roadmap is revised: the count identity and the dyadic
  ascent (level-4 datum) produce further re-expressions — correct machinery, zero
  forcing. The steering-window widening only matters downstream of a forcing.

## 4. What survives

All of it as mathematics: the staircase steering, the arc dictionary, the sweep
discriminator, the gluing criterion, the selection rigidity/reversal/freeze, the
canonical datum and sign observable, the rectangle residue/box count, the whole-loop
closure, the deck cocycle. Axiom-clean, correct, reusable. What died is the claim
that any subset of them adds up to RH₂.

## 5. The forcing criterion — the recut open core

[OPEN CORE] The fork's two prongs are: (a) quantities whose parity IS the order
parity but which are steerable/free; (b) quantities that are structurally pinned but
see only `2·(integer)`, decoupled from the order. In the entire banked machinery no
single invariant lives on both prongs. **A forcing is exactly: one invariant with
two computations — one computation order-linked, the other structurally pinned —
whose agreement is non-vacuous.** That is the lane's founding slogan
("monodromy-weight MISMATCH") stated as a structural spec rather than a metaphor.

Test for every future candidate, before building: which prong does each of its two
computations sit on, and where precisely do they compute the SAME invariant? If one
computation is an equivalence with the parity and the other is `2·winding`-type,
the candidate is dead on arrival — that is Gate 4's fork.
