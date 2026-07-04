# 76 — The Seam Mod-4 Blindness, the hD Discharge, and the Instance Protocol

**Register: SEARCH** (tasks #164–#166; fallout of assembling doc 22 §2 in Lean —
doc 22 §§8–9, AnnealWindowRelation.lean). One structural discovery, one discharge,
one measurement protocol.

## 1. The discovery [PROVED-adjacent: forced by banked theorems]

Assembling the mod-2 window relation exposed a typing fact the prose of doc 22 §2
glossed: the seam input hL needs **L mod 4** at k = 1, but the k = 1 seam datum —
the (K1) sign product, the only seam boundary reading the dictionary owns — pins
only **L mod 2**. And the mod-4 lift is PROVABLY not a boundary-transport
statement: `deckClass_blind_to_split` (DictionarySign, #131) shows level-2
boundary data cannot distinguish an on-line double zero from an off-line pair —
precisely the move that changes L by 2 (and N by 1) at fixed D. No refinement of
level-2 boundary dictionary can close this; it is a structural blindness, not a
missing lemma.

Consequence — **the work re-types**: the remaining input of the reduction is not
more boundary dictionary but *per-window certified zero data of the truncation*.
The finite side's zeros are computable objects; an instance run discharges hL
directly as a configuration congruence (Σ on-line multiplicities mod 4), which is
strictly stronger than any boundary reading and available only because the
carrier is finite. Constraint-not-flow, again: the boundary fixes what it fixes;
the rest is read off the computable bulk of the finite object.

## 2. The hD discharge [Lean, banked]

The deck-side input needed no dictionary at all: the banked Rouché substitute
(`enclosed_count_eq_of_close`, #128) already gives EXACT equality of enclosed
counts under slit-annulus domination. Banked in AnnealWindowRelation.lean:

- `anneal_D_transport` — peeled ξ and completedGN on a window ball, zeros in the
  hole, domination on chartRA ∪ chartLA ⟹ **D_ξ(W) = D_g(W)** (equality, all
  moduli at once).
- `anneal_mod_two_window_relation_of_domination` — the maximally discharged
  capstone: strip window + factorizations + domination + hL (mod 4) ⟹
  N_ξ(W) ≡ N_g(W) (mod 2). **hD is gone as a hypothesis.** The analytic inputs
  are now: the peeling data (certified zeros), domination on the charts, and hL.

## 3. The instance protocol (executable (ii); pre-registered)

`computations/mwm/window_instance_136.py` (predictions P-W0…P-W4 in the header,
written before the run): two line-centered windows at the #136 height,

- **Window A (exceptional)**: contains g₅'s off-line pair (ρ ≈ 0.6094 + 221.079i).
  Here N₂ = 1, N₁ = 0 — the parities genuinely differ, so by the CONTRAPOSITIVE
  of the machine-checked capstone the premises cannot all hold. Pre-registered
  mechanism: domination fails on A's charts (doc 22 §3's exceptional mechanism).
- **Window B (generic)**: nearest ζ-zero center below 220.8; predicted q_max < 1,
  D₁ = D₂, L₁ = L₂, N₁ = N₂ = 0 — the relation transfers end to end.

The run doubles as the first live test of the assembled theorem against ζ data:
window A exercises the contrapositive (the theorem FORCES a visible failure in
its premises), window B the positive transfer. Results: §4.

## 4. Instance results [MEASURED — window_instance_136.py, dps 60, archived .out]

All pre-registered verdicts bind; one correction and one sharp new datum.

- **P-W0 PASS.** The #136 pair re-confirmed at raw scale: |g₅(ρ)| = 3.7e−60,
  |g₅′(ρ)| = 0.428 (simple). ρ = 0.60941068066066512… + 221.07888411131592…i.
- **P-W3 PASS (contrapositive, mechanism as predicted).** Window A (pair in the
  hole): D₁ = 0 ≠ D₂ = 2, N-parities differ — and domination fails decisively,
  q_max = 9.76 at the inner circle in the θ = 0 direction (straight at the pair).
  The machine-checked capstone FORCES a premise failure; the data shows which and
  where.
- **The displacement map (new datum).** Root-finds of g₅ seeded at the three ζ
  zeros in [219.0, 221.8]:
  - 219.0676 → g₅ zero ON-line at 218.9988 (pure t-displacement −0.069; corrects
    §3's first-pass "no on-line zeros in the band" — it sat 0.0012 below the scan).
  - 220.7149 → the off-line pair member 0.6094 + 221.0788i.
  - 221.4307 → the SAME pair member.
  **The #136 off-line pair is the merger of exactly the two consecutive on-line
  slots flanking it**: L_ζ = 2 vs L_g = 0 locally — the (K1)-blind move
  (ΔL = 2, ΔN = 1, D conserved) realized by actual ζ/g₅ data. §1's structural
  blindness is not hypothetical; it is instantiated at the first off-line pair
  the lane ever certified.
- **P-W1/P-W2 PASS (zero-free control).** Window B (a = 1/2 + 220.0i): q_max =
  0.287 (inside doc 22 §3's measured band), all six counts zero, relation
  transfers. First end-to-end instance where EVERY premise of
  `anneal_mod_two_window_relation_of_domination` holds with measured domination
  and the conclusion is verified on ζ data. (Counts trivial; the content is the
  premise stack holding together.)
- **Finding (replaces the matched-pair control).** At N = 5, t ≈ 221,
  truncation-zero displacements are 0.07–0.36 and consecutive slots merge into
  off-line pairs: matched-pair windows — nontrivial positive instances — do NOT
  exist at this crudeness. They live where doc 32 §6 already moved the theorem
  track: the exponential-AFE family, whose displacement is e^{−ωt}-small. The
  measured map is an independent, instrument-level confirmation of that family
  switch.

What this opened: the script is the prototype certified reader — its zero data
IS the hL certificate. Next objects: (a) run the same protocol on a symmetrized
Jerby-family instance (matched windows should exist and give the first
NONTRIVIAL positive transfer); (b) interval-arithmetic hardening of the reader
(sign-change counts and q_max bounds as certified inequalities) so the window
data can cross into Lean as configuration hypotheses.
