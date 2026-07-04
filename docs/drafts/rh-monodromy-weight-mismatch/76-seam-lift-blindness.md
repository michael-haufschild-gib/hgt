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

## 5. Executables (a)+(b) DONE: nontrivial positive transfer + certified reader

**(a) Symmetrized exponential-family instance [MEASURED — jerby_instance.py, all
five pre-registered verdicts PASS].** Window at the ζ zero 220.71491883931400337
(the slot whose g₅ partner went off-line), r₀ = 0.15, R = 0.30. Carrier
Φ* = symmetrize(arch·Z) per the Lean `symmetrize`:

- P-J0 PASS with a FLAG: the Euler–Maclaurin family (M=500, J=20) validates at
  max|ζ−Z| = 5.7e−49; the doc 32 §7 Jerby transcription at y = 1 reaches only
  1.2e−3 — NOT exponential-grade at t ≈ 221. Family-agnostic architecture
  unaffected (E–M is finite, Schwarz-real, elementary); but the y=1 reading of
  the Jerby formula goes on the doc 32 §8 promotion-grade re-read list (possible
  causes: transcription incomplete, y=1 outside the regime, larger y needed).
- P-J1/P-J2 PASS: Φ* has EXACTLY ONE on-line zero in the ball, displacement
  1e−50 from the ζ zero (vs 0.36 for g₅); Newton stays on-line (off-line
  component 1.5e−67). The exponential family's matched windows EXIST, as doc 32
  §6 predicted.
- P-J3 PASS: domination q_max = 3.8e−49 — forty-three orders inside the premise.
- **P-J4 PASS: the first NONTRIVIAL positive transfer.** D₁ = D₂ = 1,
  L₁ = L₂ = 1, N₁ = N₂ = 0: every hypothesis of
  `anneal_mod_two_window_relation_of_domination` holds with measured values on
  a window with actual zero content, and the mod-2 relation transfers.

**(b) Certified reader [RIGOROUS — certified_reader.py, python-flint/ARB ball
arithmetic, dps 40; certificate JSON archived].** ALL CERTIFIED:

- C1/C2: ζ and g₅ have NO zeros in the closed ball(1/2+220i, 0.30) — box
  coverings (777 boxes each), certified lower bounds |ζ| ≥ 0.1038, |g₅| ≥ 0.5325.
- C3: |ζ−g₅| < |g₅| on the closed annulus [0.15, 0.30] — adaptive covering
  (3448 boxes; ARB's ζ enclosure radius ≈ 33× box half-side at t≈220 forces
  bisection), certified min margin 1.01e−3. Via the machine-checked
  `completed_domination_iff` this IS the completed-level hdom pointwise.
- C4: interval-Newton certificate for the #136 pair: N(X) ⊂ X on the 1e−8 box
  (offsets 4e−31, 1.2e−28) with g₅′ ≠ 0 on X — EXACTLY ONE SIMPLE zero: the
  first certified t₂/m₂ configuration entry (box, multiplicity 1).
- C5: certified domination-failure witness on window A (lower|ζ−g₅| = 0.2388 >
  upper|g₅| = 0.0245 at a+0.16) — the exceptional mechanism, now rigorous.

Every numerical hypothesis of the Lean capstone is now certifiable by rigorous
ball arithmetic; the zero-free window B instance is certified END TO END
(t₁ = t₂ = ∅, hL trivial, hdom via C3 + the banked bridge). What this opens:
the certificate→Lean ingestion step — a `Prop`-level window-certificate
interface whose fields are exactly C1–C4's outputs (interval bounds as rational
inequalities), letting a Lean instance consume the JSON data as the
configuration hypotheses; and the same certified protocol on the E–M carrier's
window (C3-analogue at q ~ 1e−49 is trivially certifiable) for the nontrivial
certified transfer.
