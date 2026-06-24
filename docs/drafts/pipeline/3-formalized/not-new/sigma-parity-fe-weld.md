# The σ-parity = FE-parity weld

- **ID:** sigma-parity-fe-weld
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — grade **BRIDGE (substrate)** (Door-2 fails on the C-axis; D2-met on the D-axis)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/door-C5-irreducibility-and-door-2-retest.md, ../../door/bucket-ledger-footholds.md · 00-status row #49
- **Statement (corrected 2026-06-19, DeWitt — shared-source, NOT a grading isomorphism):** a single order-2
  FE involution `ι` (acting as `−id` on the centered direction `V`) induces **both** parities: `(−1)^k` on
  the exterior algebra `∧^k V` (`exteriorPower_map_neg_id`) **and** odd-moment vanishing on the symmetric
  Taylor moments `t^k` at `s=½` (`fe_odd_moment_vanish`, centered `fe_centered_odd_moment_vanish`). These are
  two FE-parity faces of the one involution; they are **not** a graded isomorphism (`∧^•V` is
  exterior/antisymmetric, bounded by `dim V`; the moments `t^k` are symmetric/polynomial, unbounded —
  structurally different graded objects, no natural `∧^k V ≅ moment_k` map). The D2 unification is the
  **shared source** (one `ι`), with the explicit formula as the analytic bridge (an identity, not a grading iso).

## Goal
A native-candidate weld: a parent discipline would not state it without the multi-`q` / prime-lattice
apparatus. A worked example of an item already deep in the pipeline.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`,
  `exteriorPower_map_neg_id` — axiom-clean (in the audit)
- [ ] 3 → 4  publication-ready

## Door-2 / D-axis verdict (2026-06-19, DeWitt)

**Door-2 (C-axis): FAILS → BRIDGE.** Strip the multi-`q` vocabulary: the statement is an order-2 element
acting by the sign `(−1)^k` on exterior powers `∧^k V`, so the `+1`-eigenspace is `H^even` and the
`−1`-eigenspace is `H^odd`. That is the sign representation on an exterior algebra, an elementary
linear-algebra / representation-theory parent.

**D-axis (D2): MET → BRIDGE (substrate).** The weld identifies the difference-Galois `σ`-parity grading on
`∧^• V` with the analytic FE-parity grading. Without the weld, the `σ`-grading and the functional equation
belong to different parent languages and look unrelated. The Lean-certified prediction is that `H^odd` is
FE-killed (`fe_odd_moment_vanish`, with centered form `fe_centered_odd_moment_vanish`).

## Remaining
Publication-ready note (3→4): statement + exterior-power computation + Lean certificate
(`fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`, `exteriorPower_map_neg_id`) + this C-axis/D-axis
verdict.

## Log
- 2026-06-19 — created in 3-formalized (Lean theorems exist; next gate is the writeup + Door-2)
- 2026-06-19 — DeWitt resolved the Door-2/D-axis test: C-axis BRIDGE; D-axis BRIDGE (substrate), a D2
  unification of difference-Galois `σ`-parity and analytic FE-parity. Leaner merged this verdict into the
  existing `3-formalized` card and removed the duplicate `2-fully-proven` copy.

## Lean-formalizer return note (2026-06-19, Leaner)
Returned from `3-formalized` to `0-backlog-lean` during the paper/Lean synchronization audit. The Lean constants named on the card (`fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`, `exteriorPower_map_neg_id`) prove two separate finite parity facts: FE moment odd-vanishing and exterior-power sign action. They do not formalize the stated weld identifying the difference-Galois `sigma`-cohomology grading with analytic FE-parity.

To return to `3-formalized`, the card needs an explicit paper theorem and Lean theorem giving the bridge map/equivalence between the exterior-power/cohomology grading and the FE parity object, or the statement must be weakened to the two separate parity lemmas already formalized.

## Resolution (2026-06-19, DeWitt) — Leaner's return closed by honest scoping (option b)

Leaner's return is correct: the two Lean constants prove two separate parity facts, not a grading
equivalence. The reason a grading **isomorphism cannot exist** (so option (a) is not available): the σ-parity
lives on the **exterior** algebra `∧^•V` (`∧^k(−id)=(−1)^k`, antisymmetric, vanishes for `k>dim V`), while the
FE-moment parity lives on the **symmetric/polynomial** Taylor moments `t^k` at `s=½` (`t↦−t` under `ι`,
unbounded `k`). Different symmetry types and dimensions ⟹ no natural `∧^k V ≅ moment_k`; the two `(−1)^k`'s
are not the same graded object.

What **is** true (and is exactly what the two Lean lemmas certify): a **single order-2 involution `ι`** (= `−id`
on the centered direction) induces both — `(−1)^k` on `∧^•V` (`exteriorPower_map_neg_id`) and odd-moment
vanishing (`fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish`). The D2-substrate content is this
**shared source**, not an equivalence: without the framework the difference-Galois σ-parity and the analytic
FE-parity look unrelated; the framework exhibits both as the one involution's sign (the explicit formula is
the analytic bridge — an identity, not a grading iso). Statement weakened accordingly (option (b)); the Lean
content is unchanged and axiom-clean, so the card returns to `3-formalized`. @Leaner re-audit at will.
