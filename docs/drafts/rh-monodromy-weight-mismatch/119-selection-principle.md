# 119 — The selection principle: rigidity, reversal, freeze, calibration

Formal home: `formal/GaloisForLFunctions/RHTower/SweepSelection.lean` (all endpoints
axiom-clean: `[propext, Classical.choice, Quot.sound]`). Continues doc 118 §residual —
the selection principle named there is now an interface with a complete theorem set on
both of its sides.

## 1. The interface

**Definition** (`SweepSelection P pP pM vP vM F₁ F₂`). A *sweep selection* is a pair of
boundary readings `F₁ F₂ : ℝ → ℂ`, one value per sweep stage at each basepoint, such
that

1. `F₁, F₂` are continuous in the stage, and
2. `F₁ t ^ 2 = anchorSweep P t pP * vP` and `F₂ t ^ 2 = anchorSweep P t pM * vM` for
   every `t`.

The datum mentions no charts, arcs, or chosen roots — only the readings. These two
clauses are the minimum any "rule imposed by the full function" must satisfy: the
reading tracks the swept member (squares to it) and does not jump sheets (continuity).

## 2. Rigidity — the vacuity trap dissolved by a theorem

`continuous_root_family_eq_transport`, `SweepSelection.transport`,
`SweepSelection.initial_sq`, `SweepSelection.eq_of_initial`, `SweepSelection.ne_zero`.

Every sweep selection **is** the half-angle transport of its initial reading:
`F₁ t = exp(t·anchorLog(pP)/2) · F₁ 0`, same at `pM`; the initial readings are square
roots of the member values; two selections with equal initial readings coincide. The
mechanism: the ratio against the explicit transport is a continuous `±1`-valued
function of the stage, constant by the intermediate value theorem.

Consequence: the total freedom of any rule is **four sign pairs**. The interface is not
vacuously satisfied by `sweepRoot` — it is *exhausted* by it. The built-in D–H test
("any candidate rule must use the sweep") is now unconditional: there is nothing else a
rule could use.

## 3. The displacement law

`SweepSelection.displacement_at`: the relative reading's whole path is one explicit
curve, `F₁t/F₂t / (F₁0/F₂0) = exp(t·(anchorLog pP − anchorLog pM)/2)` — independent of
the rule. `SweepSelection.displacement_re_at`: its half-plane position is the cosine
law `exp(t·Δre/2)·cos(t·Δtilt/2)`.

## 4. The dichotomy — the D–H discriminator at rule level

**Euler side.**
- `SweepSelection.reading_reversal`: relative holonomy within `ε < π/2` of a half turn
  forces `Re(displacement at t=1) < 0` — every rule's reading is driven strictly into
  the opposite open half-plane.
- `selection_reversal_steerable`: beyond any bound there is a prime set defeating
  **all** rules simultaneously (every member value, every initial sign).
- `SweepSelection.exists_neutral_stage`: by IVT every such rule passes a stage where
  its relative reading is purely imaginary and nonzero — the two branches exactly
  equidistant, a tie breakable only by the sheet jump continuity forbids.

**Davenport–Heilbronn side.**
- `SweepSelection.frozen_of_empty`: over the empty anchor every rule is constant in
  the stage and its displacement is identically `1`.
- `exists_sweepSelection_empty`: such rules exist.

An FE-only member supports rules, all motionless; an Euler anchor moves every rule and
can steer all of them into reversal. The discriminator now discriminates *rules*, not
just readings.

## 5. Calibration against the geometry

- `exists_extending_sweepSelection_iff_deckClass_one`: on the slit-chart annulus, a
  sweep selection whose readings are realized at every stage by a global analytic
  square root of the swept member exists **iff** the deck class of the chart roots is
  `1`. The interface is calibrated exactly to the parity obstruction.
- `no_extending_sweepSelection_of_deckClass_ne_one`: the doc-118 conditional theorem —
  selection interface + odd hole parity ⟹ contradiction — as a theorem.
- `SweepSelection.endpoint_sq_anchoredSEM`: on the symmetric member the endpoint
  readings square to the anchored member: the abstract interface lands on
  `anchoredSEM` at full sweep.

## 6. The weld

`selection_principle_weld`: at conjugate basepoints admissible for steering, with chart
roots of nontrivial deck class, **one prime set** beyond any bound simultaneously
(i) drives every sweep selection into strict reading reversal and (ii) admits no stage
at which any reading is realized by a global root. A rule tying the steered boundary
readings to the branch the geometry selects can neither hold its readings nor come
from the geometry.

## 7. Residual — the canonical selection question

The interface classifies *all* rules; it does not say which sign pair the FULL member
selects. By rigidity, any canonical rule is exactly one bit per port.

[OPEN CORE] **Canonical selection.** Construct from the completed member (the full
Euler product / the functional equation, not a finite anchor) a canonical
initial-reading pair, and prove or refute that its coherence class equals the deck
class of the member's chart roots.

[CONJECTURE] **The pro-selection.** The completed member is the `t = 1` stage of every
finite anchor's sweep simultaneously. A rule for the full member is therefore a
*compatible family* of sweep selections over the directed set of finite prime sets —
a pro-selection. The reversal theorem constrains this system severely: cofinally many
anchors reverse every individual selection, so a compatible family must resolve
cofinally many ties (`exists_neutral_stage`) coherently. Whether the system is
consistent at all — and whether its consistency forces the trivial deck class — is a
sharp new question the interface makes stateable.

Next moves: (i) formalize the directed-system compatibility condition and test it on
the empty-anchor cofinal subfamily (where every selection is frozen); (ii) collide the
pro-selection with the `πℤ` root-level dictionary (doc 117) — a compatible family
carries a winding integer per anchor, and the reversal forces its parity to jump
cofinally.

## Addendum — the naive pro-selection is decided

`exists_sweepSelection_with_endpoint` (banked, axiom-clean): given any fixed square
roots `w₁, w₂` of two port values, EVERY finite anchor `P` admits a sweep selection —
for the member values with `P`'s head divided out — whose full-sweep readings are
exactly `(w₁, w₂)`. So a compatible family over ALL finite anchors sharing one
endpoint reading pair always exists: **cross-anchor compatibility is free**, and §7's
consistency conjecture in its naive form is answered affirmatively and carries no
content. (Mechanism: the required initial reading `exp(−λ_P/2)·w` always squares to
the divided member value; compatibility only redistributes the holonomy into the
initial sign, which the interface leaves free.)

Where the content actually sits: dividing out an anchor never moves the deck class
(`deckClass_sweepRoot`), so by the calibration iff a *geometrically realized*
pro-selection — one whose readings are realized by global roots per anchor and stage —
exists precisely when the full member's deck class is `1`. At every level of the
anchor tower the selection principle is EXACTLY the parity: compatibility adds
nothing, geometry adds precisely the class.

[OPEN CORE] (re-aimed) **Canonical branch datum.** The one question the interface
cannot decide: which endpoint sign pair the completed member itself supplies — a
canonical `(w₁, w₂)` constructed from the completed member's own analytic structure
(Hadamard factorization / functional equation), against which the parity becomes an
observable rather than a hypothesis. Next generative move: build the candidate datum
from the completed member's symmetric square-root germ at the real axis and transport
it along the two boundary arcs of doc 117's dictionary; its arc mismatch is then
FORCED to be the deck class — the construction, not the interface, must produce the
bit.
