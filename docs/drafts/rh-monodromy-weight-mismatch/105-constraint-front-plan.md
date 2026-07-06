# 105 — The Constraint Front: research plan and work split

**Register: SEARCH** (conjectures labelled; banked Lean cited by file/name).
Companions: `15-conservation-program.md` (FRONT M), `14-parity-stratum.md` (FRONT B),
`104-checkpoint-deadends-and-open-routes.md` Addendum 6 (the pivot verdict this plan executes).

**Reorientation.** The pinning/carrier lane is frozen (104 Add. 6: a flow in disguise — clock,
generative handle, height-indexed quantifiers; its open faces R1/R7 are exactly its flow
content, priced by the wall). All Lean effort redirects to the constraint-native program:
conservation × parity, where the mechanism is discrete (deck classes, parity of flux,
two-coloring) and no quantifier ranges over heights. The frozen lane's instruments transfer:
its load-bearing lemmas are monodromy calculus (πℤ/2πℤ integrality gluing, winding rigidity,
anchored-disc zero budgets, segment-length laws) — the local toolkit for seam accounting.

---

## 1. Inventory — banked, do not re-derive

**Deck spine (FRONT M, complete for piecewise-generic paths).**
- Conservation: `deckClass_step` / `deckClass_chain` / `deckClass_deformation_invariant`
  (DeckHomotopy.lean) — no-flux invariance under dominated deformation.
- Jump: `deckClass_jump` (LedgerJump.lean) — one transversal crossing multiplies the class by
  `exp(2πi·m/n)`. With the above, identity (L) of doc 15 holds on piecewise-generic paths.
- Additivity: `deckClass_multi_zero` (DeckMultiZero.lean). Anchors: `xi_deckClass_far_field`
  (FarFieldAnchor.lean), `analyticOrderAt_even_of_reflection` (ReflectionParity.lean).
- Rung dictionary: `xi_deckClass_eq_one_iff_ladder_dvd` (XiDeck.lean);
  `rh_iff_xiDescent_ne_zero_slitPlane` (UPlaneDescent.lean).

**Seam accounting (partial).** `seam_jump` + `xiDescent_seam_jump` (SeamCocycle.lean — the
local ledger around an on-seam zero, plane and u-plane forms); dominated transport
(SeamTransport.lean); reality/sign transport on the line (SeamSignTransport.lean, in particular
`im_eq_zero_on_line_of_realFE`); rung congruences (SeamCongruence.lean).

**Frozen-lane instruments (route-free; consumable as-is).**
- Winding rigidity + phase lock: `archFactor_line_polar`, `gN_line_winding_rigidity`,
  `carrier_ray_of_sign_ne_zero` (WindingRigidity.lean).
- Argument variation: `borel_caratheodory`, analytic-log-on-discs, πℤ/2πℤ integrality +
  constancy, both segment-length laws (ArgumentVariation.lean) — on-line sign-constant
  stretches are ≤ (π + BC-budget)/windingFloor, i.e. the on-line sign structure has a forced
  `1/log T` oscillation scale.
- Zero budgets: `anchor_jensen_faces_false_of_two_sign_brackets` (AnchorZeroBudget.lean),
  `gN_one_zero_window_of_jensen` (JensenCount.lean), `exists_offzero_subinterval` +
  `anchor_window_margin_scale` (RadiusScaleForcing.lean).

## 2. The target

Doc 15 §4, at k = 1: a simple off-line zero in an upper-quadrant box B forces odd mod-2 flux
through ∂B along an FE-compatible path from an anchored end. The rung follows from

> **(P-flux)** total mod-2 flux through every upper-quadrant box boundary is even,

with the open core itemized as (OC1) band-edge crossing pairing, (OC2) seam crossings,
(OC3) the anchor below σ = 1. Everything else — conservation, additivity, jump, interior
events, far-field drain, central parity — is machine-checked.

## 3. Work packages

### W3 — the ledger reduction theorem (Lean; ARCHITECTURE, runs first)
State (P-flux) ⟹ rung formally at k = 1: a single theorem with the open cells as named `Prop`
interfaces (`BandEdgePairing`, `SeamParity`, `AnchoredEnd`), consuming only banked pieces
(DeckHomotopy + LedgerJump + DeckMultiZero + FarFieldAnchor). This is the constraint-front
analogue of what `riemannHypothesis_of_residual_faces` did for the pinning lane — it fixes the
interfaces every other package fills, and its quantifiers range over boxes and family paths,
never heights. New module `LedgerReduction.lean`. Deliverable: the reduction theorem +
the interface `Prop`s, axiom-clean.

### W1 — the seam-crossing parity functional (Lean; OC2 core)
`[CONJECTURE → lemma chain]` For a box whose bottom edge lies on the critical line, the mod-2
charge absorbed through the seam edge is read off from boundary data: the on-line function is
real (`im_eq_zero_on_line_of_realFE`), so the parity of on-line zeros in the edge segment is
detected by the sign product at the edge's two endpoints (IVT + the banked one-zero window
machinery for localization). Deliverable, new module `SeamParity.lean`:
(a) endpoint-sign functional `seamSign` for an edge segment;
(b) `seam_edge_parity`: sign product negative ⟹ odd on-line zero count parity on the segment
    (and, under a Jensen-type face, exact count 1);
(c) wiring: `seam_jump` × (b) — the seam contribution to a box ledger equals the endpoint-sign
    datum, making (OC2) a boundary-data statement with no clock.

### W2 — crossing rigidity from the frozen-lane instruments (Lean; OC2 quantitative)
`[CONJECTURE]` The seam is never charge-quiet at scale: by the segment-length laws, a seam
edge of length > (π + BC-budget)/windingFloor(T) cannot be sign-constant, so its parity
functional is forced to oscillate at the `1/log T` scale — quantitative structure for (OC2)
consumed per box, homotopy-invariantly. Deliverable, new module `SeamCrossingRigidity.lean`:
the forced-oscillation theorem for seam edges (consumes ArgumentVariation + WindingRigidity +
RadiusScaleForcing read-only; disjoint from W1's file).

### W5 — the u-plane ladder (Lean; OC3 anchoring)
Root existence for the ℤ₂-tower of `xiDescent` on the slit plane beyond star-convex regions
(input: `exists_analyticOnNhd_pow_eq`, UPlaneDescent, banked simply-connected machinery).
Makes the anchored-end statements global instead of per-box (doc 15 §4 OC3(c)). Deliverable:
extension module `UPlaneLadder.lean`.

### W4 — the two-coloring conjecture (research register; OC1, the principal open mathematics)
Formulate the crossing orientation/pairing precisely on the pencil (R3c two-population
asymmetry as the shadow of a transversality two-coloring), then attack-as-false with the
banked box-84 exception as designated counterexample candidate. Pre-register predictions
before touching any computation (anti-theatre gate); measured data already in
`computations/` suffices for the first pass. Deliverable: doc 106 with the precise
`BandEdgePairing` statement (feeding W3's interface) and the attack outcome.

## 4. Work split and protocol

| Package | Owner | Files (disjoint) |
|---|---|---|
| W3 ledger reduction | Fable (this agent) | `RHTower/LedgerReduction.lean` |
| W1 seam parity | Fable (this agent, after W3) | `RHTower/SeamParity.lean` |
| W2 crossing rigidity | helper agent (Lean) | `RHTower/SeamCrossingRigidity.lean` |
| W5 u-plane ladder | helper agent (Lean) | `RHTower/UPlaneLadder.lean` |
| W4 two-coloring | helper agent (research) | `docs/drafts/rh-monodromy-weight-mismatch/106-*.md` |

**Protocol (every Lean package).** Verify mathlib names in `/tmp` scratch first; compile the
module; register in the `RHTower.lean` umbrella; `lake build`; `#print axioms` via `/tmp`
(exactly `[propext, Classical.choice, Quot.sound]`); `python3 ../scripts/formal_tools.py lint`;
one researcher-level entry in `lean_updates_codex.md`; regenerate indexes. Docstrings are
self-contained mathematics — no docs/tasks/dates. Every addition moves a quantifier: no
fixed-value witnesses, no wrapper endpoints. Files < 1500 lines. No git commits (user commits).

**Ordering.** W3 first — it names the interfaces. W1/W2/W5 run in parallel once W3's `Prop`
shapes exist (W2 and W5 can start immediately against doc 15's prose statements and refit).
W4 is continuous and feeds back into W3's `BandEdgePairing` when its statement stabilizes.

## 5. What success opens

W3 + W1 turn the k = 1 rung into: `BandEdgePairing ∧ AnchoredEnd ⟹ RHLadder 1` with the seam
cell discharged — the burden reshaped onto the two remaining named `Prop`s, both discrete.
From there the generative moves are: iterate the ledger up the rungs (k ≥ 2, where the
symmetry discount changes the books), test `BandEdgePairing` against the Beurling coherence
dial (#96), and collide the pairing structure with the parity front's quadrant-ramified cover
(#116) — the two fronts' single shared object.

---

## Status addendum (2026-07-06, same day)

- **W3 DELIVERED** (`LedgerReduction.lean`, axiom-clean): `LedgerChain` (dominated steps +
  signed jumps on annulus charts), `ledgerChain_transport` (class multiplies by exactly
  `exp(2πi·flux/n)` — identity (L) in transport form, jumps freed from `deckClass_jump`'s
  factored-form requirement), `AnchoredLedger` interface,
  `anchoredLedger_deckClass_eq_one`, `xi_deckClass_annulus`, and the capstone
  **`rhLadder_of_anchoredLedgers`**: anchored even-flux ledgers at every off-line zero at
  arbitrarily small radii ⟹ `RHLadder k`. The formal (P-flux) burden is now one named
  clause: `(2^k : ℤ) ∣ flux` inside `AnchoredLedger`.
- **W1 DELIVERED** (`SeamParity.lean`, axiom-clean): `seamSign` + zero-free positivity +
  **`seamSign_one_zero_iff_even`** (0 < seamSign ↔ Even m at a single on-line zero) +
  **`seam_jump_sign_readoff`** (the level-2 seam-jump multiplier (−1)^m read off from the
  endpoint sign product, for any bank roots). (OC2)'s local half is discharged: the mod-2
  seam contribution is boundary data.
- Interface correction vs the original W3 sketch: the honest formal (P-flux) shape today is
  the `AnchoredLedger` divisibility clause, not three separate Props — `BandEdgePairing`
  and `SeamParity` are its suppliers. W1's readoff is the seam-side supplier; W4 must
  produce the band-edge-side pairing that, combined per box path, certifies the flux
  divisibility. W2/W5 unchanged.
- Next objects: (i) a ledger-chain constructor that consumes `seam_jump_sign_readoff` to
  certify a `jump_in`/`jump_out` pair's cancellation from two seamSign evaluations;
  (ii) W4's pairing statement on the pencil (doc 106); (iii) W2's forced-oscillation
  theorem giving the seamSign functional its `1/log T` sampling scale.
