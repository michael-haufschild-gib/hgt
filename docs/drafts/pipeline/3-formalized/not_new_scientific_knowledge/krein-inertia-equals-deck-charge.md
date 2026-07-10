# Inertia = Charge: the seam Krein index equals the deck ladder charge

- **ID:** krein-inertia-equals-deck-charge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` + formalized, axiom-clean
- **Source:** ../../door/bucket-the-seam-archimedean-obstruction.md, ../../door/G5-unitarity-gatekeeper.md (00-status row: ticket in library-backlog)
- **Statement (delivered):** `[PROVED HERE]` For `k` distinct off-line poles `t_i ∈ ℂ⁺` there is a node configuration on which the FE conjugate-pair seam Krein Gram `factoredKreinForm (seamW) (seamU)` has negative index **exactly `k`** (unconditionally — the surjectivity/Cauchy hypothesis is discharged), and the seam Gram is definite (`KreinNonneg`, a positive polarization) **iff** the deck ladder charge of the configuration vanishes at every rung: `KreinNonneg ↔ ∀ m, wCharge (2^m) (k : ℤ) = 0`. The analytic definiteness face and the 2-adic charge face are one condition, common value `k = 0`.
- **Lean:** `RHTower.seam_inertia_eq_charge`, `RHTower.seamCarrier_exact_inertia`, `RHTower.seamCarrier_kreinNonneg_iff` in `formal/GaloisForLFunctions/RHTower/SeamInertiaCharge.lean`. `#print axioms` = {propext, Classical.choice, Quot.sound}. `lake build` green, lint clean.

## Terminalized verdict on the graded (`mod 2^k`) ambition
The naive graded conjecture `κ₋⁽ᵏ⁾(W) ≡ wCharge_k(W) in ℤ/2^k` for `1 < k < ∞` does **not** refine the way first posited: complex Hermitian inertia is a `ℤ`-valued signature with only a mod-2 reduction — there is no natural `mod 2^k` Krein invariant strictly between parity and vanishing. The genuine content is at the two ends: the exact integer index `κ₋ = k` (which *over*-determines all charges since `k` is the full count) and the definiteness ⟺ all-charges-vanish weld. The 2-adic grading lives entirely on the deck side (`wCharge_tower`); the signature is its mod-2 shadow. This is why the G5 positivity face is all-or-nothing: the Krein index cannot see intermediate 2-adic depth. New content shipped: the exact `κ₋ = #off-line zeros` made **unconditional** for the concrete FE carrier — the "sole remaining arithmetic input" flagged in `KreinLangerInertia`.

## Goal
A graded index identity welding the two proven-but-separate avatars of the off-line count: the
analytic signature (negative Krein index of the FE-forced form) and the 2-adic monodromy (deck/ladder
charge of the root tower). It grades the G5 positivity face by the ladder — Weil positivity stops
being an all-or-nothing inequality and becomes the top of a tower of congruences, each rung
independently attackable — and it gives `compute-omega-h2-gl` its analytic shadow: if the weld class
maps onto the ladder charge (the connecting-map target), Inertia = Charge transports Krein-side
computations into H² computations and back. Native throughout: both sides are constraint-side objects
(a form's index, a descent obstruction); no flow, no spectral-reality search.

## Proven inputs (both sides, this tree)
- Krein side, exact count: `factoredKrein_kreinNonneg_iff`
  (`formal/GaloisForLFunctions/RHTower/SeamSpectralFlow.lean:246`) — the factored FE Krein form is
  definite iff `k = 0`; `exact_neg_inertia` (`formal/GaloisForLFunctions/KreinLangerInertia.lean:603`)
  supplies a negative-definite subspace of dimension exactly `k`, with Cauchy nondegeneracy discharged
  by `cauchy_linearIndependent` (`KreinLangerInertia.lean:629`). The `k = ∞` face is
  `riemannHypothesis_iff_seam_polarization` (`SeamSpectralFlow.lean:141`).
- Deck side, exact count: `windowCertificate_one_iff_even`
  (`formal/GaloisForLFunctions/RHTower/WindowLadder.lean:178`), `rhLadder_one_iff_even_order`
  (`RHTower/WeightMismatchRefutation.lean:128`), `xiDeckCharge_eq_deckChar_ladderCharge`
  (`RHTower/DeckChargeBridge.lean:43`); conservation laws `wCharge_boundary_crossing` and
  `interior_charge_conservation` (`RHTower/DeckChargeCalculus.lean:212, 218`).
- Constraint shape: the reciprocity graph is Lagrangian for the signed Green form (`graph_lagrangian`,
  `RHTower/SeamKreinStructure.lean:107`) and no bounded operator carries the reciprocity
  (`seam_no_bounded_reciprocity_carrier`, `SeamKreinStructure.lean:63`) — so the identity must live at
  the level of forms and indices, not bounded conjugations.

## Door passport
- **Door-1:** both objects are native — the FE-forced signed form whose graph-Lagrangian seam geometry
  is already in-tree, and the ladder charge of the ξ root tower.
- **Door-4:** lives exactly at the seam (archimedean-obstruction bucket); grades the G5 unitarity
  gatekeeper by the 2-adic ladder.
- **Door-2:** proof inputs are in-tree (`KreinLangerInertia`, `DeckChargeCalculus`,
  `SeamSpectralFlow`); no external proof engine imported.

## Approach
1. **Level 1 — the frame weld.** Both sides count the off-line multiset of `W`; the open content is
   welding the counting frames: the Krein count runs through `ℂ⁺` node configurations of the
   conjugate-pair Pick Gram (`conjPairPick`), the deck count through box windows and root descent.
   Target lemma: for `W` with off-line pairs `ρ₁ … ρ_k` (with multiplicity) there is a node
   configuration whose factored Krein form has `κ₋ = k`, and conversely; then
   `κ₋(W) mod 2 = wCharge₁(W)` composes the two proven exact counts. The identity earns content only
   if the Krein side is computable from carrier data without locating zeros — e.g. from the
   `ModulusHolography` circle-average readoffs (`xi_deckClass_eq_circleAverage_slope`) — otherwise it
   is bookkeeping (see attack-as-false).
2. **The graded lift.** Inertia is a ℤ-invariant; the 2-adic grading must come from the tower, not
   from reducing `κ₋` mod `2^k`. Candidate: the level-`k` seam Gram is the Pick Gram of the level-`k`
   descent carrier (the `xiDescent`/`uSqrt` tower), whose negative index sees order mod `2^k`.
   **[OPEN CORE]** existence of the tower carriers.
3. **Mechanism — the dynamic version.** Krein–Gelfand–Lidskii transposed to the seam: eigenvalue
   pairs leave the critical line only through a collision of modes with opposite Krein signature,
   i.e. the charge jumps only at isotropic/degenerate points of the seam pencil. The isotropy algebra
   is in `SeamKreinStructure`; target: the exceptional locus of the seam form carries the rung-1 bit.
   This converts the static identity into a creation-mechanism theorem: no signature collision ⟹ no
   off-line birth ⟹ the rung holds. Constraint-compliant: signature bookkeeping at a pinned
   configuration, no `t → ∞` statistics.

## Attack as false (run first)
- **Tautology risk (level 1).** If the node configuration is chosen *from* the zeros, `κ₋ = k` holds
  by construction and the identity is a re-count, not a bridge. The falsifiable content is
  frame-independence: `κ₋` computed from carrier/window data alone equals the deck charge. If every
  formulation collapses back to "both sides count zeros", the card fails the novelty gate and goes to
  5-failed with that verdict.
- **No-lift risk (level ≥ 2).** If no natural tower carrier exists — if the level-`k` Gram cannot be
  built without choosing roots, i.e. without already trivializing the deck class — the graded
  conjecture retreats to the proven endpoints (level 1 and level ∞). That outcome still terminalizes
  the card: downgrade to the level-1 theorem plus a no-lift no-go.

## Gates
- [x] 0 → 1  in-progress: well-posed (level-1 statement precise), source-pure (both objects native to
  this tree), attack idea (frame weld; signature-collision mechanism), Door passport sketched
- [ ] 1 → 2  fully-proven: the level-1 identity `[PROVED HERE]` frame-independently — or the tautology
  verdict with its no-go
- [ ] 2 → 3  formalized: Lean `krein_inertia_eq_deck_charge_one` (level 1), `lake build` green,
  axiom-clean
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-07 — created in 1-in-progress
