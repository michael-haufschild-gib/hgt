# Attempt 9: the GNS socket — RH ⟺ the Weil form is a sum of squares (2026-08-11)

Module `RHTower/GaussHodgeWeilGNSSocket.lean` (wired, built, axiom-clean, 4 theorems).

Audit finding first: the corpus already owned the complete positivity criterion
(`XiWeilPositivityCriterion.lean`: `riemannHypothesis_iff_xiWeilPolarization_nonneg`, with the
off-real sign test as converse witness) — nothing rebuilt.

New keystones:
- `XiWeilSquareRealization : Prop` — ∃ g : (ℂ→ℂ) → XiZeroCopy → ℝ such that for every
  square-summable F, HasSum (g F ·)² (Re (xiWeilPolarization F F)) — the coordinate form of a
  GNS/compressed-trace realization.
- `riemannHypothesis_iff_xiWeilSquareRealization`: **RH ⟺ the diagonal Weil form is a sum of
  squares.** (Forward: tautological realization g F q = ‖F(α_q)‖ via the RH diagonal law;
  backward: sums of squares are nonneg + the criterion.)
- `xiWeilSquareRealization_iff_gaussHodgeMass_vanishing`: square realization ⟺ H-mass ≡ 0 —
  Gate II lands on the loop.

Programme state: 49 new theorems this session across 7 modules
(HyperbolicBounds append, SeamEnergyBridge, CoherenceBudget, VerticalExtraction,
PencilSourcing, WeilPolarizationFusion, GNSSocket), every one axiom-clean. The entire
remaining content of RH for this programme = construct one square realization of
xiWeilPolarization on square-summable tests. Milestones: (b) CC archimedean compressed
positivity; (c) multi-place extension via label-faithful assembly. Concurrent session note:
`GaussReciprocalCharacterAdmission.lean` (virial normalization of the H-mass) was added to the
lane in parallel — read before extending.
