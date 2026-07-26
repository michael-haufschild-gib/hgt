# Prop-interface discharge audit: HTGeometry, HilbertMetric, RHTower

- **ID:** prop-interface-discharge-audit
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** loop mandate — audit the three owned areas for undischarged hypotheses / `Prop` interfaces
- **Statement:** every `Prop` interface consumed as a hypothesis in `HTGeometry`, `HilbertMetric`,
  `RHTower` is either (a) produced by an unconditional or corpus-discharged theorem, (b) proved
  unsatisfiable with an exact obstruction plus a satisfiable structural replacement, or (c) recorded
  as a genuinely open analytic input with its named open core.

## Goal
Remove silent conditionality from the three owned theorem areas.  A `Prop` interface that no
theorem in the corpus ever concludes is either an undischarged premise (recoverable) or a vacuous
one (fatal to every consumer).  Both cases must be resolved explicitly.

## Audit instrument (reproducible)
A Lean metaprogram over the whole environment, not a text grep.  For every project theorem it
records the head symbol of each `Prop`-valued binder and of the conclusion, using a
**non-reducing** `forallTelescope` (a reducing telescope unfolds a `Prop` def in the conclusion and
loses the producer, which is why index/grep searches under-report producers).

- script: `scratchpad/AuditAll.lean` pattern — import `GaloisForLFunctions.MainTheorems`,
  `forallTelescope`, emit `module|theorem|propHypHeads|conclHead`, plus every project
  `Prop`-valued `def`/`inductive`.
- corpus size measured 2026-07-26: 71 232 project theorems, 1 721 project `Prop`-valued
  definitions.
- result: **258** project `Prop` interfaces are consumed as a hypothesis inside the three areas and
  concluded by **no** theorem anywhere in the corpus.  Ranked worklist:
  `prop-interface-discharge-worklist.md` (next to this card).

## Worklist status
- HilbertMetric full-CCR layer (`IsFullCCRMatrixTuple`, `IsCommutingFullTuple`,
  `IsInvariantFullCompression`) — **in progress**, see below.
- 255 remaining entries — untouched.

## Finding 1 — the finite full-CCR interface is unsatisfiable
`IsFullCCRMatrixTuple T : ∀ i j, T i * (T j)ᵀ = δᵢⱼ • 1 + (T j)ᵀ * T i` on
`Matrix (n ⊕ m) (n ⊕ m) ℝ`.  Taking `i = j` and the trace, `tr (T Tᵀ) = tr (Tᵀ T)` forces
`tr (1) = 0`, i.e. `Fintype.card (n ⊕ m) = 0`.  So for `Nonempty I` the interface holds only on the
empty space: every `CCRPowerConcavity` theorem carrying it is vacuous in positive dimension.
This is the finite-dimensional CCR obstruction (Wintner/Wielandt) in exact matrix form.

## Structural replacement (satisfiable, keeps every downstream theorem)
The proofs only ever read the relation on the **upper-left block**.  Replace by
`IsBlockCCRMatrixTuple T : ∀ i j a b, (T i * (T j)ᵀ) (inl a) (inl b) = (δᵢⱼ • 1 + (T j)ᵀ * T i) (inl a) (inl b)`.
Then, under `IsInvariantFullCompression T`:
`IsBlockCCRMatrixTuple T ↔ IsCCRCompletion (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)`,
and `IsFullCCRMatrixTuple T → IsBlockCCRMatrixTuple T`, so the existing statements are corollaries.
Non-vacuity is then inherited from the already-proved Gaussian coherent completion
(`GaussianJetPositivity.exists_gaussianCoherentCCRCompletion`,
`gaussianCoherentCompression_commutes`) via `T i = Matrix.fromBlocks (A i) (B i) 0 0`.

## Gates
- [x] 0 → 1  in-progress: audit instrument built, worklist ranked
- [ ] 1 → 2  fully-proven on paper for each worklist entry touched
- [ ] 2 → 3  formalized: Lean module per finding, `lake build` green, lint PASS
- [ ] 3 → 4  n/a (infrastructure card)

## Log
- 2026-07-26 — created in 1-in-progress; audit instrument built; 258 undischarged interfaces found;
  finding 1 (finite full-CCR unsatisfiable) proved on paper with structural replacement.
