# Card 21 last blocker — PSL₂(ℝ) normalization twist plan (2026-08-13)

Card 21 (`nevanlinna-boundary-bauer-retract-maximal-ht`) audit blockers: (1) MaximalTranslationInputs
term — CLOSED 2026-08-13 (`analyticNevCarrierFamilyMaximalTranslationInputs`); (2) normalization
independence from arbitrary admissible matrix changes.  The card's own §"Independence of the
Nevanlinna normalization" (eqs 14–16) defines a normalization change as right-composition with
`g ∈ PSL₂(ℝ)`: `π' = g∘π`, `μ'_{gτ} = μ_τ`, and independence is the transport (15)-(16) — already
`carrierProjector_eq_of_leaf_label_covariance` (NevanlinnaConstraintProjector.lean:225).

## The honest endpoint to build (task #5)
Module `NevanlinnaNormalizationTwist.lean`:
1. Real det-1 2×2 data g = (p q; r t) (mirror NevanlinnaMatrixData style, or reuse it: a=p b=q c=r d=t).
2. Total Möbius action `mobiusOnePoint g : OnePoint ℝ → OnePoint ℝ`:
   τ ↦ (pτ+q)/(rτ+t) with pole ↦ ∞, ∞ ↦ if r = 0 then ∞ else p/r.
   Laws: `mobius g ∘ mobius (inv g) = id` (inv g = (t, −q; −r, p)), continuity on OnePoint ℝ.
   CHECK FIRST: mathlib/corpus homeomorphism `OnePoint ℝ ≃ₜ ℙ¹ℝ` or an existing Möbius action —
   would give composition law + continuity for free.
3. Matrix twist: A·g entries (ap+br, aq+bt, cp+dr, cq+dt), det 1 ✓.
   Fiber covariance: `finiteDenominatorFiber' σ = finiteDenominatorFiber (mobius g σ)` (+ ∞ cases):
   from c'τ'+d' = c(pτ'+q) + d(rτ'+t).
   Label covariance: `projectiveLabel' = mobius (inv g) ∘ projectiveLabel`.
4. `NevanlinnaBoundaryFamily.twist g`: matrix' = A·g; leaf' σ := leaf (mobius g σ); fields:
   continuity of c',d' ✓; continuous_leaf' = F.continuous_leaf ∘ mobius-continuity;
   carried fields from fiber covariance; moments ✓ unchanged.
5. Endpoint: **`twist_carrierProjector_eq : (F.twist g).carrierProjector = F.carrierProjector`**
   via carrierProjector_eq_of_leaf_label_covariance with e := mobius (inv g)
   (hleaf: (twist).leaf (e t) = F.leaf (mobius g (mobius (inv g) t)) = F.leaf t;
   hlabel: label' = e ∘ label ✓).
Then card 21 re-audit → promote (companion + move), and sweep the other nine moment-fibre cards
(5, 11, 17, 19, 25, 34, 35, 36, 41) against their own numbered statements.

## Context
Bottleneck-1 interface fully closed (see mem: nad/bottleneck1-closed-mriesz-2026-08-13).  Both
capstones (`analyticNevCarrierFamily_maximalTranslationPhase_dense_residual` + full-rank) are
unconditional and axiom-clean.
