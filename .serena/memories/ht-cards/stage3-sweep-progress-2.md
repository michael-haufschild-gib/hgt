# ht/ sweep, checkpoint 2 (2026-08-13, after card 1 promotion)

## Card 1 triptic-kummer: ✅ PROMOTED to 3-formalized (see mem:ht-cards/stage3-sweep-2026-08-13).

## Card 4 first-order tail: deck fixed fields ALL DONE (new this checkpoint)
Built, wired, axiom-clean:
- `RootOfUnityScalingFixedField.lean` — invariant field of exact-order-n scaling on free rank-1
  differential field = C⟨vⁿ⟩ (both directions + equality). KEY TRICK: collapse the adjunction over
  the velocity field via `IntermediateField.extendScalars` + `adjoin_le_iff`, NOT adjoin_induction
  (which explodes).
- `TranslationRotationDeckFixedField.lean` — compact signatures: Fix(t₁) ∩ Fix(ρ_ζ) = C⟨(q′)ⁿ⟩.
  Uses `fixedField_zpowers_scalarDifferentialTranslation_one` (⊥ over F⟨q′⟩ ⟹ membership),
  subfield plumbing letI (Differential ↥L via derivationClosedDifferential, DifferentialAlgebra
  F ↥L manually, CharZero ↥L manually), restricted automorphism ρL as explicit structure,
  ρL = torusScaleEquiv via `tailEquiv_ext`, then RootOfUnityScaling theorem inside ↥L, descent via
  `coe_mem_differentialAdjoin_of_subfield` (adjoin_induction over jet set with differentialJet_coe).
  CRITICAL LESSON: passing implicit palettes as `adjoinLift`-families to the rotation theorem causes
  a whnf defeq EXPLOSION (>6.4M heartbeats). Cure: define v₀ := ⟨q′, mem⟩ explicitly and state
  every hypothesis over (fun _ : Fin 1 ↦ v₀); then 1M heartbeats suffices.
  Also `setOf_forall_fixed_eq_differentialAdjoin_derivPow` — arbitrary deck family (tower form).
- `DihedralInversionFixedField.lean` — (2,2,∞): inversionAutomorphism (w ↦ w⁻¹ via
  differentialIndependentTopAlgEquiv), negates current; Fix(all scalings)∩Fix(ι) = C⟨(w′/w)²⟩ via
  rank-1 rotation theorem with ζ = −1 (orderOf via orderOf_eq_prime; −1≠1 via linear_combination,
  NOT linarith — F unordered). Tower form too.
Card 4's md updated with a Lean-progress section (still in 2-fully-proven).

## REMAINING for cards 3+4 (shared): the elliptic column
Card 4's compact-branch tail-in-protocol-presentation delegates to card 3's isogeny-tail for
elliptic phases. Next work item: elliptic function-field protocol witness —
model: differential field C⟨u⟩ free (cover), phase fields = Fix(Γ_n) with Γ_n = lattice
translations + rotation (DONE = my fixed-field theorems); the *concrete* presentation via
mathlib's `PeriodPair.weierstrassP` (analytic ℘, `Mathlib.Analysis.SpecialFunctions.Elliptic.
Weierstrass`) to inhabit the phase-field/deck-identity package (mirror
`MultiplicativeProtocolWitness.lean` for the elliptic case). This closes card 3's abelian-variety
(dim 1) column AND card 4's protocol-presentation residue simultaneously.
Useful pieces: `WeierstrassPDifferentiallyAlgebraic.lean` (corpus, consumes mathlib ℘),
`EuclideanOrbifoldCurrents.lean` (current identities), `AbelianVarietyIsogenyTail.lean`
(conditional scheme-level bridge — the analytic route can bypass it).

## Build/lint notes
- lint gate currently FAILS on other agents' parked unwired modules
  (NevanlinnaTransferMinimalType, PositiveObserverCompactResolventLaw) — not mine, do not wire
  others' parked work.
- subst can eliminate the WRONG variable (theorem binder) — use `rw [hu]` instead after
  mem_singleton_iff.
- `(e)′` with expected type T coerces INSIDE: pin subtype derivs with double ascription
  `(((x)′ : ↥L) : T)`.
- mathlib: `Differential.deriv.leibniz_pow/leibniz_inv/leibniz`, `orderOf_dvd_iff_zpow_eq_one`,
  `Units.val_zpow_eq_zpow_val`, `IntermediateField.extendScalars`, `Set.range_const`.
