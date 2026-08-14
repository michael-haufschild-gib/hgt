# Card 6 — the ONE remaining step before promotion (2026-08-14)

Everything else on card 6 is formal and audited axiom-clean (I ran `#print axioms` on all of
`iInter_powAdjoin_eq_logDerivField`, `weight_quantization`, `eq_zero_of_expanding_degree_law`,
`eventually_eq_zero_of_expanding_bound`, `parabolicSphereSignature_of_pole_orders`,
`parabolicSphereSignature_iff`, `hyperbolic_signature_gap`, `parabolic_signature_classification`,
`symbolDegree_const_of_protocol`, `symbol_comparison`, `logDeriv_sq_eq_chebyshev_current`,
`weierstrass_{square,cubic,quartic,sextic}_current`,
`setOf_scaling_inversion_invariant_eq_differentialAdjoin_sqCurrent`,
`setOf_translation_rotation_invariant_eq_differentialAdjoin_derivPow`,
`setOf_forall_fixed_eq_differentialAdjoin_derivPow`,
plus the new `setOf_deck_rotation_invariant_eq_differentialAdjoin_jetPow` — ALL CLEAN).

## MISSING: the phase-tail-equals-deck-fixed-field step UPSTAIRS
`exists_mem_ellipticSubfield_planeScale_iff` is the depthwise deck identity DOWNSTAIRS (in
`MeromorphicPlane`). The card wants the phase TAIL (an intersection of protocol images) to equal the
deck fixed field ON THE REPARAMETRISED CARRIER. Build `HTGeometry/EllipticPhaseTailReparam.lean`:

1. `baseAdjoinJets (S : IntermediateField ℂ MeromorphicPlane) : IntermediateField ℂ (ReparamField MeromorphicPlane)`
   `:= IntermediateField.adjoin ℂ ((algebraMap MeromorphicPlane (ReparamField MeromorphicPlane)) '' S ∪ Set.range ReparamField.jet)`
   — the phase field: the elliptic functions of the phase together with the reparametrisation jets.
2. `velocityField ≤ baseAdjoinJets S` (jets are among the generators;
   `velocityField_eq_adjoin_range_jet` + `IntermediateField.adjoin.mono`).
3. If every `e ∈ G` fixes `S` pointwise then `ReparamField.fieldEquiv e` fixes `baseAdjoinJets S`
   pointwise: the fixed set is an intermediate field containing both generator sets
   (use `IntermediateField.adjoin_le_iff`).
4. IMAGE: `IntermediateField.map (twistAlgEquiv m) (baseAdjoinJets S) = baseAdjoinJets (planeScale m '' S)`
   via mathlib `IntermediateField.adjoin_map` plus: the image of `Set.range jet` is
   `constPlane m • Set.range jet`, and adjoining that gives the same field because `constPlane m` is
   a nonzero constant.
5. Combine with `exists_mem_ellipticSubfield_planeScale_iff` (which computes
   `planeScale m '' (ellipticSubfield Λ)` as the fixed field of the `m`-division points) and with
   `deckInvariantField_eq_velocityField` / `setOf_deck_rotation_invariant_eq_differentialAdjoin_jetPow`:
   `⋂ n, IntermediateField.map (Φ n) (baseAdjoinJets (ellipticSubfield Λ)) = velocityField`
   (and with the rotation, `= differentialAdjoin ℂ {jet 0 ^ n}`).

## THEN promote card 6
git-mv to `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ht/`, set `Stage: 3-formalized`,
add a companion `…-formalized.md` with the module list + theorem chain + verification block, fix
relative links, add a Formalized-companion pointer. Follow the already-promoted
`triptic-ht-kummer` card (see `mem:ht-cards/stage3-sweep-2026-08-13`).
