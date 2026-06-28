# Handoff: current `hRigid` branch of `q62_independence`

This handoff supersedes the old "make a new `Rigidity.lean` file" note.  The hRigid lane has already
created substantial axiom-clean Lean infrastructure.  Do not redo it, and do not replace the remaining
work by axioms, `sorry`, or terminal hypotheses.

## Current verified surface

The main active files are:

- `DendriteBoundary.lean`
  - `nhdsWithin_compl_filledJulia_neBot_of_not_mem_interior`
  - `exists_mem_ball_compl_filledJulia_of_not_mem_interior`
  - `nhdsWithin_compl_filledJulia_neBot_of_mem_emptyInterior`
  - `exists_mem_ball_compl_filledJulia_of_mem_emptyInterior`
- `DendriteContinuesAcross.lean`
  - `not_continuesAcross_of_emptyInterior_modulus`
  - `mem_frontier_of_mem_filledJulia_emptyInterior`
  - `not_continuesAcross_of_emptyInterior_modulus_at_filled`
  - `hnb_of_emptyInterior_modulus`
- `RelativeFibreGeneric.lean`
  - `fibrePoly_eq_denseFibreCoeff`
  - `exists_sparse_fibre_separable_crossing`
  - `exists_commonBasin_input_of_sparse_fibre_crossing`
  - `exists_commonBasin_frontier_input_of_sparse_fibre_crossing`
  - `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior`
  - `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_globalRegion`
  - `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent`
  - `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_carrierClosure`
- `RepellingPeriodicFrontier.lean`
  - repelling periodic points lie on `frontier (filledJulia c)`;
  - strong orbit-product repulsion now implies frontier membership.
- `ConnectedRepellingFibreInput.lean`
  - absolute `φ_c` transcendence from a repelling separable fibre;
  - full-fibre and coefficient-avoidance reductions;
  - selected-denominator reduction;
  - chosen-denominator reduction:
    `phiMero_transcendental_of_repelling_chosen_denominator_input`;
  - composed-relation denominator clearing is now created internally:
    `exists_compRelPoly_denominator_of_minimal`,
    `chosenCompRelDenom`,
    `chosenCompRelQuot`,
    `chosenCompRelDenom_spec`;
  - selected-denominator sparse-crossing reduction:
    `phiMero_transcendental_of_repelling_selected_denominator_crossing_input`;
  - function-field-separable crossing reduction:
    `phiMero_transcendental_of_repelling_fraction_separable_crossing_input`;
  - finite-bad-locus shrinking reduction:
    `phiMero_transcendental_of_repelling_target_accumulation_input` (logically valid, but no longer
    the active final interface because fixed-period accumulation is not the right geometry).
- `PeriodicPointAvoidance.lean`
  - finite counting bricks for choosing a fixed point of `f_c^[p]` outside a finite bad set;
  - two-polynomial and finite-family zero-locus avoidance from `natDegree` bounds.
- `IndexEstimate.lean`
  - exceptional fixed-point index mass estimates:
    `eventually_exceptional_mass_small`;
  - root-bulk smallness bridge:
    `eventually_exceptional_mass_small_roots`;
  - pinned-bulk contradiction with the smallness hypothesis created asymptotically:
    `eventually_false_of_pinned_bulk_repelling`.
- `GreenLogDeriv.lean`
  - rightmost filled-Julia anchor:
    `exists_rightmost_filledJulia`;
  - a rightmost filled-Julia anchor is a Julia-frontier point:
    `rightmost_mem_frontier_filledJulia`;
  - right-half-plane branch constructors now use the named rightmost anchor instead of duplicating the
    compactness maximizer proof.
- `GlobalBasinBranch.lean`
  - half-plane dendrite contradiction with the rightmost anchor chosen internally:
    `false_of_rightmost_halfplane_dendrite`;
  - empty-interior specialization:
    `false_of_rightmost_halfplane_dendrite_emptyInterior`;
  - these consume the existing `false_of_halfplane_dendrite` and remove the caller's explicit
    rightmost-anchor datum from that route.  The empty-interior specialization also creates the
    rightmost frontier fact and local empty-interior ball internally.  The remaining input is the punctured
    basin-sector preconnectedness and fibre nondegeneracy package at the chosen rightmost frontier point.
- `BasinColimit.lean`
  - one-step normalized square-root branch constructor:
    `exists_sqrtLevel_succ_of_simplyConnected`;
  - recursive square-root tower constructor from simply-connected successor levels:
    `exists_sqrt_family_of_simplyConnected_levels`;
  - current square-root branch constructor:
    `exists_global_branch_of_sqrt_family_modulus`;
  - simply-connected-level branch constructor:
    `exists_global_branch_of_simplyConnected_levels_modulus`;
  - coherent square-root recursion creates the `2^n` power law, the nonvanishing global basin branch,
    and the basin-wide Böttcher modulus internally.  The simply-connected-level constructors are useful
    local/over-strong constructors, but the final connected route should prefer the existing global
    branch or monodromy/uniformization route rather than trying to prove exterior escape levels simply
    connected.
- `ConnectedRepellingPeriodicAvoidance.lean`
  - lower finite-point-set absolute `c₂` entry:
    `phiMero_transcendental_of_repelling_fixedPoint_avoidance_input`;
  - intermediate polynomial-family absolute `c₂` entry:
    `phiMero_transcendental_of_repelling_polynomial_bad_locus_input`;
  - squarefree/strong-root counting bricks:
    `squarefreeBadFamily`,
    `separable_specialization_of_avoids_squarefree_bad_locus`,
    `minimal_relation_squarefree_bad_polys_ne_zero`,
    `exists_fixedPointPoly_root_avoiding_squarefreeBadFamily_of_budget`,
    `strongFixedPointRoots`,
    `nonStrongFixedPointRoots`,
    `strongFixedPointRoots_card_add_nonStrongFixedPointRoots_card_eq_roots_card`,
    `squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt`,
    `nonStrongFixedPointRoots_subset_of_strong_off_exceptional`,
    `squarefreeBadDegreeBudget_add_nonStrong_card_lt_of_exceptional`,
    `eval_ne_zero_of_notMem_roots`,
    `squarefreeBadDegreeBudget_add_nonStrong_card_lt_of_exceptional_poly`,
    `squarefreeBadDegreeBudget_empty`,
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_noExtra_input`,
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_chosenDenominator_noExtra_input`,
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_clearedDenominator_noExtra_input`,
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input`,
    `exists_strong_fixedPoint_avoiding_squarefreeBadFamily_of_budget_card`;
  - fixed-point lower-bound bricks for the strong-root pool:
    `strongFixedPointRoots_orbitProduct_at_fixed`,
    `mem_strongFixedPointRoots_of_fixed_pow_norm`,
    `mem_strongFixedPointRoots_of_fixed_norm_gt_two`,
    `strongFixedPointRoots_card_pos_of_fixed_norm_gt_two`,
    `fixedNormGtTwo_finset_subset_strongFixedPointRoots`,
    `fixedNormGtTwo_finset_card_le_strongFixedPointRoots_card`,
    `squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_fixedNormGtTwo_finset`;
  - fixed-point finite-set lower-bound absolute `c₂` entry:
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_fixedNormGtTwo_clearedDenominator_noExtra_input`;
  - current active absolute `c₂` entry:
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input`;
  - finite exceptional-set entry with no extra bad family remains available:
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalSet_noExtra_input`;
  - finite exceptional-set entry with caller-supplied extra bad family remains available:
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalSet_asPoly_input`;
  - direct polynomial exceptional-locus entry remains available:
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalPoly_input`;
  - creator bridge from no extra bad family and a finite exceptional set to the polynomial
    exceptional-locus entry:
    `exceptionalPoly`,
    `exceptionalPoly_ne_zero`,
    `exceptionalPoly_natDegree`,
    `exceptionalPoly_eval_eq_zero_of_mem`,
    `phiMero_transcendental_of_repelling_standard_squarefree_budget_exceptionalSet_noExtra_input`;
  - replaces the unusable accumulating fixed-period target callback and the over-strong
    every-denominator interface by finite polynomial zero-locus avoidance for the denominator Lean
    constructs from minimality.  The active callback now chooses only `p` and proves
    `squarefreeBadDegreeBudget P (chosenCompRelDenom hUo hUne c₂ hU₂ P hP0 hPrel hPmin p) ∅ <
    (strongFixedPointRoots c₂ p).card`.  The denominator identity
    `(Polynomial.C e) * compRelPoly c₂ p P = P * S` is created internally by
    `exists_compRelPoly_denominator_of_minimal`/`chosenCompRelDenom_spec`.  The extra bad family is
    created internally as `∅`; the avoiding target is selected internally from
    `strongFixedPointRoots c₂ p`.  Squarefree bad polynomials create fibre separability internally,
    and the derivative witness is created from the orbit-product multiplier.
- `RelativeRigidityNaturalBoundary.lean`
  - natural-boundary hRigid bridges from `ContinuesAcross` obstruction;
  - empty-interior specialization deriving the obstruction from the Böttcher modulus;
  - local/off-other `γ` endpoints;
  - common-region and common-basin endpoints;
  - level-root tower endpoints;
  - crossing-driven endpoints that create the separable target fibre internally;
  - `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing` now routes through the
    natural-boundary frontier interface, with the frontier payload created internally from empty interior;
  - reduced-geometry global-region endpoint:
    `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_globalRegion`;
  - common-component endpoint:
    `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_commonComponent`;
  - carrier-closure endpoint:
    `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_carrierClosure`;
  - level-root reduced-geometry global-region endpoint:
    `noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing_globalRegion`;
  - square-root-family endpoints now construct the modulus-carrying global basin branches directly via
    `exists_global_branch_of_sqrt_family_modulus`;
  - empty-interior `_repellingG` endpoints now use the current chosen-denominator direct
    strong-root-card `c₂` input:
    `q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable_repellingG`,
    `q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_crossing_repellingG`,
    `q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_repellingG`.
- `RelativeRigidityGlobalBranchCrossing.lean`
  - global-branch crossing endpoint;
  - current strongest global route:
    `q62_independence_connected_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm_autoFrontier_repellingG`;
  - this route now uses the chosen-denominator direct strong-root-card `c₂` input.
- `RelativeRigidityHNBCrossing.lean`
  - abstract natural-boundary crossing endpoints;
  - current strongest HNB repelling-G routes:
    `q62_independence_connected_of_naturalBoundary_commonBasin_level_roots_offOther_crossing_repellingG`,
    `q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_repellingG`;
  - simply-connected-level HNB crossing endpoint:
    `noRelation_phiMero_of_naturalBoundary_commonBasin_simplyConnectedLevels_offOther_crossing`;
  - empty-interior simply-connected-level HNB crossing endpoint:
    `noRelation_phiMero_of_emptyInterior_commonBasin_simplyConnectedLevels_offOther_crossing`;
  - these routes now use the chosen-denominator direct strong-root-card `c₂` input, and the
    simply-connected-level endpoints remove explicit square-root tower data from the natural-boundary
    and empty-interior crossing routes.  The empty-interior version also creates the natural-boundary
    obstruction internally from the Böttcher modulus.

Verification from the current session:

- `lake env lean GaloisForLFunctions/Bottcher/PeriodicPointAvoidance.lean`
- `lake env lean GaloisForLFunctions/Bottcher/ConnectedRepellingPeriodicAvoidance.lean`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityGlobalBranchCrossing.lean`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityHNBCrossing.lean`
- `lake build GaloisForLFunctions.Bottcher.MonodromyObstruction`
- `lake build GaloisForLFunctions.Bottcher.PeriodicPointAvoidance
  GaloisForLFunctions.Bottcher.ConnectedRepellingPeriodicAvoidance
  GaloisForLFunctions.Bottcher.RelativeRigidityGlobalBranchCrossing
  GaloisForLFunctions.Bottcher.RelativeRigidityHNBCrossing`
- `lake build GaloisForLFunctions.Bottcher.BasinColimit
  GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary
  GaloisForLFunctions.Bottcher.RelativeRigidityHNBCrossing`
- `git diff --check` over touched hRigid files
- placeholder scan for `sorry`/`admit`/`axiom`/`opaque`/`unsafe` over touched hRigid files
- `#print axioms` for the new finite-family/strong-root bad-locus theorems and rewired q62 endpoints:
  only `[propext, Classical.choice, Quot.sound]`
- `#print axioms` for `exists_global_branch_of_sqrt_family_modulus` and the rewired square-root
  natural-boundary endpoints: only `[propext, Classical.choice, Quot.sound]`
- `#print axioms` for `exists_sqrtLevel_succ_of_simplyConnected`: only
  `[propext, Classical.choice, Quot.sound]`
- `#print axioms` for `exists_sqrt_family_of_simplyConnected_levels` and
  `exists_global_branch_of_simplyConnected_levels_modulus`: only
  `[propext, Classical.choice, Quot.sound]`
- `#print axioms` for
  `noRelation_phiMero_of_naturalBoundary_commonBasin_simplyConnectedLevels_offOther_crossing`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityHNBCrossing.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeRigidityHNBCrossing`
- `#print axioms` for
  `noRelation_phiMero_of_emptyInterior_commonBasin_simplyConnectedLevels_offOther_crossing`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/DendriteContinuesAcross.lean`
- `lake build GaloisForLFunctions.Bottcher.DendriteContinuesAcross`
- `#print axioms` for
  `mem_frontier_of_mem_filledJulia_emptyInterior`,
  `not_continuesAcross_of_emptyInterior_modulus_at_filled`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake build GaloisForLFunctions.Bottcher.DendriteBoundary`
- `lake env lean GaloisForLFunctions/Bottcher/NaturalBoundaryContradiction.lean`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeNaturalBoundary.lean`
- `#print axioms` for
  `nhdsWithin_compl_filledJulia_neBot_of_not_mem_interior`,
  `exists_mem_ball_compl_filledJulia_of_not_mem_interior`,
  `nhdsWithin_compl_filledJulia_neBot_of_mem_emptyInterior`,
  `exists_mem_ball_compl_filledJulia_of_mem_emptyInterior`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/ConnectedRepellingPeriodicAvoidance.lean`
- `lake build GaloisForLFunctions.Bottcher.ConnectedRepellingPeriodicAvoidance`
- `#print axioms` for
  `strongFixedPointRoots_orbitProduct_at_fixed`,
  `mem_strongFixedPointRoots_of_fixed_pow_norm`,
  `mem_strongFixedPointRoots_of_fixed_norm_gt_two`,
  `strongFixedPointRoots_card_pos_of_fixed_norm_gt_two`: only
  `[propext, Classical.choice, Quot.sound]`
- `#print axioms` for
  `fixedNormGtTwo_finset_subset_strongFixedPointRoots`,
  `fixedNormGtTwo_finset_card_le_strongFixedPointRoots_card`,
  `squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_fixedNormGtTwo_finset`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/ConnectedRepellingPeriodicAvoidance.lean`
- `lake build GaloisForLFunctions.Bottcher.ConnectedRepellingPeriodicAvoidance`
- `#print axioms` for
  `phiMero_transcendental_of_repelling_standard_squarefree_budget_fixedNormGtTwo_clearedDenominator_noExtra_input`:
  only `[propext, Classical.choice, Quot.sound]`
- `#print axioms` for `exists_rightmost_filledJulia` and `rightmost_mem_frontier_filledJulia`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/GlobalBasinBranch.lean`
- `lake build GaloisForLFunctions.Bottcher.GlobalBasinBranch`
- `#print axioms` for `false_of_rightmost_halfplane_dendrite` and
  `false_of_rightmost_halfplane_dendrite_emptyInterior`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake build GaloisForLFunctions.Bottcher.ConnectedRepellingFibreInput`
- `lake build GaloisForLFunctions.Bottcher.ConnectedRepellingPeriodicAvoidance`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityHNBCrossing.lean`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityNaturalBoundary.lean`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityGlobalBranchCrossing.lean`
- `#print axioms` for
  `exists_compRelPoly_denominator_of_minimal`,
  `chosenCompRelDenom_spec`,
  `phiMero_transcendental_of_repelling_chosen_denominator_input`,
  `phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_chosenDenominator_noExtra_input`,
  `phiMero_transcendental_of_repelling_standard_squarefree_budget_nonStrong_clearedDenominator_noExtra_input`,
  `phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input`,
  and the strongest rewired `_repellingG` endpoints: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeFibreGeneric.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeFibreGeneric`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityNaturalBoundary.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary`
- `#print axioms` for
  `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior`,
  `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeFibreGeneric.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeFibreGeneric`
- `#print axioms` for
  `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_globalRegion`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeFibreGeneric.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeFibreGeneric`
- `#print axioms` for
  `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeFibreGeneric.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeFibreGeneric`
- `#print axioms` for
  `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_carrierClosure`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityNaturalBoundary.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary`
- `#print axioms` for
  `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_globalRegion`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityNaturalBoundary.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary`
- `#print axioms` for
  `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_commonComponent`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityNaturalBoundary.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary`
- `#print axioms` for
  `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_carrierClosure`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityNaturalBoundary.lean`
- `lake build GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary`
- `#print axioms` for
  `noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing_globalRegion`: only
  `[propext, Classical.choice, Quot.sound]`
- `lake env lean GaloisForLFunctions/Bottcher/IndexEstimate.lean`
- `lake build GaloisForLFunctions.Bottcher.IndexEstimate`
- `#print axioms` for
  `eventually_exceptional_mass_small_roots`,
  `eventually_false_of_pinned_bulk_repelling`: only
  `[propext, Classical.choice, Quot.sound]`

## What the created pieces already remove

- The natural-boundary predicate is no longer a raw input in the empty-interior case.
- Basin-side nontriviality at a boundary/non-interior target is now a named theorem in
  `DendriteBoundary.lean`; downstream natural-boundary proofs no longer need to rederive
  `𝓝[(filledJulia c)ᶜ] z₀` nontriviality from `closure_compl`.
- The selected separable fibre is no longer a raw input in the crossing route; it is produced by
  `exists_commonBasin_input_of_sparse_fibre_crossing`.
- In the empty-interior crossing route, a target point supplied only in `filledJulia c₁` is now promoted
  internally to `frontier (filledJulia c₁)` by
  `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior`.
- The empty-interior sparse crossing route can now supply the open/preconnected common-basin region once,
  via `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_globalRegion`; the pointwise
  target geometry only needs filled/off-other membership, a local sector into that region, and punctured
  sector preconnectedness.
- The common-basin region can now be created as the connected component of
  `(filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ` containing the carrier `U`, via
  `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent`.  The caller
  supplies closure contact of that component at each target plus local punctured-sector preconnectedness;
  Lean derives the open/preconnected `V`, `U ⊆ V`, basin inclusions, and sector inclusion into `V`.
- Component-closure contact can now itself be created from carrier closure via
  `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_carrierClosure`: if
  `S ⊆ closure U`, Lean uses preconnectedness of `U` inside the common basin to prove the targets lie in
  the closure of the common component containing `U`.
- The `γ`-level no-relation endpoint can now consume that common-component payload directly through
  `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_commonComponent`, so the
  actual hRigid route no longer has to expose the global common-basin region at this layer.
- The `γ`-level no-relation endpoint can now also consume the carrier-closure payload directly through
  `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_carrierClosure`, so this layer
  no longer has to expose the common-basin component when the crossing target set is known to lie in
  `closure U`.
- The corresponding `γ`-level no-relation endpoint is now available as
  `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_globalRegion`, so downstream
  routes can consume the reduced global-region callback directly.
- The level-root route can now consume the same reduced global-region callback directly through
  `noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing_globalRegion`, while still
  creating both global basin branches from the level-root towers internally.
- The full `2^n` power-law tower and the modulus-carrying global branch are no longer raw inputs in the
  newest square-root routes; they are produced by `exists_global_branch_of_sqrt_family_modulus` from a
  coherent square-root family.  The coherent family itself is now produced by
  `exists_sqrt_family_of_simplyConnected_levels` from the simply-connectedness of successor escape
  levels, and the HNB crossing route has a direct simply-connected-level endpoint.  This is an
  over-strong constructor route; it should not be treated as the main final geometry unless the level
  hypothesis is replaced by a genuine monodromy/uniformization theorem.
- The right-half-plane branch route no longer has to reprove or externally choose the rightmost
  filled-Julia anchor: `exists_rightmost_filledJulia` creates it, and
  `rightmost_mem_frontier_filledJulia` proves it lies on the Julia frontier.  The half-plane dendrite
  contradiction now consumes that anchor internally via `false_of_rightmost_halfplane_dendrite`; the
  empty-interior variant also creates the local empty-interior ball, leaving only the punctured-sector
  preconnectedness and fibre nondegeneracy package at the rightmost frontier point.
- The abstract `Transcendental (RatFunc ℂ) (phiMero c₂ hU₂)` can be replaced by the current
  cleared-denominator direct strong-root-card repelling interface in the `_repellingG` endpoints,
  including the empty-interior natural-boundary endpoints.
- The direct strong-root-card `c₂` input can now itself be created from a finite set of ordinary fixed
  points with `‖(2 : ℂ) * z‖ > 2` whose cardinality beats the internally chosen squarefree budget, via
  `phiMero_transcendental_of_repelling_standard_squarefree_budget_fixedNormGtTwo_clearedDenominator_noExtra_input`.
- On the `c₁` side, strong periodic orbit-product repulsion now proves frontier membership internally.
- In the index/pinned-bulk route, the exceptional-mass smallness inequality is no longer a terminal
  hypothesis once `B` is a finite set of repelling fixed points and `p` is sufficiently large:
  `eventually_exceptional_mass_small_roots` converts the analytic estimate to the actual
  `card(roots ∖ B)` bulk, and `eventually_false_of_pinned_bulk_repelling` feeds it to the index
  contradiction.
- On the `c₂` side, the repelling interface no longer asks for a squaring-fixed simple fibre root, a
  chosen fibre root, fibre-level degree/constant data, one point avoiding every possible denominator,
  pointwise fibre separability/leading-coefficient avoidance at the selected periodic target, or the
  full-degree squarefree witness specialization, `fixedPointPoly` separability at the terminal
  endpoint, or a non-strong count comparison.  The squarefree witness is now created internally from
  minimal-relation function-field separability by
  `minimal_relation_fraction_field_separable`,
  `exists_abs_full_separable_specialization_of_fraction_separable` and
  `HolomorphicIFT.exists_squarefree_specialization`.
  The previous accumulating fixed-period target callback has been superseded: the current `c₂`
  callback chooses a period `p`, then proves
  `squarefreeBadDegreeBudget P (chosenCompRelDenom hUo hUne c₂ hU₂ P hP0 hPrel hPmin p) ∅ <
  (strongFixedPointRoots c₂ p).card`.  The Lean bricks
  `roots_biUnion_card_le_sum_natDegree`, `exists_mem_finset_avoiding_polys_of_sum_natDegree_lt`,
  `squarefreeBadFamily_ne_zero`, `separable_specialization_of_avoids_squarefree_bad_locus`,
  `squarefreeBadDegreeBudget_empty`, `exists_strong_fixedPoint_avoiding_squarefreeBadFamily_of_budget_card`,
  and `hasDerivAt_quadratic_iterate` now create the empty extra bad family, the avoiding strong target
  point, standard nonzero facts, fibre separability, and derivative witness from this finite count.

## Remaining work for a hypothesis-free both-connected theorem

The final theorem is not done.  A theorem that still carries these as terminal hypotheses must not be
presented as the q62 close.

1. **General Eremenko-van Strien natural-boundary obstruction.**
   Current code proves the obstruction from `interior (filledJulia c) = ∅`.  The full connected
   nonexceptional theorem needs an axiom-clean Lean proof that analytic continuation of the basin
   Böttcher branch through a Julia point forces a smooth Julia piece, then E-vS rigidity forces
   `c ∈ Exceptional`, contradiction.

2. **Absolute `c₂` finite periodic-point construction.**
   The geometry/count callback still must be created from dynamics: for each minimal relation, prove
   existence of a period `p` with
   `squarefreeBadDegreeBudget P (chosenCompRelDenom hUo hUne c₂ hU₂ P hP0 hPrel hPmin p) ∅ <
   (strongFixedPointRoots c₂ p).card`.  The denominator identity is now constructed by Lean; the old
   every-denominator quantifier, explicit `e,S` terminal hypothesis, explicit fixed-point-polynomial
   separability hypothesis, and non-strong-count comparison are no longer the active route.

3. **Capacity/common-basin crossing geometry.**
   The hRigid endpoint now consumes sparse crossing data plus pointwise common-basin target geometry.
   The missing created theorem should supply this geometry from distinct connected parameters:
   enough points in `filledJulia c₁ ∩ (filledJulia c₂)ᶜ`, accumulating inside an analytic coefficient
   region, with local preconnected basin sectors from the carrier `U` to the selected point.

4. **Actual branch construction on connected basins.**
   The square-root constructors now promote coherent recursion, and even the over-strong
   simply-connected-level input, to a modulus-carrying global branch.  The final connected theorem still
   needs the genuine branch/uniformization theorem on `(filledJulia c)ᶜ`; do not aim to prove exterior
   escape levels simply connected as the main route.  The half-plane route has a canonical frontier
   anchor via `exists_rightmost_filledJulia` and `rightmost_mem_frontier_filledJulia`; the remaining
   local geometry there is the dendrite/tip or E-vS continuation input, not the anchor.

5. **Final assembly without terminal theorem-shaped hypotheses.**
   The current endpoints are Lean-clean reductions.  They are not the q62 close until the callbacks
   above are supplied as theorems rather than carried as hypotheses.

## Coordination boundary

- Avoid the hDisc files unless the user explicitly redirects: `HDiscLoopDeck.lean`, deck/cover
  construction files, and the disconnected Kummer lane are separate work.
- `Bottcher.lean` already imports the new hRigid files.  Do not churn the import list except when a new
  module is genuinely added.
- Keep every new theorem axiom-clean.  Run `#print axioms` from `/tmp`, not by editing the tree.

## Target shape

The target remains an unconditional both-connected `NoRelation` theorem for the genuine Böttcher
coordinates, suitable as the `hRigid` branch of `q62_independence`.  The proof must have no extra axioms,
no `sorry`/`admit`, and no terminal hypothesis that is just the missing theorem in another form.
