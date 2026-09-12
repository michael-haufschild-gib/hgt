# Actual SL2 Haar quotient and strongly continuous unitary representation

2026-09-12, /Users/michael/Documents/code/hgt; Lean root formal/. Goal remains ACTIVE, no budget. User requires corpus/deep/method searches first, actual mathematical obstacle attacks, foreground one Lean process, no added axioms/sorry/limits/numerical certificates; lake env lean for scratch/needed oleans, lake build <module> only final audit; no umbrella builds. No subagents authorized. Shared repo has other active workers; don't modify their files/processes.

## New verified modules
- GaloisForLFunctions/RHTower/RealSL2Haar.lean (74 lines): concrete standard SL2R topological/Borel, locally compact, second countable, Polish instances; actual nonzero sigma-finite Haar. Matrix.SL2.commutator_eq_top with real a=2 gives perfectness. Abelianization.commutator_subset_ker applied to character.toHomUnits kills every commutative-monoid character, hence actual Measure.modularCharacter=1 and actual right-Haar invariance. Avoids Mathlib modular-character continuity TODO. Exact namespace Matrix.SL2, NOT Matrix.SpecialLinearGroup.SL2.
- IntegralSubgroupQuotientMeasure.lean (~206 lines): PRIVATE proved countable-cover least-patch selector and discrete-subgroup domain construction. W z = z * interior U, where U has disjoint nontrivial subgroup right translates. Cover by countably many W; keep points whose orbit misses all earlier patches, Nat.find proves strict existence/uniqueness. Actual integralSL2ToReal image of every Γ : Subgroup SL2Z is countable/discrete. Constructs integralSubgroupFundamentalSet, proves measurable and each orbit unique, actual Haar IsFundamentalDomain, HasFundamentalDomain (realImage Γ).op SL2R realSL2Haar. integralSubgroupQuotientMeasure on G/Gamma is actual pushforward of restricted Haar; nonzero, sigma-finite, locally finite, regular, invariant under all SL2R left translations. Strong positive lemma quotientMeasure_image_le: mass of π '' A ≤ Haar A for measurable A. No normality, finite-index or finite-covolume premise. Right multiplication orbits x Gamma are LEFT cosets G/Gamma; avoid mistaken terminology.
- IntegralSubgroupUnitaryRepresentation.lean (70 lines): integralSubgroupUnitary Γ g is complex LinearIsometryEquiv on Lp C 2 of actual quotient measure. Implemented using DistribMulAction.toLinearEquiv C _ (DomMulAct.mk g⁻¹). One/mul laws, integralSubgroupRegularRepresentation bundled Representation C SL2R, literal pullback v(g⁻¹ q) AE, joint continuity hence strong continuity, inner product preserved. Global explicit quotient Regular instance shortens search; local Fact ((2:ENNReal)≠top) proved by norm_num. No limits raised.

## Verification DONE
- Combined scratch /tmp/maass_quotient_measure.lean passed. Actual modules passed lake env lean; only needed Haar and quotient oleans generated manually.
- Final LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.IntegralSubgroupUnitaryRepresentation passed: 3 modules rebuilt at 2.2/2.5/2.7s, all other dependencies cached (3218 jobs total). /tmp/maass_quotient_final_build.log.
- /tmp/maass_quotient_axioms.lean audits all 37 public declarations incl instances/defs; passed, output /tmp/maass_quotient_axioms.log parsed and every dependency set restricted to propext, Classical.choice, Quot.sound. Names /tmp/maass_quotient_audit_names.txt.
- Three umbrella imports exactly once (around RHTower.lean16631-33, may shift). Scoped no-forbidden/no-limit changes, whitespace and diff checks passed.
- scripts/formal_tools.py index then lint --check-generated; concurrent sources caused stale generated indexes. Refreshed once more; final lint /tmp/maass_quotient_lint_refresh.log fails ONLY unrelated untracked/unwired RHTower.ThetaCuspHawkingBMBackgroundDiagonalJet. Did not edit/build that other worker's file. All stale-generated errors cleared. Do NOT claim global lint passed.
- All owned Lean/lake/search sessions collected; process audit 0 owned Lean/lake. No commits/push. Capstone file opened in Codex (queued).

## Current proof chain / next obstacle
Prior verified actual finite differential Maass-model intertwiner, faithful finite-coset hyperbolic source L2, and first ladder energy are in mem:selberg/maass-actual-l2-first-ladder-2026-09-12. Now actual ambient quotient unitary representation exists. Missing: actual Maass-source admission into this quotient L2 and exact comparison with earlier norm, including central -I multiplicity; all-order derivative domains; identification of cyclic Hilbert closure. Unitarity alone still allows complementary series. Arithmetic exclusion needed for lambda>=1/4 remains unproved. Do not claim Selberg solved.

Next serious paper route: actual Iwasawa section b(z), compact stabilizer K; push hyperbolic volume times normalized Haar(K) by (z,k)->b(z)k. Left g gives (gz,c(g,z)k): hyperbolic measure and fiberwise Haar invariance prove left Haar invariance. Uniqueness supplies positive normalization. Need actual measurable/homeomorphic decomposition, K compact normalized measure, and quotient central multiplicity. This is a PAPER PLAN, not proved. Do not insert fields assuming desired norm identity.

## Searches / paper screening
Custom deep/method files /tmp/maass_sl2_unimodular_search.json, /tmp/maass_modular_character_methods.json, /tmp/maass_discrete_quotient_search.json, /tmp/maass_measurable_selector_methods.json, /tmp/maass_quotient_lp_methods.json. Mixture of partial/source-only results; exact sources and Lean verified. Existing ConnesPeriodizationLift only assumes strict selector, didn't solve existence; mathlib FundamentalDomain file TODO confirms generic existence absent. Broad arXiv rigidity -> Chow/Wang arxiv2609.11702 Sep10 positive isotropic curvature higher-dimensional eigenform theorem inapplicable; transport -> Weng arxiv2608.17363 Aug18 assumes LCA group, doesn't give SL2R estimate. Both opened and screened; no claimed transfer.

Persistent card docs/drafts/pipeline/1-in-progress/selberg-actual-maass-model-intertwiner.md updated top frontier and appended paper proofs/audits/next bridge. Don't reread whole long card; offsets/tail.

## Useful Lean lessons
- Matrix types and SL2Z may need explicit inferInstanceAs on finite Pi/subtype for Countable/LocallyCompact/SecondCountable/Polish.
- Exact right-separation lemma IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty.
- isOpen_iUnion_countable in TopologicalSpace namespace.
- No MeasurableSet.forall; use countable iInter including Prop binder.
- QuotientGroup.isOpenMap_coe (N := subgroup) U hU, subgroup is implicit.
- QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := realSL2Haar) μ, must specify ν.
- Import Topology.Algebra.ProperAction.Basic for Hausdorff nonnormal quotient. Explicit Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure works when broad synthesis stalls.
- Representation map laws: apply LinearMap.ext; intro v, NOT ext v (over-descends into Lp AE equality).
