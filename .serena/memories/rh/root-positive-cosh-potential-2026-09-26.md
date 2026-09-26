# Root RH checkpoint — positive-cosh source ansatz closed

## Goal/rules/status
Goal remains ACTIVE and unachieved: unconditional Lean proof/falsification of RH. On every continuation read `/Users/michael/.codex/attachments/57626bac-f4cf-4d94-bed5-5e4426c73652/pasted-text-1.txt`. No git, no numerical experiments, one foreground Lean process, scratch validation then named leaf builds only, no full/umbrella build. No subagents authorized. All owned jobs exited at this checkpoint. Previous turn classified PROGRESS: new actual-source no-go and quantitative survivor, 16 theorems verified.
Methods previously read docs/meta/stroke-of-genius-method.md and scientific-method.md. Existing init/manual/memories done; architecture/testing absent. update_plan unavailable; own cards hold plans. Corpus direct research command required; deep queries perform method retrieval, --mode method invalid. Don't inspect search implementation/help unless command fails. Inspect partial/compiler coverage. Preserve others' logs/modules.

## New completed theorem
File `formal/GaloisForLFunctions/RHTower/ThetaPositiveCoshPotentialObstruction.lean`, ~345 lines, 16 public theorems, wired in RHTower umbrella.
Phi=thetaCuspFullSource; potential(x)=log Phi(0)-log Phi(x).
Literal complete-source envelope gives `pi*exp(2x)-(9/2)x+C1 <= V(x) <= pi*exp(2x)-(9/2)x+C2` forx>0. Thus exp(-2x)V(x)->pi and
`(V(x)-2pi(cosh(2x)-1))/x -> -9/2`.
Closed unconditional no-go: no q>=0, summable a_n>=0, b_n>=0, all real-halfline mode sums admitted, satisfy V(x)=qx²+sum a_n(cosh(b_nx)-1). Stronger no-go excludes an added r with r(x)/x->0.
Positive survivor: generic positive-cosh spectral edge. If F=q x²+sum modes has exp(-cx)F->C (c>0), active b_n<=c, total mass at b_n=c is exactly 2C, and F>=2C(cosh(cx)-1). Any exact theta repair r negligible relative to exp(2x) therefore satisfies eventually r(x)/x < -9/2+eps for everyeps>0. This keeps full countable mode sum.
Scope: representation test [BRIDGE], not a Lee–Yang theorem for arbitrary cosh potentials, not a failure of all interacting Ising/nonsummable classes, not RH. No global novelty claim. Do not spend next turn refining this rejected class.

## Proof ingredients
Generic namespace RHTower.PositiveCoshEdge: mode=cosh(bx)-1, mode_nonneg, scaled_mode_eq, exp_neg_rate, scaled_power_limit, scaled_mode_limit, scaled_mode_le_one, active_frequency_le, mode_sum_scaled_limit, edge_mass_and_floor (line143).
For active b>c, multiply F by exp(-bx): finite c-leadinglimit implies0 but positive mode givesa/2, contradiction. After b<=c, Tannery dominated convergence bounded bysummableweights identifies edge mass. Positive rest givesfloor.
Literal namespace RHTower.ThetaCoshPotential: potential_bounds, scaled_potential_limit, exists_potential_below_edge, no_positive_cosh_representation (line251), potential_edge_linear_limit (281), correction_eventually_le_linear (293), no_sublinear_positive_cosh_representation (317). Imports HedenmalmThetaKernelEnergy (two-sided actualenvelope) and Mathlib.Analysis.Normed.Group.Tannery. No complexzero premise.

## Verification
Scratch /tmp/rh-positive-cosh-edge.lean/log passed. Named build /tmp/rh-positive-cosh-build.log passed9109jobs. Axiom scratch /tmp/rh-positive-cosh-axioms.lean/log audited all16publicnames against /tmp/rh-positive-cosh-axioms-expected.json: no missing/error, onlypropext/Classical.choice/Quot.sound. Parser must splitaxiomlist on comma and stripwhitespace (one report wraps lines; initialparserfalsealarmfixed withoutrerunningLean). /tmp/rh-positive-cosh-index.log success; /tmp/rh-positive-cosh-lint.log GLOBALPASS with existinglargefilewarnings. All processhandles terminal. Two ring tactic informational messages fromconvert aren't errors; no optionalcosmeticretestingneeded.
Owned final handles (allterminal): scratch24246; build38410; audit35864; index12467; lint41851. All searchesbelowterminal.

## Cards/facts
Own root card moved stage1 -> `docs/drafts/pipeline/5-failed/rh-positive-cosh-potential-root-2026-09-26.md`; contains frozenC3, completepaperproof, exactstrongerpositive survivor, explicitclass/scope,16theoremverification. Oldstage1rootfiledeletedafterownershipcheck.
Own main `docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26.md` appendednewclosure andcorrected staleGABTCnextgate. Own facts sibling `...-facts.md` nowF1–F44. F41distinguishcutoffcarriers; F42actualcoshno-go; F43exactedge/linearcorrection; F44verification. Nevereditotherlogs.

## Route audit/current hard gap
Source all-polynomial/Hankel sign remains open. Positive auxiliarymomentsequence isnotcanonicalincidence. DegreezeroGABTC alone oneHankelblock, noallorderupgrade. TH firstopenactualfifthmomentmustbecontrolledjointlywithlowerdeviations; genericmonotonicity/logconcavity/strictRawGram/allorderupperrecurrence fail. Exact arithmetic/modular/interacting source law required. Candidateconstructionmustretain signedprefactor andfull infiniteassembly. No next primary producer conjecture selected; don't mechanically generate more asymptotic/no-go lemmas or restate RH-equivalentpremises.
Readprior card theta-all-degree-hankel-producer.md: allorderconnectedhardexclusion incidence, sourceSchurpositive norm, Ising/FKrealization,clearedkernelpositiveoperator allunconstructed. B/Dmonotonecontraction waskilledpreviously. Everyfiniteprefixnonrealzeros Leanclosedpreviously.
IMPORTANT F41: j~N² in `theta-center-pair-singularity-condensation.md` is integratedpaircurrent offdiagonalsingularity condensation, NOT a known boundonfirstnegativefiniteprefixHankeldegree. No transferproofwasfound; don'tconflatecarriers.
That other card (read1–340,402–680) alreadypaper-proves fixedNpositiveTaylor tail, fullrationalwallThomaecharge, shrinkingGamma-profile, naturalsourcecurrentboundary, leadingwalltail-invariancecountermodels, exactrelativecore response atdelta^(9/2). Leadingwallpositiveprofile isn'tRH sign; ratioamplitudesnonsummable. Avoidduplicating these.
Other owner's new `ThetaCuspChargeModularCriticality.lean` and `ThetaCuspChargeCriticality.lean` source-read (NOT built/audited byus): statements give arbitrarily smallpositive exactlymodular deformations with positive realsource andanoff-linezero. Not actualXi/RHfalsification. Alltheirnew modulesnowwired (priorlint6missingresolved externally); don'ttouch.

## Completed corpus searches
/tmp/rh-root-cleared-kernel-method-20260926.json (partial)
/tmp/rh-root-tilt-flux-method-20260926.json (partial)
/tmp/rh-root-cutoff-degree-method-20260926.json (partial)
/tmp/rh-root-theta-potential-method-20260926.json (complete retrieval)
/tmp/rh-root-positive-cosh-edge-deep-20260926.json (partial)
All inspected candidates/source_arguments/ingredient_sets/prose. Sourceinventory~59537complete; compiler mostlypending/stale; no ready positivecoshrepresentation/completeedgetest retrieved. Sourcesverifieddirectlyandmathnamesin/tmp APIscratch. Broadsearches oftenreturnunrelatedmodules; preferfocusedfollowups, notmassiveheadingrgallcards.

## Prior completed research
See `mem:rh/root-cold-corner-transfer-2026-09-26` for full literal-theta negativecold/degree diagonal and39audits; that result remainsLeanclosed. Foru>0, L_n=(n+.5)/u, L_n^4 S_n(-L_n)->(logPhi(sqrt y))'''(u), negativeatu9⇒eventualnegativeactualS. Globalallj aperturepositivityfalse; notGABTC/RHrefutation. Sixleavesin stage3/rh-cold-degree-corner-2026-09-26.md; actualnogoin5failed/rh-global-all-degree-aperture-convexity-root-2026-09-26.md. Earlierrootclosures: monotoneGramcontraction, allfiniteprefixnonrealzeros, dyadicwindingclassification, exactimaginaryarccharges+interiorsourcezero. Do notredo.

## Lean/edit gotchas
No guessedmathlibimportpaths: Hyperbolic.lean doesnotexist; Real.cosh_eq inAnalysis.Complex.Trigonometric; one_le_cosh inTrigonometric.DerivHyp, alreadyimported byHedenmalmThetaKernelEnergy. Tannery requires explicit(𝓕:=atTop) whenhave holes. `id_eq` needed aftercompositiontendsto_id. Conditional limit `if b=b then1/2else0` needs typed hmode with `by simpa using ...`; deleting an apparentlyunusedsimp tactic removesitsimplicit simplifications. Positiveifweights useha nexplict, positivitydoesn'talways instantiateforall. field_simp thenring; modelleadingexpidentity needs linear_combination Real.pi*he (nlinarith alone missestripleproduct). Preserve exactnewlinedata inmetadata/parser. Pythontriple singlequotes unsafeformath''' derivatives. rg directory --glob ratherthanhugeglobargv.
