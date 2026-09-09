# Selberg continuation — complete character core/cusp gluing and arithmetic seam integral

2026-09-09, cycle49. Root unbudgeted Selberg quarter goal remains ACTIVE / UNPROVED. This turn completed two positive corpus-derived proof loops. Do not repeat completed normalization/gluing or declare the full conjecture solved.

Previous context: `mem:selberg/character-core-and-observed-cusp-2026-09-09`, then `mem:selberg/character-seam-phase-flux-2026-09-09`.

## Finished module and verification

`formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterCuspGlue.lean`:372lines,28public declarations,1local normality instance. Namespace matches module. Imports CharacterCoreGreen,ReadoutCusp,ResidualSupport (reuses actual source gradient continuity).

All complete scratch/source checks passed. Final `lake build GaloisForLFunctions.RHTower.SelbergMaassCharacterCuspGlue` rebuilt only named target in6.8s. All28 post-build axiom rows contain only standard propext,Classical.choice,Quot.sound. Source hash unchanged. One umbrella import. Exact-module API/search coverage28public+1local. Index refresh and repository lint passed, existing large-file warnings. Scoped whitespace and96research-card links passed. All owned handles terminal; process scan found no owned Lean/Lake. No full/umbrella build, overlap, numerical experiments, commit,or push.

Artifacts `/tmp/selberg_glue51_manifest.json`, `_audit.json`, `_coverage.json`, `.lean`, `_source.log`, `_build.log`, `_axioms.lean/log`, `_index.log`, `_lint.log`. All done; do not rerun checks absent new changes.

## Exact positive results

- `upperReadout N r q := (EuclideanSpace.proj q).comp (characterProjection N (upperBlock N) r).toContinuousLinearMap`.
- `mass_slice_continuous`, `mass_slice_periodic`, `current_slice_periodic`: physical chart mass/current continuous and unit-periodic.
- `readoutMass_eq_integral`: exact level-normalized squared coordinate integral.
- `mass_integral_eq_sum_readout`: integral0..1 original characterMass=sum_q observed masses.
- `readoutMass_hasDerivAt`, `mass_integral_hasDerivAt`: actual mass derivatives=twice physical observed flux.
- `unit_current_eq_sum_readoutFlux`, `sum_readoutFlux_eq_topCurrent`(line154): complete observed flux=sum matches topCurrent/2. Proof differentiates physical unit-strip mass equality and shifts unit-period current to[-1/2,1/2].
- `readout_hyperbolicMass_tail_integrable`, `character_tail_mass_integrable`, `tailMass_eq_sum`: genuine integrability and exact finite sum/integral exchange for every exceptional Maass source, including zero observations.
- `tailMass N f r Y`: literal integral_y>Y (integral_x0..1 characterMass(point x y))/y².
- `boundarySum N f r T`: finite qsum of entire integer Bessel seam series for literal upperReadout.
- `squareSum`: finite qsum of entire observed mode-square tails; `squareSum_nonneg`.
- `character_flux_boundary_identity`: -topCurrent(expT)/2+(lam-1/4)*tailMass(expT)=boundarySum+squareSum.
- `core_cusp_quarter_identity`(line236), `core_cusp_quarter_identity_one`(line279): Qcore+B+S=pairedArcIntegral/2+(lam-1/4)*(coreMass+tailMass). All quantities literal; zero cutoff height T=0 gives physical Y=1 with no extra height hypothesis.
- `boundarySum_eq_projected_fourier`: B=sum'_n seam(loglevel,T,n)*norm(P_r coefficientVector(n,expT))².
- `boundarySum_eq_residue_fourier`: equivalently sum'_n if n modlevel=r then seam*norm(coefficientVector)² else0.
- `squareSum_eq_mode_sum`: justified exchange to sum'_n sum_q squareTail, using actual proved summability.
- `arcLossGradient N f r x`: (norm(sourceVector(circle x))²-norm(inversionTransfer r r sourceVector(circle x))²)*original gradientDensity(circle x).
- `arcLossGradient_continuousOn`: continuous on full modular arc[-1/2,1/2], from actual source/gradient smoothness and finite linear transfer continuity.
- `pairedArc_integral_sq_le`: (integral_0..1/2 J)² <=(1/2)*integral J², proved by literal square completion J-2*integral J. No global continuity extension is imposed.
- `half_pairedArc_integral_sq_le`(line342): (integral J/2)² <=(2/3)*integral arcLossGradient, using original cycle47 J²<=(16/3)*loss*gradient and the half-arc length.
- `core_cusp_balance_sq_le`(line362): [Qcore+B+S-(lam-1/4)*(coreMass+tailMass)]² <=(2/3)*integral arcLossGradient atY1.

## Corpus and paper provenance

Broad explicit OR gluing/interface/transmission/current/periodic retrieved9771declarations2366modules (`_corpus.json`). All matching metadata retrieved, not all bodies read. Actual mass normalization, pairing derivative, physical trace Stokes and complete cusp formula inspected. Follow-up AND integral/square/current yielded5declarations4modules (`_integral_corpus.json`); read SelbergWeightedPathEnergy square-completion/resistance proof. Adapted square completion directly to actual current's compact arc continuity.

## Remaining next positive target

The finite core/cusp assembly is now COMPLETE. Do not repeat it. Use actual residue Fourier form and complete inversion phase/angular decomposition to compare coherent seam response with positive physical bulk terms. Need a source-derived uniform full-domain mass<=4physicalGradient comparison; no trace-to-area estimate, angle, boundary sign or coercivity assumption has been introduced. New2/3 is a seam integral coefficient, not the spectral quarter constant. Full Selberg remains unproved. Existing angular remainder and original phase triple law remain explicit.

Research card `docs/drafts/pipeline/1-in-progress/selberg-character-core-green.md` remains1-in-progress only because quantitative full-quarter comparison is still required. Parent conjecturing-loop and original-source-current cards updated throughcycle49. Four modules in current card total80public declarations.

## Toolchain lessons

- `dir` is polymorphic. In Complex coercion context use `((dir I D z : ℝ):ℂ)` explicitly; otherwise Lean infers wrong complex codomain for real D.
- Annotate `have hint : ∀a b, IntervalIntegrable ... volume a b`; unannotated `.intervalIntegrable` leaves measure typeclass unresolved.
- `coefficientVector` lives in SelbergMaassUnipotentFourier, not CharacterFourier; open correct namespace.
- `Summable.tsum_finsetSum` exists. `Summable.finsetSum` and `Complex.inner_def` do NOT. Use `hasSum_sum` for finite sum convergence.
- hyperbolicMass_tail_integrable lives in SelbergMaassTailEnergy, not Flux.
- For core+cusp equations, `linear_combination hc-ht` is the correct sign.
- Research tool rejects empty query. Exact module query `research SelbergMaassCharacterCuspGlue --module SelbergMaassCharacterCuspGlue ...` returns all29entries.
- Filename SelbergBesselModes.lean does NOT exist; namespace is in SelbergBesselAdverseModes.lean. Use rg --files before guessed paths.
- Keep every Lean process strictly serialized, wait until terminal. Other agents' unrelated processes untouched.
