# EWU: purification survives finite-energy completion

Status: in progress. Scope: unconditional structural existence; no RH sign claim.

## Obstruction

Fixed-window purification already removes finite mixture rank, including strict-interior smooth sources. It does not supply a source for a limiting autocorrelation. Smooth compact sources are not closed under the convergence available to energy minimization, and choosing an entire factor separately at every stage gives no phase continuity.

## Conjecture loop

1. Smooth purification should survive every energy-bounded limit as a smooth source. Rejected: the actual logarithmic form norm does not provide smoothness. No claim of a smooth limiting source is justified.
2. Use the actual complete CCM form domain instead. Conjecture: at every fixed positive aperture and finite energy budget, the pointwise closure of normalized finite positive smooth even polar mixture profiles consists of profiles of actual even polar form-domain vectors in the same aperture and budget. This removes both infinite-mixture rank and phase-selection escape.
3. Actual blind attainment at every positive aperture. Paper proof succeeds: the narrow three-bump family can be placed strictly inside any aperture and below the first integer lag; its central value proves nonzero mass, so rescale to norm one. All complex integer-lag constraints are closed in physical L2. Intersect them with the compact even polar energy sublevel at this feasible source's own energy. The existing lower-semicontinuous extended actual quadratic attains its minimum there, and every feasible vector outside that sublevel has greater energy. Thus a normalized even polar blind minimizer exists unconditionally. Evenness makes each correlation real and symmetric, so these are exactly the EWU real arithmetic constraints. Both pole coordinates and the finite prime sum vanish; the optimized energy is the actual archimedean integral.
4. Lean exposes a stronger survivor: arithmetic blindness can be imposed only on the limiting profile. The approximating normalized finite mixtures need not be exactly blind. The blind slice of the entire budgeted completion still consists of actual single blind sources, and the attained pure minimum is below every such relaxed budget. This removes asymptotic constraint error together with mixture rank, without an exact correction at each approximation stage.

## Dependency-closed paper argument for conjecture 2

Write J for the compact embedding of the actual CCM archimedean form domain into the physical aperture L2 space. Its literal source quadratic satisfies Q(u)=||u||_form^2+D(Ju), with D a bounded continuous quadratic. Thus normalized physical vectors with Q<=B lie in the compact closure of J of one form ball. The physical Q sublevel is closed by the existing lower-semicontinuity theorem. Reflection-fixedness and the two polar moments are closed physical constraints. Their intersection with norm one and the sublevel is therefore compact.

The complete autocorrelation h -> <translation(-h)f,f> depends continuously on f in physical L2, pointwise in h (in fact uniformly). Its image of that compact set is compact and closed in the product space of complex profiles. Every normalized budgeted positive finite mixture lies in that image: exact interior-window purification gives one smooth even polar source; the existing smooth CCM/zeta identity identifies its energy, and its correlation at zero identifies its norm. Hence the entire pointwise closure lies in the same actual single-source image. No coherent choice of phases along the approximating family is needed.

Preserves: actual aperture, full profile, normalization, both pole constraints, every arithmetic observation, finite completed energy budget. Does not assert smoothness at the boundary, positivity of the blind minimum, or equality of energy along arbitrary convergent sequences.

## New source modules

- `EvenSectorEnergyCompletion.lean`: compact physical budgets, actual single-source profile image, exact native-source bridges, purification of the whole pointwise completion.
- `EvenSectorBlindVariationalAttainment.lean`: blind feasibility at every aperture, equivalence with real symmetric trace cancellation, actual archimedean energy identity, unconditional blind minimizer.

The completion module has built successfully. The attainment module's feasibility and actual archimedean identity checked on its first build; remaining type-inference/closed-set elaboration issues are being resolved. No mathematical premise was added.

## Corpus evidence

- EvenSectorWindowPurification: exact finite purification at unchanged interior aperture.
- CCMRestrictedWeilEvenSectorCrossZeros: actual form compactness, closed polar/even constraints, existing unconstrained even ground attainment.
- CCMConnesConsaniHilbertOne: closed physical source-energy sublevels and exact bounded-remainder decomposition.
- SuzukiCCMMixedSmoothCore / CCMZetaWeilSmoothIdentity: literal smooth sources, translations, polar moments, actual zeta energy.
- CCMApertureCorrelationKernel: completed L2 correlation, compact support, Fourier density identity.

Fresh corpus research searches executed; deep searches report complete source inventory, but most compiler enrichment is pending/stale. All names and applicability will be verified against the current Lean toolchain. No web or novelty audit.

## Audit checklist

- [ ] Source and paper proof complete.
- [ ] Foreground leaf olean build with --old.
- [ ] Direct lake env lean final audit.
- [ ] Mathlib-name probes and axiom audit in /tmp.
- [ ] Umbrella imports, formal lint, owned scratch cleanup.
