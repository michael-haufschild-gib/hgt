# EWU: purification survives finite-energy completion

Status: in progress. Scope: unconditional structural existence; no RH sign claim.

## Obstruction

Fixed-window purification already removes finite mixture rank, including strict-interior smooth sources. It does not supply a source for a limiting autocorrelation. Smooth compact sources are not closed under the convergence available to energy minimization, and choosing an entire factor separately at every stage gives no phase continuity.

## Conjecture loop

1. Smooth purification should survive every energy-bounded limit as a smooth source. Rejected: the actual logarithmic form norm does not provide smoothness. No claim of a smooth limiting source is justified.
2. Use the actual complete CCM form domain instead. Conjecture: at every fixed positive aperture and finite energy budget, the pointwise closure of normalized finite positive smooth even polar mixture profiles consists of profiles of actual even polar form-domain vectors in the same aperture and budget. This removes both infinite-mixture rank and phase-selection escape.
3. After proving this, seek actual attainment with the arithmetic observations imposed, rather than a conditional minimizer receiver.

## Dependency-closed paper argument for conjecture 2

Write J for the compact embedding of the actual CCM archimedean form domain into the physical aperture L2 space. Its literal source quadratic satisfies Q(u)=||u||_form^2+D(Ju), with D a bounded continuous quadratic. Thus normalized physical vectors with Q<=B lie in the compact closure of J of one form ball. The physical Q sublevel is closed by the existing lower-semicontinuity theorem. Reflection-fixedness and the two polar moments are closed physical constraints. Their intersection with norm one and the sublevel is therefore compact.

The complete autocorrelation h -> <translation(-h)f,f> depends continuously on f in physical L2, pointwise in h (in fact uniformly). Its image of that compact set is compact and closed in the product space of complex profiles. Every normalized budgeted positive finite mixture lies in that image: exact interior-window purification gives one smooth even polar source; the existing smooth CCM/zeta identity identifies its energy, and its correlation at zero identifies its norm. Hence the entire pointwise closure lies in the same actual single-source image. No coherent choice of phases along the approximating family is needed.

Preserves: actual aperture, full profile, normalization, both pole constraints, every arithmetic observation, finite completed energy budget. Does not assert smoothness at the boundary, positivity of the blind minimum, or equality of energy along arbitrary convergent sequences.

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
