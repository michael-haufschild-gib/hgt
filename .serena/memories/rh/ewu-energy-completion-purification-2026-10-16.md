# EWU energy completion and actual blind attainment — 2026-10-16

Completed, wired, olean-built and directly Lean-audited:
- formal/GaloisForLFunctions/RHTower/EvenSectorEnergyCompletion.lean
- formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean
Card: docs/drafts/pipeline/3-formalized/ewu-energy-completion-purification-2026-10-16.md

NEW structural result beyond fixed-window finite purification: every pointwise limit of normalized finite positive smooth even polar mixture profiles, at a fixed positive aperture and finite actual Weil-energy budget, is the whole autocorrelation of ONE actual even polar source in the complete archimedean form domain at that SAME aperture. Blindness may be imposed only on the LIMIT; approximating mixtures need not be exactly blind. At EVERY positive aperture the normalized even polar arithmetic-blind actual energy has an actual minimizer in the complete form domain. Its energy is exactly the archimedean Gamma integral, not a surrogate.

Namespace RHTower.EvenSector APIs:
- energyProfile a f h := ccmApertureCorrelation a f (-h), the EF.weilTest orientation.
- physicalEvenPolarBudget a B: physical aperture L2 vectors of norm 1, reflection-fixed, both polar moments zero, with a genuine form-domain lift of actual source energy <= B.
- isCompact_physicalEvenPolarBudget a B; isCompact_completedEnergyProfiles a B; isClosed_completedEnergyProfiles a B.
- completedEnergyProfiles a B := energyProfile a '' physicalEvenPolarBudget a B.
- nativeProfileEnergy P := (weilFullFunctional vonMangoldt P).re. This is FULL Weil energy; on the blind polar domain it equals archimedean energy.
- interiorMixtureProfile a c for c : InteriorWindowedSmoothEvenPolarTestFn a ->_0 NNReal.
- nativeEnergyProfiles a B: these finite positive mixture profiles P with P 0 = 1 and nativeProfileEnergy P <= B.
- closure_nativeEnergyProfiles_subset_completed a B (line 213): closure(nativeEnergyProfiles a B) subset completedEnergyProfiles a B, UNCONDITIONAL.
- isCompact_closure_nativeEnergyProfiles a B.
- interiorCCMSource and exact profile/energy/evenness/polarity bridges identify the earlier smooth domain with actual CCM sources.
- blindProfiles := {P | forall n : LogIndex, P(log n)=0}.
- BlindUnitSource a := {u : CCMArchimedeanFormDomain a | IsPolarConstrained a u AND CCMEvenSector.IsEven a u AND norm(Ju)=1 AND energyProfile a (Ju) in blindProfiles}.
- energyProfile_eq_zero_iff_trace_zero: on even sources, complex vanishing iff real symmetric trace vanishes. Thus the constraints really are EWU's arithmetic constraints.
- nonempty_blindUnitSource a: explicit proof of feasibility at EVERY positive aperture, no feasible-seed premise.
- closure_nativeBlindProfiles_has_source a B (line 135): closure(nativeEnergyProfiles a B) intersect blindProfiles subset {P | exists u : BlindUnitSource a, Q(u)<=B AND energyProfile(Ju)=P}. NOTE intersection AFTER closure: permits asymptotic blindness.
- sourceQuadratic_blind_eq_gamma u (line 145): Q(u) = integral 2*gammaHardyPhaseRate(2*pi*xi)*norm(u.val.val xi)^2.
- exists_blind_minimizer a (line 172): exists u : BlindUnitSource a, forall v : BlindUnitSource a, Q(u)<=Q(v), UNCONDITIONAL.
- exists_blind_minimizer_for_mixture_completion a (line 211): same actual minimizer also has Q(u)<=B for EVERY nonempty blind slice of closure(nativeEnergyProfiles a B).

Proof mechanism: exact finite interior-window purification + COMPACTNESS IN THE ACTUAL ENERGY DOMAIN. Q=norm_form^2+bounded physical quadratic. On norm-one vectors, a finite Q budget bounds form norm. The compact J embedding and closed physical Q sublevel make the normalized physical budget compact; parity and poles are closed. The full correlation map is continuous from physical L2 into pointwise profiles, so its compact image is closed. Native finite purification places every finite mixture in it, and closure costs no phase coherence. No continuous selection of entire factors is needed.

Blind attainment: place smoothPolarBump j strictly inside a and below first integer lag (3*r_j < min(a,log 2/4)). Its value at 0 is 1, hence positive physical mass; normalize. Intersect the compact budget at this feasible source's own energy with all closed blind constraints. Existing lower semicontinuity of extended actual Q yields a minimum; every feasible vector outside this budget has larger energy. Exact poles and prime blindness cancel the non-Gamma terms.

LIMITS: output at completion is an actual form-domain compact L2 source, not claimed smooth or strictly interior. The sign of the attained blind minimum remains OPEN. No RH or Weil-positivity premise, no claim of equality of energy along arbitrary pointwise limits, no converse density theorem for every completed blind source, and no uniform/cofinal aperture result. Do not repeat these proved completion/attainment results as the next frontier.

Audit: both leaf targets built using lake --old build; final sequential lake env lean <each source> exit 0 with NO diagnostics, hashes unchanged and oleans fresh. All 118 referenced Mathlib names checked and explicitly probed with have := @Name in /tmp. All 34 public declarations #print axioms: only propext, Classical.choice, Quot.sound. Both umbrella imports exactly once; no full/umbrella build, computations/experiments, holes, added axioms, heartbeat increases, web/novelty search, or commits by this agent. All 23 owned /tmp/ewu8-* files cleaned.

Global formal lint ran and found nine UNRELATED unwired modules: DeningerMeyerGaussianContourMass, DeningerMeyerSourceSeries, DeningerMeyerXiContourBounds, DeningerMeyerXiContourHeights, DeningerMeyerXiContourQuotient, DeningerMeyerXiContourSource, WeilDilationRayCriterion, HTGeometry.DividedDifferenceCauchyProjection, HTGeometry.EntireDividedDifferenceContour. Preserve concurrent foreign work. No new-module lint error.
