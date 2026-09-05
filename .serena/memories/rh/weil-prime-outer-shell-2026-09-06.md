# Exact actual outer-shell prime bound, 2026-09-06

ACTIVE unbudgeted RH goal remains unproved; no completion/blocked status. No subagents or computations used. User still requires corpus-first proof/fail/pivot, foreground one Lean process, scratch lake env lean, named leaf final audit, no full/umbrella builds.

New wired leaf: formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPrimeOuterShell.lean (16 public theorems, 2 definitions). Card: docs/drafts/pipeline/3-formalized/weil-prime-outer-shell-partial-isometry.md. Route O current-state paragraph and route-independent constraint updated. Standard axioms only for every public theorem; exact leaf build PASS; formal lint PASS, large-file warnings only. Earlier eight Bellman unwired errors were resolved by concurrent work. All own sessions terminal; do not kill other tasks' Bellman builds.

Source research: prior AutocorrelationChainDamping only scalar two/three-chain bounds; actual CCMRestrictedWeilGroundFrequencyLocalization used ||T(n)||<=2/sqrt(n) and ||finitePrime||<=42exp(a). Existing numerical reports cannot prove all-aperture sign and already show arch-alone/finite-truncation failures; no experiments needed for this result.

Theorems:
- ccmApertureCompression_val identifies the actual adjoint/subtype compression with literal cutoff.
- ccmApertureSymmetricTranslation_coeFn.
- ccmOuterShiftSupport a h = Icc(-a,a-h) union Icc(-a+h,a).
- ccmApertureSymmetricTranslation_sq_val: for h>a, S_h²f=cutoff_outer f, with S_h=P_a(T_h+T_-h)P_a on aperture Hilbert.
- norm_ccmApertureSymmetricTranslation_le_one.
- ccmApertureSymmetricTranslation_eq_zero_of_diameter and ccmPrimeTransportOperator_eq_zero_of_diameter: vanish at and beyond 2a, including null singleton endpoint.
- norm_ccmPrimeTransportOperator_le_outerShell.
- ccmPrimeOuterShellBudget: finite literal sum weight Λ(n)/sqrt(n) with factor 1 if a<log n, factor 2 otherwise.
- norm_ccmFinitePrimeOperator_le_outerShellBudget, ccmPrimeOuterShellBudget_le_naive, ccmPrimeOuterShellBudget_le_twoScaleMass.
- norm_ccmFinitePrimeOperator_le_twoScaleExp: <=21(exp a+exp(a/2)), via already proved massHalf(X)<=21sqrtX.
- exists_polarConstrained_outerShell_eigenvectors: for a<h<2a, two nonzero actual form-domain vectors satisfying both pole constraints have physical embeddings with S_h eigenvalues +1 and -1.
- norm_ccmApertureSymmetricTranslation_eq_one, norm_ccmPrimeTransportOperator_eq_outerShell (exact 1/sqrt n).
- polarConstrained_outerShell_bound_iff: for every real C, the uniform physical contraction estimate over constrained form vectors holds iff 1<=C.

Sharpness construction: b=(2a-h)/4; take existing explicit nonzero constrained smooth source at b; translate form vector by +/-h/2 into a. Their unwanted +/-3h/2 translates lie outside a. S_h interchanges the pair. Pair is orthogonal since h>2b. Sum/difference are nonzero and constrained; opposite eigenvalue signs. Public theorem states actual form-domain vectors, not a formal source-level smoothness theorem.

Conjecture loop: transfer scalar factor-two bound -> prove exact support-square identity; stronger atomwise bound from pole constraints -> false; positive survivor -> exact optimal constant and both signed extremizers plus literal two-scale prime envelope. This does not retire Weil route and is not an external novelty claim for shift numerical radii. The half-diameter equality h=a remains conservatively inner-shell charged in budget. Full-diameter h=2a handled exactly.

Open core unchanged: exclude nonzero constrained zero grounds H_a f=c(p_++p_-) or c(p_+-p_-) from actual source, equivalently all-aperture ground positivity. New norm estimate grows exponentially, gives no complete Weil sign. Further gain needs joint arithmetic/Gamma information, not better independent atomwise constants. A possible next corpus-first conjecture: two distinct outer-shell prime shifts cannot simultaneously attain their individual constrained norm extrema; quantify incompatibility via difference of logarithmic lags, then combine with exact Gamma energy. This is only a lead, not checked/proved.

Scratch /tmp/hgt-prime-shell.7o42tom1/Combined.lean is final exact production copy. Shell.lean and SharpBody.lean assemble it (Shell lacks final module header/imports). Audit.lean imports final leaf, prints all 16 axioms and actual RiemannHypothesis. Lint.txt says formal lint passed. Named command lake --old --log-level=error build GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell succeeded (only leaf rebuilt, cached dependency job count 11308).

Lean lessons: actual CLM scalar norm instances may not unify with norm_smul_le; existing norm_smul_continuousLinearMap_le works. CLM smul_zero sometimes needs ext f then vector smul_zero. .isSymmetric rewrite across local abbrev S failed; make explicit equality inner(S(Sf))f=inner(Sf)(Sf), rewrite hsq there and take symm. abs_sub_le has 3 arguments; use abs_add_le for triangle. Eventually predicates use tendsto_ae.eventually, not Eq.comp_tendsto; functions ae_eq can comp_tendsto. Lp.coeFn_add needs function application exposed by change. Import CCMRestrictedWeilPolarConstrainedSmoothCore explicitly for exists_polarConstrained_smooth_ne_zero; FormTranslation imports only right continuity.
