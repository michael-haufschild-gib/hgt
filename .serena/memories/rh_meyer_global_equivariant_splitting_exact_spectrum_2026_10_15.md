# Global actual Meyer source splitting and coherent resolvents

Completed 2026-10-15. User required unconditional structural progress from local Lean corpus; no web/novelty search, no computations, no new axioms, no heartbeat changes, one foreground Lean process, no full/umbrella builds. Preserve concurrent workspace edits; no commits made.

Four new audited leaves, all wired exactly once into RHTower around lines 25843-25846:
1. DeningerMeyerInvisiblePolynomialInjectivity.lean (108 lines)
2. DeningerMeyerGlobalCausalSplitting.lean (259)
3. DeningerMeyerGlobalObservableSource.lean (212)
4. DeningerMeyerObservableSourceSpectrum.lean (221)
All under formal/GaloisForLFunctions/RHTower.

Main insight: K = kernel(actual Meyer -> compact-open Xi comparison) is divisible under every shifted generator by previous actual causal source theorem. Complex polynomial factorization promotes this to divisibility by every nonzero p(X). Principal ideals prove Module.Baer C[X] (Module.AEval' A_K), hence injectivity. Let F be union of all finite causal Xi synthesis ranges. F is A-invariant and F intersect K = 0 (faithful finite full jets). K therefore injects into polynomial module Q/F. Baer extension of identity gives r:Q->K commuting with A, identity on K, zero on all F. P=id-inclusion*r is a global A-equivariant projector with ker P=K, preserving comparison and every Xi jet, and P P_S=P_S=P_S P for every finite causal projector. No global spectral synthesis assumption.

Principal APIs (namespace RHTower):
- DeningerMeyerCohomologyPolynomialModule, DeningerMeyerInvisiblePolynomialModule = Module.AEval' of actual generators.
- deningerMeyerInvisiblePolynomial_smul_surjective p hp; ..._baer; ..._injective.
- DeningerMeyerFiniteCausalModes : Submodule C Q, membership exists finite S, u in range causal synthesis S.
- deningerMeyerInvisible_exists_causalRetraction: exists r:Q ->_C K, r|K=id, r A=A_K r, r|F=0.
- deningerMeyerGlobalCausalProjector; ..._ker; ..._comparison; ..._jets; ..._generator; ..._idempotent; ..._synthesis; ..._finite_left; ..._finite_right.
- DeningerMeyerObservableSource := range P, actual subspace of Q.
- DeningerMeyerObservableImage := range actual comparison.
- deningerMeyerObservation: Q->_C image (rangeRestrict).
- deningerMeyerObservableSourceGenerator := A restricted to range P.
- deningerMeyerObservableSourceEquiv : Source ≃_C Image, via bijective actual comparison.
- deningerMeyerGlobalObservableSection S : Image->_C Q, E S=id and S E=P; intertwines image generator.
- deningerMeyerGlobalObservableOperatorLift B := S B E. Faithful, preserves composition and exact generator commutators; ..._finite recovers all prior finite lifts.
- deningerMeyerGlobalObservableEndEquiv : End_C Image ≃_C-alg End_C Source.
- deningerMeyerGlobalCausalProjector_gaussian_not_finite: P(actual log-Gaussian class) not in F. Uses its nonzero zeroth jet at every Xi point and actual infinite Xi divisor. Thus model is genuinely beyond finite modes.
- deningerMeyerObservableGeneratorWord_kernel L u: W(A_Source)u=0 iff u=P_(support L)u and W(T_(support L)) E_(support L)u=0. Exact all-multiplicity finite resonant kernel, no invisible remainder.
- deningerMeyerObservableSource_shift_bijective_of_xi_ne_zero rho h: A_Source-rho id is bijective. Injectivity: local analytic-unit jet cancellation then ker P; surjectivity: project existing actual causal preimage.
- deningerMeyerObservableResolvent (rho:{rho:C // xi rho !=0}) : Source ≃_C Source. ..._equation and ..._identity: Rrho u-Rtau u=(rho-tau) Rrho(Rtau u).
- deningerMeyerObservableSource_eigenvector rho: actual nonzero eigenvector at each divisor point, final causal chain member.
- deningerMeyerObservableSource_spectrum: spectrum C A_Source = {rho | xi rho=0}, unconditional, line 210.

Scope: algebraic, noncanonical global source splitting for the ACTUAL COMPARISON IMAGE, not full entire proxy surjectivity. K=0/global spectral synthesis remains open. No continuity, boundedness, positive metric, trace comparison, or reflection/dilation compatibility of P claimed. The advance removes the algebraic global extension/ghost ambiguity obstruction for all admitted data and preserves exact finite Hedenmalm sources. Do not sell spectrum alone as novelty: finite causal span could already model point spectrum; the key is whole admitted image and non-finite sources plus compatible global resolvents.

Audit: every leaf passed final lake --old env lean -o <olean> <leaf>.lean with no warnings. Name scratch passed. Separate final scratch imported leaf4; 18 principal #print axioms audits only [propext, Classical.choice, Quot.sound]. git diff --check passed. First global lint found three concurrent HTGeometry MomentHankel modules unreachable; recaptured lint after external updates exited 0, no errors/new-leaf diagnostics (existing large-file warnings). No unrelated edits. Own scratch files cleaned at completion. No full/umbrella builds.

Card: docs/drafts/pipeline/3-formalized/meyer-global-equivariant-splitting-2026-10-15.md.

Lean pitfalls: Submodule.Quotient.eq and mk_eq_zero need explicit submodule parameter before .mp/.mpr. LinearMap.surjective_rangeRestrict (not rangeRestrict_surjective). AEval polynomial sub_smul rewriting suffered instance transparency; instead apply AEval.of.symm.injective, rewrite AEval.of_symm_smul then aeval_X/aeval_C/map_sub. Explicit change beta-redexes before rw. Module.Baer.extension_property h inclusion injective LinearMap.id yields retraction. LinearMap.ofAEval converts C-linear intertwiners into C[X]-linear maps. Verified LinearEquiv.conjAlgEquiv, Module.End.isUnit_iff, spectrum.mem_iff, IsUnit.sub_iff locally.