# HB actual modular energy domain and full weak angular response — 2026-09-07

RH goal remains active and unproved. Frontier map `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is READ ONLY by user instruction. No STATUS edit required this turn. Full chain: literal theta cusp → Xi occurrence → retained spin-two source → physical causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

## Verified new result
Actual complete modular form domain V is constructed; scalar projection J:V→L²(mu) proved continuous, dense and injective. No domain/density/closability premise is supplied. Associated self-adjoint form operator gives a unique finite-energy weak response to COMPLETE cusp-subtracted mixed Einstein forcing F at EVERY actual Xi occurrence, BOTH branches. This closes the actual domain and weak-response gap, not the remaining smooth reconstruction/causal physical bridge.

Five canonical leaves under formal/GaloisForLFunctions/RHTower, namespace RHTower.D4BMModularCore:
1. ThetaCuspHawkingBMSmoothModularPeriodization (4 public theorems)
2. ThetaCuspHawkingBMSmoothModularCore (7)
3. ThetaCuspHawkingBMModularWeakDerivative (4)
4. ThetaCuspHawkingBMModularEnergyDomain (7)
5. ThetaCuspHawkingBMGlobalAngularWeakResponse (7)

Proof card: docs/drafts/pipeline/3-formalized/hb-modular-energy-domain-and-weak-response.md. Current working card: docs/drafts/pipeline/1-in-progress/hb-global-angular-resolvent.md. Updated corresponding live metric-jet and physical-correction cards, and prior forcing card's remaining obligation only. Frontier map untouched.

## Exact construction / avoid false substitutes
mu = UpperHalfPlane.volume.restrict ModularGroup.fd, native dx dy/y²; Space=Lp ℂ 2 mu.
ChartSmooth f := ∀ z:ℍ, ContDiffAt ℝ ∞ (f ∘ ofComplex) (z:ℂ). Globally REAL smooth, not holomorphic compact support.
periodize f z = tsum γ:PSL2Z, f(γ • z). Proper discontinuity from actual SL2Z action and quotient surjection; local fixed finite sum; rational Mobius action smooth; invariance by reindexing; support inside fdo gives pointwise equality on full closed fd.
CellCompact f := ∃ K compact in ℍ, ∀ z∈fd, z∉K → f z=0. Full smoothCore uses globally modular ChartSmooth CellCompact fields. NO zero modular-side boundary condition.
Interior tests are periodized into full core. Actual modular boundary is mu-null. Distribution test separation on open complex chart + boundary null proves smoothCore_dense.
weightedDeriv v f z = (z.im:ℂ) * fderiv ℝ (f∘ofComplex) (z:ℂ) v, v=1,I hyperbolic frame. Continuous derivatives and local zero germ outside compact core support prove actual MemLp internally.
EnergySpace = PiLp 2 (fun _:Fin 3 => Space). frameGraph f = (fieldVector f, derivativeVector f 1, derivativeVector f I). energyDomain = closure of span of actual frameGraph range. embedding = scalar projection restricted to domain. Explicit CompleteSpace instance unfolds definition. embedding_dense and embedding_norm_le proved.
Native map measure = planar measure restricted to complex cell, withDensity ((1/‖z.im‖₊)^2). Height² cancels density. For all smooth compact g supported in complex fdo, integral D_v f*(y*g) dmu = -integral f*(y²*partial_v g) dmu. Planar IBP only needs field differentiable on test support, so no bogus extension across real axis.
Mass/flux tests are actual L² vectors with internally proved integrability. Their continuous linear constraints have closed kernels containing graph/span/closure. If completed scalar component=0, smooth-test separation for y*each gradient component, local integrability, y>0 and boundary null force both gradients=0. Hence embedding_injective: actual differential graph closability.
CRITICAL: full modular core defines energy closure; interior tests only detect/density. Do not replace domain by energy closure of interior compact tests, which changes modular side conditions.

## Actual operator and response
energyOperator = friedrichsFormOperator embedding, inverse graph of C=J J.adjoint. energyOperator_selfAdjoint uses constructed embedding_injective/embedding_dense.
L=parameter q branch=(2s+1)(2s+2), s=rho−2 or−rho−1, Im L≠0 from existing Xi theorem. Positive form A represents 1−Delta, so physical_resolvent_bijective uses shift 1−L, RHS −F. Preserve sign and shift.
energy_inner_decomposition: inner v h = inner Jv Jh + sum_i inner derivative_i v derivative_i h.
WeakSolution q b h: ∀v∈V, inner v h − (1−L)*inner Jv Jh = −inner Jv F.
weakSolution_iff_gradient: sum_i inner D_i v D_i h + L*inner Jv Jh = −inner Jv F, exact weak form (Delta−L)h=F.
exists_full_forcing_weak_response obtains x in actual operator domain from nonreal resolvent at −F, lifts x=C y to h=J.adjoint y and uses adjoint identity.
full_forcing_weak_response_unique self-tests difference and takes imaginary parts; Im(1−L)*||Jdiff||²=0 and J injective.
weakResponse chooses proved solution; weakResponse_spec is final unconditional full forcing equation, parameterized only by actual Xi copy and branch.
F is original COMPLETE forcing, all Weyl/Fourier/cross/cutoff derivative terms, established prior turn; mem:hawking_bm_full_angular_forcing_and_xi_modularity_2026_09_07.

## Validation — DO NOT repeat these audits
All 8 development scratch modules passed lake env lean with no warnings. Five byte-identical canonical leaf sources passed sequential final lake build <exact module> in cache-only audit package: 2.9s, 8.4s, 11s, 18s, 10s. Only new leaves compiled; old dependency caches reused. Exactly10 new olean/ilean copied after exact source equality and exclusive destination checks. Five leaves wired once in RHTower umbrella; NO umbrella build.
Exactly29 NEW public theorem axiom sets audited ONCE with lake env lean scratch: all and only propext, Classical.choice, Quot.sound, no diagnostics. Never re-audit previous23 or27 theorem batches either.
formal_tools.py index passed; formal_tools.py lint --check-generated PASSED (existing large-file warnings). Scoped source whitespace checks passed. No numerical experiment, no added axiom/sorry/admit/opaque/unsafe/native_decide.
Owned scratch /tmp/hb-modular-core.exXVMm; all owned Lean/Lake/index/lint jobs terminal. Cleanup at end of turn. Preserve unrelated processes and concurrent repo changes.

## Exact next hard mathematical work
Construct globally smooth quotient representative of this ACTUAL weak response and prove its hyperbolic differential equation across modular charts/seams/orbifold points. Build global cusp-cutoff extension (naive chi(y)H0 only cell function, not globally automorphic), assemble chi H0+h, then prove physical causal admission in vector metric, with actual horizon/radial boundary/gauge/left-QNM conditions. SS/VV sectors and independent fixed Hawking-clock extinction remain open. Angular weak resolvent does not alone prove physical causality or RH.
Actual cusp center is rho−1/2, not rotated xiSpectralPoint. Do not discard correction's linear image from original left pairing before domain and boundary terms justify reduction.

## Useful exact Lean repairs
Explicit CompleteSpace energyDomain unfolding closure avoids typeclass timeout. inner_self_im/inner_self_eq_norm_sq sometimes require `simpa using! ...` due instance diamonds. L2.inner_def, not Lp.inner_def. Complex.conjCLE is real continuous linear equivalence; no recalled conjCLM. withDensity_apply in MeasureTheory namespace. ContDiffAt.div for rational Mobius first over ℂ then restrict_scalars ℝ. `change` before rewriting toLp ae representatives prevents coercion opacity problems. `innerSL ℂ x`, `.toLinearMap.ker`, `.isClosed_ker`, Submodule.topologicalClosure_minimal establish closed constraints. LocallyIntegrable.locallyIntegrableOn requires explicit set. `Function.comp_def` handles bundled ofComplex; `ContDiffAt.congr_of_eventuallyEq` expects new=old.
