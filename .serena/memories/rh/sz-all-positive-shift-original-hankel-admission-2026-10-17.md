# SZ: original arithmetic Hankel admission for every positive shift

The active cross-route goal selects one previously unworked route per turn, with corpus-only evidence, no numerical experiments or extra analytic premises, one owned foreground Lean process, no full builds or heartbeat increases, and a read-only frontier map. This turn selected SZ. The global 44-route/candidate goal remains active.

## Verified positive result

For every omega > 0 and every real aperture a, the literal unsmoothed kernel suzukiSourceHFinite omega (x*y) defines a compact self-adjoint bounded operator on the original RHTower.IntervalL2 0 a. The integral exists almost everywhere for every L2 input. For omega > 1/2 and a > 0, this operator equals the existing suzukiCompressedHankelOperator. No meromorphic-inner, RH, positivity, or unproved analytic premise is added.

This removes the original construction's square-integrable-row admission barrier and admits the entire critical range 0 < omega <= 1/2. Credit is for existence and compactness of the exact original source operator, not the intermediate row estimate. Moving infinite-head Wronskian control, source positivity, all-aperture invertibility and uniform zero-shift cusp passage remain open. No RH claim.

## Files and proof

formal/GaloisForLFunctions/HTGeometry/IntegrableMultiplicativeHankel.lean: 211 lines, 14 public theorems. Integrable profiles vanishing at u <= 1 give bounded Schur operators p(x*y); amplitude truncations converge in operator norm, proving compactness. Real profiles give self-adjointness.

formal/GaloisForLFunctions/RHTower/SuzukiCanonicalPositiveShiftHankel.lean: 163 lines, seven public theorems, namespace RHTower.SuzukiPositiveShiftHankel. Absolute Mellin convergence at s=omega+2 gives local L1 admission of the full arithmetic source. Key names: integrableOn_source, operator, ae_integrable, operator_coeFn, operator_isCompact, operator_isSelfAdjoint, operator_eq_existing, operator_unique.

Both modules wired once into their corresponding umbrellas. Paper proof and conjecture ledger: docs/drafts/pipeline/3-formalized/sz-positive-shift-original-hankel-admission-2026-10-17.md.

## Validation

Both direct lake --old env lean -j1 -o ... <module> commands pass with exit 0 and no warnings. All 21 public theorem axiom audits pass using only propext, Classical.choice and Quot.sound. API scratch checks pass. Default heartbeats. No full/umbrella build. Index refresh passes. git diff --check passes.

Final lint --check-generated exits 1 solely for two concurrently added, unwired modules: RHTower.ArchimedeanResonanceRange and RHTower.EvenSectorBlindMinimumSmallAperturePositivity. Generated-file freshness passes after refresh; 381 existing large-file warnings. Preserve those other sessions' unfinished work. Do not report a global lint pass.

Three deep corpus searches completed partial=false, no errors, 73,118 then 73,119 indexed files; source-only compiler metadata was supplemented by direct Lean checks. All three search JSON files and both Lean scratch files removed and absence checked. All owned jobs ended.

Prior turn PM also removed its exact source admission threshold for every positive damping. Earlier XN, HF, IRK, EGC, OWU and RN turns were attempted without strict contribution credit. Do not mark the full goal complete.