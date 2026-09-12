# HB original correction boundary exchange — verified 12 September 2026

Goal remains active: literal theta → Xi → retained spin two → actual physical causal/left-QNM action → original fixed Hawking-clock extinction → RH. No extinction/RH proof obtained.

Own log: docs/drafts/pipeline/1-in-progress/hb-extinction-own-research-log.md, entries 28–31; paper card hb-radiative-source-period-attack.md, opening section. Consult these before repeating an attack.

## Closed result
For original physical first source H, full symmetric correction A, independent full symmetric test M:
W0(M) E2(H,A)+W1(H,M) L A = W0(A) E2(H,M)+W1(H,A) L M + D_H D_A Theta(M)-D_H D_M Theta(A).
Theta is original determinant-weighted connection-current divergence. Only original H is on shell. No equation for A or M assumed. Original ingoing mixed correction jet specialized directly.
Complete actual mixed-source discrepancy is cubic linear work plus two exchanged correction/source pairings, two test residual terms and two original boundary defects (WBC on card). Both ++/+- channels and all four polynomial correction slots retained before actual differentiation. Independent scalar/vector amplitudes and all metric weights retained. Local identity, no integrated cancellation.

## Audited files
1. formal/GaloisForLFunctions/HTGeometry/CoordinateEinsteinOnShellPairing.lean, 383 lines, SHA256 64cf3ceb8383e96e2b62d46928fb917e86e66fa5036f817d8874cee221fe44de. New weighted_second_of_value_zero, testCoefficient_first, bulk_second_eq_hessian_and_weights. Previous on-shell statements preserved via shorter specialization. Exact isolated cached leaf audit passed 27s/2 jobs.
2. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMInhomogeneousCorrectionBoundary.lean, 210 lines, SHA256 e3c1114c3085bec97c828ffe290cf0c4152cdcd05645edb95174596439623e2a. Namespace D4BMInhomogeneousCorrectionBoundary. physical_correction_exchange; physical_mode_correction_exchange; original_mixed_correction_exchange. Scratch clean; exact cached audit131s/2jobs.
3. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedCorrectionBoundary.lean,38lines,SHA256 5e149d6677caf3ee90c6cb3f7fef37dfedac11e5c9ae31d559b5f8b048b8495f. Namespace D4BMMixedCorrectionBoundary.complete_mixed_exchange. Scratch clean; exact cached audit86s/2jobs.
Each imported exactly once in appropriate umbrella; no umbrella/full build. Generated index regenerated once; scripts/formal_tools.py lint --check-generated passed (existing large-file warnings). Scoped git diff --check passed. No owned Lean processes remain; foreign processes left alone. No added heartbeat/depth/transparency settings, axioms, #print axioms, numerical work or commits.
Logs/scripts: /tmp/hb-inhomogeneous-onshell-pairing-{audit.py,audit.log}; /tmp/hb-inhomogeneous-correction-boundary-{audit.py,audit.log}; /tmp/hb-mixed-correction-boundary-{audit.py,audit.log}; /tmp/hb-correction-boundary-{index.log,lint.log}. All handles terminal; no live sessions from this work.

## Actual left interface / next mathematical attack
Do not identify a second original Xi source mode (which closes L M) with actual physical left reader. D4BMMixedActionCurrent.mixedJet has second slot0 intentionally: action current needs only first metric jet. streamMetricJet uses stream two-jet, so cannot justify actual full Einstein residual from placeholder second metric slot.
Original left stream is exp(-w*time) times radiusLift(tortoiseMode outer w physicalRadialFrequency) times literalVector. Keep opposite time phase -w and original w² radial equation. Full metric field needs third radial derivative of radius lift c=rY(tortoise r): c'''=[rY'''-3(r²+1)Y''+8rY']/(r²-1)^3 (paper LJ, not Lean yet). physicalTortoiseMode_hasDerivAt in BMPhysicalRadialModeMatching gives Y'=Y1 and Y1'=(w²-lambda angularWeight²)Y on original response band. Differentiate actual smooth potential to produce third derivative. D4BMVectorStream.cosmological_component expresses full Einstein residual through master/masterFirst; inspect exact signature before use. PhysicalModeAction angularJet_operator gives lambda times literal coexact field. Existing StreamMetricEinstein theorem applies specific envelope/power field, not automatically physicalLeftModeStream.
Even after L M=0, must prove actual causal corrections' derivative admission and integrated correction/source cancellation with all original horizon/cusp/characteristic/source-contact common limits. WBC alone does not imply extinction.

## Research
Three full-index searches completed partial=false: original-correction-boundary-exchange-deep (57354 files), causal-correction-symplectic-methods (57360), physical-left-complete-metric-jet-deep (57362). Results in formal/.lake/hb-extinction-scratch. Most compiler metadata pending; adopted lemmas tested in Lean. Broad current arXiv abstract screening recorded on card; no external theorem/positivity premise imported.

Shared tree active: preserve others' RouteE, Steinhaus, angular/vector-vector leaves and umbrella edits. Never broad-build to resolve unrelated work. Wait process terminal before reading JSON/mutating dependent files; don't restart on wait timeout.