# HB: original physical response equals complete-source endpoint Green integral

Goal RH remains ACTIVE and UNPROVED. This turn is PROGRESS: closes the actual physical response/endpoint Green comparison on the original overlap, not its continuation or residue. Frontier map READ ONLY, SHA-256 preserved. No agents, numerical experiments, full builds, or umbrella builds.

## Installed, audited result
Seven leaves, 20 public theorems + 1 definition, 433 lines:
- HTGeometry.NegativeRayBoundedDerivative (32)
- RHTower.ThetaCuspHawkingBMCompleteAngularSourceBounds (75)
- ...PhysicalResponseDerivativeBounds (58)
- ...JointSourceOuterModeLimits (39)
- ...PhysicalResponseEndpointCurrents (52)
- ...PhysicalGreenSourceAdmission (82)
- ...PhysicalResponseGreenIdentification (95)

For original Xi source/target copies q,r, branch,a and 3/2<Re(w)<2, Im(w)≠0, P is the original physical Hilbert contraction, F=continuedAngularSourceProjection (residual + all three cutoff commutators), chi=physicalRadialFrequency r, H/N original modes and c original connection.

New source-only definition completePhysicalGreenProfile:
G(t)=[N(t) integral(Iic t, H F)+H(t) integral(t..0,N F)]/c.
physicalCuspProfile_eq_completePhysicalGreenProfile proves P(t)=G(t) for every t<0. physicalCuspResponse_ae_completePhysicalGreenProfile proves equality with the original Hilbert response almost everywhere for radialMeasure. No replacement response, boundary-current, integrability, or derivative-bound premise.

Mechanism: all principal |Im chi_i|<3/2, so original Green bounds transfer to continued principal coefficients on the physical overlap. Reduced compact forcing profile bounded; full F bounded. The actual classical equation P''=w²P−lambda*h*P−F and existing bound P give P'' bounded. Reflect a backward unit interval and use corpus BoundedComplexDerivative: |P'|≤4C+M, all t<0 including near0. H,H'→0 at horizon, N→0 and N'→−1 at outer endpoint. The physical trace P→0 plus actual bounds gives J_H→0 and J_N→0. H has exact exponential norm bound C exp(Rew*t), so HF absolutely integrable to horizon; N bounded on each finite outer interval and F bounded give NF admission. Limits of actual finite transport give J_H(t)=integral(Iic t,HF), J_N(t)=−integral(t..0,NF), hence cP=N J_H−H J_N gives G.

## Verification and cleanup
Each leaf passed scratch lake env lean <file>, then individual exact lake build <module> in a private cache-backed audit project. Seven final builds warning-free. Scratch-only #print axioms on all21 new public declarations: exactly propext, Classical.choice, Quot.sound. All21 installed source/olean/ilean artifacts SHA256-matched. Seven unique umbrella imports, none built. One index refresh and lint --check-generated passed; 141 existing large-file warnings. git diff --check passed. No owned Lean/Lake process remains; all observed sessions terminal. /tmp/hb-endpoint-green.wgghbqhk and /tmp/hb-endpoint-green-current cleaned after verification.

Build discipline: use cache-backed dummy Lake dependency stubs to avoid rebuilding thousands of old modules. Own exact leaf lean_lib needs roots=[module], globs=[module]; globs=[] is a no-op. Link audited own new .olean/.ilean into private cached import prefix before scratch axiom audit. Integrable over radialMeasure needs explicit IntegrableOn annotation before .mono_set.

## Current authoritative docs
- docs/drafts/pipeline/3-formalized/hb-physical-response-endpoint-green-identification.md (paper chain, exact scope and audit)
- docs/drafts/pipeline/1-in-progress/hb-physical-response-radial-equation.md (current remaining same-response continuation)
- universal-law-field/STATUS.md F20i-ab extended with route-independent absolute-integral and endpoint-current fidelity rule.
Earlier classical and Dirichlet endpoint cards updated to link the now-closed comparison. No frontier edit; preserve other tasks' unrelated dirty files.

## Next hard mathematical step (proposal, NOT proved)
Continue this same full-source G to QNMs and derive physical adjoint residue. Pointwise meromorphy of F does not continue an improper horizon integral outside convergence. Source decomposition F=M A+sum_i h V_i C_i has principal L_lambda_i V_i=M A_i, hence L_lambda V_i=M A_i+(lambda_i−lambda)h V_i. For lambda_i≠lambda, candidate response = (A−sum_i C_i A_i/(lambda_i−lambda))*G_lambda +sum_i C_i V_i/(lambda_i−lambda), where L_lambda G_lambda=M with original endpoints. Can construct G_lambda from original tortoiseGreen with J=1, K=lambda/2−(s+1)(s+2), minus radialLift; its continuation is available at native coefficient level. Must prove same-response identification and meromorphy, and handle coincident eigenvalues through confluent limits or another exact construction. Never insert global noncollision premise. ThetaCuspHawkingBMScalarCutoffBoundaryValue.scalarCutoffPeriod_weyl proves the matching-root cutoff period is opposite Weyl coefficient times (2k−1), retaining a boundary Wronskian; the coincident channel cannot be discarded. Existing principal equation and continuation are in JointSourcePrincipalEquation, JointSourcePrincipalContinuation, JointSourceTortoiseContinuation. Complete-source pole survival, spin-two/AIME reconstruction, independent extinction and RH still open.
