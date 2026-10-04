# Route RN: global diagonal Ward crossing and Schur-energy peak

Goal ACTIVE; RH not proved or falsified. No subagents. Current sources, not recalled literature, ground this work.

Actual definitions in namespace RHTower.ThetaDiagonalWard: Z=mass=H00/k0²; row g=H0x/(k0*kx); n=ThetaCoordinate.normalizedMixedRow; forcing F=1-g*(1+n)/Z; energy E=Hxx-H0x²/H00. For x>0, F strictly increases, has negative initial limit -ThetaConfluent.centerEntry/k0², strict bounds -n0<F<1, and zero total integral against w=2*x*kx². F has exactly one positive zero, negative before and positive after. E'=-wF and E has a unique maximum on x>=0. F is defined by totalized division at zero; continuity is only asserted on x>0.

New leaves: formal/GaloisForLFunctions/RHTower/ThetaDiagonalWardForcing.lean (15 public theorems) and ThetaDiagonalWardCrossing.lean (14). Both wired into RHTower.lean. Final direct actual-source checks/exports: lake --old env lean <leaf> -o <olean>, sessions28526 and89292 exit0; neither source changed afterward. All29 #print axioms queries in /tmp passed23335, exact closure [propext, Classical.choice, Quot.sound]. Manifest verified29 expected/29 actual, none missing/extra/nonstandard. Forcing has an informational ring hint; Crossing and axioms no diagnostics. No raised heartbeat, computation experiment, unproved premise, added axiom, umbrella/full build or subagent.

Lint46380 exit1:24 unrelated unreachable modules, no own-leaf/forbidden-declaration error. Exact errors saved in rn-singular-weight-conjecture-loop-2026-10-01 working log. Targeted git diff --check passed.

P3 certificate docs/drafts/pipeline/3-formalized/theta/rn-diagonal-ward-single-crossing.md; frontier updated. Main working card docs/drafts/pipeline/1-in-progress/rn-finite-current-integrated-compensation.md.

Next hard problem RN-P-7ah: D=E/kx², z=x*p-1. Prove F-z*D/x²>0 globally, equivalent decreasing D/x². One-crossing E does not imply this. Proposed producer: F strictly concave as a function of z. Since wF and wz are centered, the line joining prefix/tail conditional means passes through origin; strict clock concavity would put (z(x),F(x)) above that line and give desired sign. Actual concavity remains UNPROVED. Write j=1+n and Q=p+x*c=z'>0; exact target Q*(g*j)''-Q'*(g*j)'>0. Retain favorable 2Q*g'*j', rather than demand separate convexity. Expanded target in working card.

Smoothness not missing: M=ThetaJoint.firstLeft 0 x, M'=ThetaJoint.mixed 0 x, M''=ThetaJoint.mixedRight 0 x (ThetaTailJointCenterJets). With d=x*k0*kx and L=1/x-p, j''=[M''-2L*M'+(L²+1/x²+c)M]/d. Hard task is actual signed source comparison/payment, not derivative admission.

Search65550 (clock/row curvature) partial=true, inventory65290, semantic coverage unmeasured/source-only dominant; all20 candidate and20 source statements inspected, no ingredient set. Existing normalizedMixedRow_eq_residual applies, unrelated curvature hits do not. Earlier7933/24629 recorded in card. Actual raw translated rows have opposite midpoint gaps (ThetaTailNormalizedRowCurvature), so uniform raw row convexity cannot substitute; this does not refute centered-anchor clock conjecture.

Build repair lessons: use id_eq in coprod derivative simplification; explicit memberships via by simp, bare le_rfl may fail; whitespace before mass avoids <m matroid notation; unfold mass before row; kernel_two_point_det_pos hx.ne gives nodes0,x. No owned process remains; exact temporary-file cleanup is recorded in working log.