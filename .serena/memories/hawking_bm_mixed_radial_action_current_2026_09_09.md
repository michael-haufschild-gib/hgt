# HB mixed Einstein radial current; direct pulse-horizon cancellation test

Goal ACTIVE: unconditional RH via literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. RH and full extinction UNPROVED. Frontier map READ ONLY; no computations; one owned foreground Lean/Lake process. User demands conjecture→proof/fail/pivot attacking hardest cancellation, no no-go packaging, no generic infrastructure unless required by a specific source proof. No agents authorized.

NEW INSTALLED/AUDITED leaf `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMMixedRadialActionCurrent.lean` (181-ish lines). Namespace `RHTower.D4BMMixedActionCurrent`; only public theorem `mixed_radial_action_current` line163. Four public defs: actionCurrentPath, actionSymplectic, mixedMatrix, mixedJet. Imports CoordinateEinsteinActionVariation and BMBackgroundMetricTwoJet. RHTower import at14910. All dependencies read from existing cache; do NOT re-audit old modules.

Proved actual Einstein symplectic current, not an assumed bilinear form: actionCurrentPath(J,H,K,a,t)=volumeRatio(J.metric,H.metric,0,0,t)*EinsteinActionBoundary.current(affine J H t,K,a). actionSymplectic is derivative at0 in H minus derivative in K. Private helpers differentiate actual inverse, linearized connection, current and volume. Mixed connection variations commute and cancel. Evaluating full contraction on original BM metric gives
(r²/y²)*actionSymplectic(bg,h,k,r)=sum_A[h_tA*(∂t k_rA−∂r k_tA)−k_tA*(∂t h_rA−∂r h_tA)].
All mixed first metric jets free; all angular first slots retained. Second metric jets irrelevant to this current. Final theorem takes actual ExteriorPoint and discharges r/y/f nondegeneracy internally; no equation/inverse/extinction premises. It does NOT integrate physical endpoints, identify causal response, or supply SS/VV.

Paper card: `docs/drafts/pipeline/3-formalized/hb-mixed-radial-action-current.md`. Active card `.../1-in-progress/hb-radiative-source-period-attack.md` now points to direct tensor test. Do NOT return to scalar norm/normalization, clock positivity, generic Green machinery, or re-prove this current; next actual target is causal pulse contribution to same SV–SV amplitude coefficient.

Analytical source/horizon result (NOT yet formal actual-field/horizon/integral theorem): let s=physicalRate, t=-s-3, k_s=s(s-1)/4; A_s=fullAngularCovector, J=fullSquareCovector. F_s(r)=a²*(1+1/r)^(2s)*(A_s−k_s*J/r²). Stream Psi_s=chi(v)*exp(2s*v)*F_s(r), chi=Real.smoothTransition, v=static time+tortoise. This is switched PARTICULAR stream; not identified with retarded solution. Actual stream reconstruction in ingoing coords:
h_vA=exp(wv)[(chi'+w chi)F_A+f chi F'_A], h_rA=−exp(wv)chi F'_A, w=2s, f=r²−1.
Static time/radial curl equals ingoing curl and is −exp(wv)[2(chi'+wchi)F'_A+2r chi F'_A+f chi F''_A].
At horizon X_s=A_s−k_sJ, Y_s=−sX_s+2k_sJ; F_s(1)=a²2^(2s)X_s, F'_s(1)=a²2^(2s)Y_s. Thus increasing-r current:
omega_hor=−a²b²/32 exp(−6v)[(chi'+2s chi)(chi'+(2t+1)chi) dot(X_s,Y_t)−(chi'+2tchi)(chi'+(2s+1)chi)dot(X_t,Y_s)].
Outward horizon orientation reverses this sign. Angular dot is component products; no angular integral/cusp boundary suppressed.

Let e=(s+1)(s+2), B_s=(2s+3)dot(X_s,X_t)+2k_t dot(X_s,J)−2k_s dot(X_t,J). Cchi=∫_0∞exp(−6v)chi², Dchi=∫_0∞exp(−6v)(chi')². Both converge; IBP gives ∫exp(−6v)chi chi'=3Cchi. Integrated horizon formula:
−a²b²/32 * [(Dchi−(4e+7)Cchi)B_s +4Cchi(s*k_t dot(X_s,J)−t*k_s dot(X_t,J))].
Key insight: actual metric reconstruction yields squared onset derivative Dchi, absent in scalar master Wronskian. Its coefficient, NOT another normalization, must be canceled by actual pulse response. Algebra for this expansion passed scratch Lean with only propext/Classical.choice/Quot.sound; improper integral and actual horizon trace not formalized yet.

Second scratch-checked coefficient: alpha=(2s+1)(2s+2), beta=(2t+1)(2t+2). Formal spectral-coordinate multipliers X_s=[alpha/(lambda−alpha)−k_s]J, X_t=[beta/(lambda−beta)−k_t]J yield
B multiplier=(2s+3)P_e(lambda)/(16(lambda−alpha)(lambda−beta)),
P_e(lambda)=(e−2)(e−6)lambda²−2(4e³−13e²−36e+108)lambda+4e(4e−3)(e²+28).
Denominator-cleared identity checked by ring. This is a coefficient target ONLY: full theta square/global response have cusp tails; no global spectral expansion or resolvent functional calculus/domain admission proved. Retain original cutoffs/cusp boundary terms. These two polynomial lemmas are NOT installed as standalone leaves.

Important correction: do not cancel different polarization monomials. With independent branch amplitudes (aS,aV),(bS,bV), SV–SV has aS*aV*bS*bV, SS–VV aS²*bV², VV–SS aV²*bS². Unless actual source proves a polarization relation, these coefficients cannot be combined. The immediate conjecture is horizon/pulse cancellation in SAME SV–SV coefficient. Full extinction still needs every sector pairing. Do not fit amplitudes to cancel coefficients.

Existing switched-current onset already retained: `ThetaCuspHawkingBMMixedCurrentCutoff.switchedCurrentSource_eq` says switched tensor =chi literalMixedSource +currentOnsetTensor; temporal/radial onset blocks D/r² and D/(r² f). It is a current-sector extension, not Einstein Hessian of switched first-order metric or causal solution. It does not remove new horizon pulse by fiat. Prior `BMFullSourceOnsetReduction` source identity F=L Phi+R and incoming tail remain valid; see mem:hawking_bm_full_source_onset_reduction_2026_09_09.

Validation complete: scratch final source passed lake env lean. Isolated final lake build exact new module passed28s3jobs, only new leaf compiled, 2630 needed corpus modules frozen by .ilean directImports closure. Lake emitted bootstrap missing temporary dependency-manifest warnings, no Lean leaf warnings. Source/olean/ilean byte equality checked; installed/wired. Final new public theorem #print axioms only propext/Classical.choice/Quot.sound. Index refresh and lint --check-generated passed (existing large-file warnings only), scoped whitespace passed. Source SHA256 b462a5b37c2c2ccf5565775bbc950e3fd298046a361580d3c171065f282b3511; olean eec9eb95691d8771c32f08eb96d53c5e3f232fefa217fde593b75a7ff3e0a526; ilean af58e0d52b49e86cf8d9d44888836f5e778add784d47c2da4cab08bc45b25f08.

Owned scratch `/tmp/hb-tensor-current.hkQs53pt` and isolated audit/frozen caches DELETED; all owned Lean/Lake processes completed. No lingering owned process. No numerical work, full/umbrella/dependency build, frontier-map or STATUS edit. Preserve concurrent tasks' edits.

Lean efficiency lesson: `.neg` / `.sub` after nested matrix/sum derivative can leave huge point-free elaboration/instance mismatch, and `convert!` timed out at1.2m heartbeats. Use generated `.fun_neg` and `.fun_sub` methods (Deriv/Add @[to_fun]) instead; immediate success. Type constant matrix derivative explicitly as ((0:Mat)i j) to avoid fun i j=>0 normalization. Generic weighted-current antisym proof: distribute finite sums, simp_rw connectionMixed_symm and mul_assoc, then ring. Final file contains proof; do not recreate helper infrastructure.
