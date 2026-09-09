# HB: actual theta mixed-source onset reduction

Goal remains unconditional RH via literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. RH and the complete physical Peierls extinction remain unproved. Frontier map is READ ONLY. No computations; analytical work only. Latest user demands conjecture→proof/fail/pivot targeting the hardest cancellation, no more no-go packaging or generic infrastructure.

Installed one new audited leaf: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullSourceOnsetReduction.lean` (371 lines, 21 public theorems). Main theorem `RHTower.D4BMJointSource.timeOriginalForcing_full_onset_decomposition` at line352. It quantifies over actual Xi copies, source branch, amplitude, real times and UpperHalfPlane point; no inverse/PDE/extinction premise. The source is the full unprojected SCALAR POTENTIAL of the SV/mixed stream; do NOT claim full SS/SV/VV Einstein pairing is closed.

Paper record `docs/drafts/pipeline/3-formalized/hb-full-source-onset-reduction.md`; active card `docs/drafts/pipeline/1-in-progress/hb-radiative-source-period-attack.md` now points to it.

Exact result. Let s=physicalRate q branch, alpha=(2s+1)(2s+2), k=s(s-1)/4, u=-tanh t, z=1-u², r=a²(1+u)^(2s), b=r*u, ell=-k*r*u³, Q=fullSquarePotential q, H=fullAngularField q branch. The EXISTING global angular inverse satisfies Delta H=alpha(H+Q). With psi(v)=smoothTransition(v)*exp(2s*v), v=tau+t, Phi=(bH+ellQ)psi, original time source F satisfies
F=L Phi+R, R=2(b'H+ell'Q)*chi'(v)*exp(2s*v).
L is actual time/radial/angular wave. Lean expresses L Phi as sum of waves of two constructed summands, retaining actual derivatives and angular inverse/cutoff terms. The actual scaled field `timeAngularSeedField` is -alpha*b*psi*H. `fullSourceOnsetPulse/alpha` is R. Pulse support is ingoing strip 0≤tau+t≤1, NOT spacetime compactness. Source/frequency stay independent.

Key free-w identity checked against original reducedPolynomial:
reducedPolynomial(s,w,u)=-alpha(1-u²)u + s(s-1)/2*(w-2s)*(1-u)*u²*[3+(2s+3)u].
The steady angular inverse and two-factor radial construction ALREADY existed in BMFullAngularMasterCurrent; new result is original actual time-domain onset remainder, not rediscovery of the steady inverse. We found this during prior-research checks and reused it.

Exact generic polynomial field Qseed=-alpha*u-k*(alpha-lambda)*u³ is differentiated twice in new module. Its wave equals (alpha-lambda)*originalForcing + explicit (w-2s) pulse. Global theta assembly uses lambda=alpha and existing H. No new angular inverse assumption. Alpha nonzero is discharged using xi_resolvent_parameter_nonreal from BMQuadraticMixedCurrent (physical_parameter_nonreal in BMGlobalAngularWeakResponse is PRIVATE).

Hard remaining target: actual 2 Ω(B(p,p)/2,B(m,m)/2), ALL tensor channels and endpoint terms. The constructed field has an incoming horizon tail; cannot remove L Phi from Peierls pairing by fiat. ANALYTICAL, not yet Lean: at fixed v and t→-∞,
Phi→a²*2^(2s)*(H-kQ)*chi(v)*exp(2s*v).
The real next primary test is whether the physical pulse response and this explicit horizon contribution cancel in full tensor action. Need actual SS/VV corrections and boundary/left action, not scalar mode normalization or another no-go.

Analytical observation available for that direct test: opposite rates s'=-s-3 have same A=(5s²+15s+4)/4, and alpha=6k+2A. Thus alpha'-alpha=6(k'-k)=6(2s+3). Not installed as a theorem; use only if it enters actual H/resolvent horizon pairing.

Adjoint exploration (DO NOT prioritize as new infrastructure): true scalar radial formal left mode is at the same w. Reflected w'=-w-3 solves a different squared-frequency equation. Paper norm N(w)=Gamma(w)Gamma(1/2)/(4Gamma(w+3/2)); first two horizon counterterms for (1/2) integral z^(w-1)sqrt(1-z) are required. N=(w+3/2)(w+5/2)/(2w(w+1))*Beta(w+2,3/2). Primitive Fw=z^w(1-z)^(3/2)[1/w+(w+3/2)z/(w(w+1))] proves finite-part transport. Connection slope=2wN. Integral theorem NOT formalized and Adjoint scratch NOT installed. Do not call that work a complete physical adjoint pairing.

Validation: scratch lake env lean passed; isolated final lake build exact module passed (18s, 3 jobs) using 3980 needed old corpus modules frozen by hardlink and external cache stubs. No dependency/full/umbrella builds. All21 new public theorem #print axioms audits show only propext/Classical.choice/Quot.sound. Source/olean/ilean installed byte-identically; RHTower import wired. formal_tools.py lint PASSED (only existing large-file warnings). Generated index refresh run. No re-audit of previous modules needed.
Hashes: source 513d925f91d119bf6240b75fef600d2dd299330ebc89d17f3503f4f246ce410b; olean e5c6d11efd9ce663104489acfcd64ef695c69dcfe0841a379db8927055173fdb; ilean 05869931b45c79670947af861bc77032edf1184decae20de28ef41561c27c1b4.

Build practicals: frozen caches must include new olean/ilean before lake env lean Axioms since first Galois prefix shadows later paths. .ilean JSON `directImports` rows enumerate dependencies, so freeze only required old corpus closure, not entire repo. Stub old libraries have roots=[], globs=[]; new exact lean_lib has roots=[full.module], globs=[full.module].

Owned scratch root /tmp/hb-left-source.vEIumV1R and its isolated audit/frozen caches were removed. No owned Lean/Lake process remains. Targeted git diff --check passed; generated LEAN_API contains the new terminal theorem and RHTower has the new import. Preserve other tasks' concurrent modifications, including frontier map.
