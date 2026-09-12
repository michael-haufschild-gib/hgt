# HB 0912j: all-height intrinsic contact and exact moment boundary recovery

Goal remains UNPROVED and active. Chain: literal theta-cusp source -> Xi occurrence -> retained spin-two source -> physical causal radial/left-QNM action -> fixed Hawking-clock extinction -> RH. Previous 0912i proved low-height full source survival; 0912h proved high-height survival. No overlap has been proved. Intermediate-height cancellation of the specified complete source moment remains unresolved.

Three NEW leaves are scratch-checked, exact-leaf audited, installed with five audited artifacts each, and wired into formal/GaloisForLFunctions/RHTower.lean. No heartbeat or resource limits changed, no axiom checks, no numerical computations, no umbrella or dependency builds. Exact audits reported 2 jobs each:
- ThetaCuspHawkingBMSourceEndpointPolynomial: 31 seconds.
- ThetaCuspHawkingBMFundamentalBoundaryRecovery: 9.6 seconds.
- ThetaCuspHawkingBMPhysicalSourceContactSurvival: 269 seconds (one owned foreground Lean).
Do not repeat checks of these unchanged leaves.

All new theorem names below are in RHTower.D4BMJointSource.

## Exact retained boundary
Let In=fundamentalJacobiMoment n w s, d=2*s-w, e=w+2*s+2. For Re(w)>-2 and w+1!=0, the original admitted Jacobi recurrences give
2*I0=(d^2+5*e+8)*I2-(e+2)*(e+3)*I4,
(e+d^2)*(e+2)*(e+3)*I4 - (d^4+(6*e+8)*d^2+3*e*(e+2))*I2 = 2*d.
Theorem fundamentalJacobiMoment_boundary_recovery, line 10. NO assumptions e!=0 or e+1!=0. Proof uses recurrences n=1,2,3 and existing second recurrence; two small linear_combination identities retain the boundary without division. Norm consequence fundamentalJacobiMoment_boundary_lower_bound at line 33 gives 2*norm(d) <= weighted sum of norms I4,I2.
PhysicalSourceContactSurvival.physicalFundamentalJacobi_second_fourth_survival at line119: for every q:XiZeroCopy and branch side:Bool, I2!=0 OR I4!=0. Actual d!=0 follows from Im(q)!=0 in all four cases. This is NOT yet identification of two independent physical action channels, and does not exclude A*I2+B*I4=0.

## All-height contact quartic
For actual true/true w=-1-q/2, s=q-2=-2*w-4, v=w+1, -1/2<Re(v)<0.
A=5*v^2+(5/2)*v-3/2,
B=(15/2)*v^4+(81/4)*v^3+15*v^2+(9/4)*v.
nonstationarySourceEndpointPolynomial(v)=30*v^4+81*v^3+80*v^2+19*v-6=4*(A+B).
nonstationarySourceEndpointPolynomial_ne_zero, line12: this polynomial is nonzero on the entire CLOSED vertical strip Re(v) in [-1/2,0], arbitrary imaginary part.
Proof: t=-Re(v) in [0,1/2], y=Im(v). Existing realSourceCoefficient_bounds at u=Re(v)-1 gives P(-t)<=-15/4. ImP=y*(F-(81-120*t)*y^2), F=19-160*t+243*t^2-120*t^3. At ImP=0 with y!=0, F>=0. Factored inequality t*(1/2-t)*(183-120*t)>=0 gives F<=19-(137/2)*t, hence t<=1/3, y^2<=1/2. (t-1/3)*(183-180*t)<=0 gives H=-180*t^2+243*t-80<=-19. ReP=P(-t)+y^2*(30*y^2+H)<0, contradiction. y=0 uses real bound directly. Uses nlinarith only with small factored hypotheses. First scratch only failed guessed Complex numeric projection lemma names; norm_num [pow_succ,Complex.mul_re,Complex.mul_im]; ring fixed it. No heartbeat hacks.

## Original physical contact and fixed onset
PhysicalSourceContactSurvival (147-ish lines), imports SourceEndpointPolynomial, FundamentalBoundaryRecovery, PhysicalNonstationarySource and IncomingPairingEndpoint. All proofs checked with default resources.
- physicalFundamentalSourceCore_endpoint_ne_zero line12: for every actual q and a!=0, fundamentalSourceCore(w,s,a,0)!=0. Exact core0 = 2^(2*s-w)*a^2*(A+B). Uses quartic theorem.
- physicalFundamentalSourceRemainder_endpoint line35: keeps J=1 and K=reducedGreenGradient(physicalRadialFrequency q,s,1); sourceRemainder(s,w,a,1,K,1,0)=core0. Uses actual fundamental connection root and original gradient identity. Needed rfl after simp for local w,s let definitional mismatch; no resource change.
- physicalFundamentalIntrinsicContact_ne_zero line51: core0/(2*(w+1))!=0 at ALL heights for a!=0.
- physicalFundamentalIncomingSlope_factor line64: existing incomingResponseSlope(s,a,1,K,w)=[core0/(2*(w+1))]*continuedOnset(s,w).
- physicalFundamentalIncomingSlope_zero_iff line76: for a!=0, slope=0 iff unchanged continuedOnset(s,w)=0.
- physicalFundamentalIncomingTransport_survival_iff line87: for a!=0, (eventually b->0+, incomingSourceTransport(s,chi,a,1,K,w,b)!=0) iff continuedOnset(s,w)!=0. This is the existing analytically continued Green-quotient spatial derivative and remains valid at target connection zero. Uses existing incomingSourceTransport_tendsto_horizon and nonzero slope. Converse uses exact onset factor in transport definition. Does NOT assert full physical projection, total moment or QNM residue survives. Angular amplitude identification remains necessary.
- physicalFundamentalJacobi_second_fourth_survival line119 as above.
APIs verified in THIS toolchain: Complex.cpow_ne_zero_iff, Filter.Tendsto.eventually_ne, Filter.eventually_const. Numeric projection names are Complex.re_ofNat/im_ofNat, not ofNat_re/im; norm_num avoids guessing.

## Next exact onset target
continuedOnset(s,w)=1/(w-2*s)+onsetCorrection(2*s,w), with original Real.smoothTransition profile. Actual lambda=w-2*s=3-(5/2)*q has Re(lambda) in (1/2,3) for true/true. Existing ThetaCuspHawkingBMOnsetPulseTransform proves onsetPulseTransform(v-w)=1+(w-v)*onsetCorrection(v,w), where onsetPulseTransform(z)=integral_0^1 smoothTransition'(u)*exp(z*u) du. Thus onsetPulseTransform(-lambda)=lambda*continuedOnset(s,w). Nonvanishing at this fixed complex curve is unresolved. Existing real-exponent positivity and isolated-zero theorems do not prove it at fixed duration. Possible stronger conjecture: centered Fourier transform of the exact derivative has only real zeros; UNPROVED, no premise assumed, no substitute kernel or adjustable duration used. Do not rerun generic duration-nearby arguments.

## Search and literature
Six cached research JSON requests inspected candidates/source_arguments; first four also inspected ingredient sets/proof ideas. Broad contiguous; deep moment-system (120s); exact OR Casoratian/Wronskian; deep source contact method (120s); exact OR Laguerre/Hurwitz; exact single smoothTransition. All partial=false; latest snapshot 57,202 files, 738,063 declarations, mostly pending compiler metadata, semantic coverage unmeasured. Second-kind Wronskians supplied recurrence-boundary mechanism but their positiveMomentForm assumptions were not transferred to these complex moments. Deep suggested sets were inapplicable to original source. Last two searches recovered original onsetPulseTransform identity but no applicable complex zero-free theorem.
Broad arXiv biorthogonality search via DIRECT arxiv.org/search sorted newest worked; web engine year+recency queries mostly gave old/irrelevant hits. Sept 2026 primary abstracts inspected:
https://arxiv.org/abs/2609.04012 Polyachenko/Shukhman radial potential-density basis pairs: adjacent basis combinations restore physical tail with tridiagonal Gram; alternative Jacobi bases keep biorthogonality. Possible boundary-adapted projection mechanism, no HB identification. Only abstract read.
https://arxiv.org/abs/2609.07806 Edward/Simpore boundary null control of damped beams: polynomial-exponential Fourier-Jordan moments, noncollision/modal transfer conditions, DESIGNED control; not fixed Hawking-clock extinction. Only abstract.
https://arxiv.org/abs/2609.05632 non-Hermitian Hawking microscopic analogues: biorthogonal flux in Lindbladian model, no actual HB source identification. Only abstract.
Also inspected old abstracts arxiv 2210.15935 (Kerr renormalized bilinear QNM projection), 2401.16790 (positive-P biisometries). No external numerical results or paper premises used.

## Docs, lint and cleanup
Updated ONLY docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md, section 'Intermediate-height source and retained horizon contact' (starts line1286), with exact proofs, limitations, audit status and search/literature. Frontier map READ ONLY unchanged; universal-law-field/STATUS unchanged (no new route-independent conclusion).
Formal lint ran once and exited1: only error was unrelated HTGeometry.InversePowerCancellation unreachable from HTGeometry umbrella, plus existing large-file warnings. New HB leaves had no lint errors. Do not edit/rebuild concurrent unrelated module.
All owned Lean/Lake/search/lint session handles terminal before cleanup. Final physical exact audit session33999 exit0, scratch50997 exit0. Cleanup completed: removed 15 explicit owned /tmp/*0912j* paths after verifying all three installed sources matched their passed scratch files, fifteen audited artifacts existed, each umbrella import occurred once, and no owned Lean/Lake process remained. Other agents' processes were untouched. No Git or launch.sh used.
