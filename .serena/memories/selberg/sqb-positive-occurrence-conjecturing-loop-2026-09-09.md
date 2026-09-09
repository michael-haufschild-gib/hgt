# SQB positive source loop: current state

RH and full-Xi occurrence remain UNPROVED; goal ACTIVE. User forbids numerical computations and modifying the frontier map. Every turn must state full chain, hardest obstacle and attack. Latest steering: positive conjecture -> analytical proof/fail -> immediate pivot; do not turn failed estimates into more no-go projects. No subagents authorized. One owned foreground Lean/Lake process at a time; collect terminal exit before next. All owned processes from this work have exited.

Authoritative card: docs/drafts/pipeline/1-in-progress/sqb-positive-occurrence-conjecturing-loop.md. Formal report: docs/drafts/pipeline/3-formalized/sqb-theta-dilation-correlations.md. Frontier and universal STATUS have peer edits; leave them untouched unless a new route-independent proved law genuinely belongs in STATUS.

## Completed positive Lean source result

New module formal/GaloisForLFunctions/RHTower/SelbergThetaDilationTransform.lean, namespace RHTower.SelbergThetaDilationTransform, 36 public declarations, 394 lines, wired once into RHTower.lean. Imports ThetaCuspTiltFluxSourceWeld, XiCanonicalProduct, Mathlib.Analysis.Convolution. Scratch /tmp/sqb26_theta_transform.lean passed, canonical source check passed without diagnostics.

Phi=actual thetaCuspFullSource. g0(t)=Phi(t/2) exp((rho+1/2)t/2)/2, c=exp(-log(2)/2), g(t)=2g0(t)-c g0(t+log2), d(z)=2-c exp(i z log2). Raw Fourier convention exp(-i z t).
Proved all-plane exponential integrability and exact transforms:
hat g(z)=d(z) xiCent(rho+1/2-2iz).
K(u)=integral conj(g(t))g(t+u); hat K(z)=conj(hat g(conj z))hat g(z).
J(v)=integral conj(g(t))g(v-t); hat J(z)=conj(hat g(-conj z))hat g(z).
Both correlation product identities include all-plane integrability, proved by actual Bochner convolution theorem.
At actual Xi copy rho=beta+i gamma: hat g(-i/2)=xi(rho)=0; both correlation transforms vanish there. At b=gamma/2, hat g(b)=d(b)xi(beta+1) !=0; Re(hat K(b))>0. Uses actual divisor beta>0 and c<=1<2.

Audit: all 36 #print axioms in /tmp/sqb26_axioms.lean, output /tmp/sqb26_axioms.log: only propext, Classical.choice, Quot.sound. Final leaf build `lake --old build GaloisForLFunctions.RHTower.SelbergThetaDilationTransform` PASS (only own leaf rebuilt), output /tmp/sqb26_leaf_build.log. --old was needed to use existing dependency artifacts; ordinary transitive preflight /tmp/sqb26_build_preflight.log found 16 unrelated stale dependency roots. This is NOT fresh audit of whole dependency source tree. --old preflight /tmp/sqb26_build_old_preflight.log showed sole own leaf pending. No full/umbrella build. Index regenerated. Scoped whitespace check passed. Global `scripts/formal_tools.py lint` FAILED on four unrelated unwired HTGeometry modules: ConservativeDissipativeConstraints, ConservativeDissipativeFlow, ConservativeDissipativeOperator, ConservativeDissipativeSpectrum. /tmp/sqb26_lint.log. Do not claim global lint passes or modify peer modules blindly.

## Hardest mathematical obstacle

Chain: actual theta source -> normalized native approximate vectors at e=5/4-kappa^2, kappa=(rho-.5)/2 -> actual entire operator approximate vectors at unchanged mu=F((rho/2)(1-rho/2)) -> real-preimage classifier -> critical line -> RH. Native normalized source residual comparison remains missing. Real spectral packet receivers and target classifier already proved elsewhere; do not duplicate them.

Paper construction/card: h_rho(y)=y/2 exp((rho-.5)log(y)/2)Phi(log(y)/2); scaled P_rho,a is complete primitive-row periodization. Mean Xrho, X(s)=xi(s). Dyadic S=2P_a-P_2a has mean Xrho and nonzero E2 pairing (7/4)a^-2 Lambda4 X(rho+4). Q(L)=e^(L/2) S_expL, A Q=5/4 Q-Q''. At Xi q source mean zero. Source admission and full modular Gram are still PAPER, not covered by new module.
Actual paper Gram: <Q(L),Q(M)>=K(M-L)+H(L+M), with H(v)=sum_c phi(c)/c integral J(v-2logc-log(1+x²))/sqrt(1+x²) dx. Full residual norm is G(w''-kappa²w). Need positive normalization and ratio ->0.

Paired Gaussian w=exp(-L²/(2R²))(exp(kappa L)+eta_R exp(-kappa L)): exact 2x2 Gaussian forms (12),(13) on card. At real spectral b, leading cancellation eta0=-conj(m(b))*hat g(-b)/hat g(b), denominator now proved nonzero; m(t)=Lambda(2it)/Lambda(1+2it). But real selected energy retains displacement a²+2iab from full complex target, a=Re kappa. No vanishing residual proved; do not formalize a new exclusion. Exact normalized asymptotic limit also NOT proved.
Safe-half-plane H Laplace candidate: integral H(v)e^-sv = Lambda(2s)/Lambda(2s+1)*hat J(-is), Re s>.5. Need actual totient/archimedean integral weld and continuation to real Fourier line before using global Plancherel. The new correlation mean vanishing supplies source cancellation at s=.5 but not contour justification. Expected amplitude A_g(t)=hat g(t)+conj(m(t))*hat g(-t); real-line norm formula not yet audited/proved in Lean.

Replacement analytical test: alpha=rho-.5; u=exp(-alpha x) integral_x^infty exp(alpha t)Phi(t)dt. Source identity gives u'+alpha u=-Phi. Let q=Phi'/Phi and v=exp(alpha x/2)u/sqrt(Phi). Exact LOCAL pencil:
[-d²/dx²+q²/4-q'/2]v=-(alpha²/4)v-(alpha q/2)v.
Retained linear term prevents claiming self-adjoint occurrence. Weighted domain/tails for v and any coercive source comparison remain unproved. No conditional receiver added. Need attack actual arithmetic comparison, not package this missing condition.

## Corpus searches / leads inspected

Broad OR discovery files /tmp/sqb26_{gram_discovery,positive_lift_search,source_phase_search,lee_yang_search,positive_kernel_search,theta_positive_search,oscillation_search,bessel_search,theta_pencil_search}.json. Theta positivity search found actual global reflected Riccati and unconditional 3-point reflected-source PSD; they do not supply full source norm comparison. Inspected ThetaCuspGlobalReflectedRiccati (global angle subadditivity), HedenmalmCenterMixedCorrelationAngle, HedenmalmAutocorrelationPath, PrimeArchThetaBornWittenGroundState (individual source amplitudes with positive curvature), SelbergBesselBoundaryOperator (compact positive boundary correction, no native quotient-core response), HedenmalmThetaEigenODE (forced equation, two tails coincide at Xi zero). Do not treat their missing transports as supplied.

Prior SQB24 closed modules SelbergResummedSource, SelbergNativeConstantMode, SelbergResummedOccurrenceAudit remain complete; do not redo their native mean obstruction. Centered exponential-source exclusion /tmp/sqb25_decay deferred under user steering. Existing memories mem:selberg/sqb-locally-resummed-source-mean-obstruction-2026-09-09 and mem:selberg/source-density-and-invariant-carriers-2026-09-09 contain prior/peer context.
