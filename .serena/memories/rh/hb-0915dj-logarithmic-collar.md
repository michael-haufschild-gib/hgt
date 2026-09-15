# HB DJ: original logarithmic collar comparison

Sole active target: full temporal/metric/QNM matching or impossibility. Neither proved; RH remains open. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Frontier read-only. Never reread computations/results.md. Analytical only. No Git/launch.sh/#print axioms/heartbeat hacks; one owned foreground Lean job. No subagents authorized.

## Closed in this turn
Three leaves passed /tmp scratch lake env lean and isolated exact lake build, now installed and wired in formal/GaloisForLFunctions/RHTower.lean. Whole formal lint passed (large-file warnings only). Audits: OriginalHorizonProductDecay150s, OriginalMetricTraceDecay101s, OriginalMetricLogMatching30s. No added axioms/premises for matching or trace cancellation.

1. ThetaCuspHawkingBMOriginalHorizonProductDecay.lean (162 lines), namespace D4BMOriginalHorizonProductDecay:
- horizon_angular_product_decay: all Fin5 source base jets × Bool reader operations, actual horizonAngularProduct. Every N has G>=0; Re w>=G+1 supplies C>=0 with norm(exp(-wp)*product)<=C exp(-Nk)exp(-p), all p>0,x,k>=0. No w.im condition. Proof uses actual actionRemainder horizon estimate rho0 at N+1; original angularJet bound exp(k); actual three horizonCoefficient bounds exp(2p); weighted reader tails; retains all principal-tail cross terms.
- horizon_forcing_product_decay: both horizonProduct reader operations, same bound for Re w>=1; exact two-field forcing decomposition through fixedProduct (square and half-gradient), actual timeOnset and horizonReader.

2. ThetaCuspHawkingBMOriginalMetricTraceDecay.lean (197 lines), namespace D4BMOriginalMetricTraceDecay:
- horizon_transfer_decay: all Fin4 actual horizonTransfer, N+2 absorbs exp(2k) Laplacian factor; uniform p,x,k bound C exp(-Nk-p).
- horizon_boundary_decay: complete horizonBoundary, both endpoints and four moments, uniform every0<a<=b.
- horizon_source_decay: actual horizonSourceFunctional, from DI horizon_period_bound plus exponential_interval_bound.
- metric_trace_decay: H=horizonSourceFunctional+horizonBoundary has norm<=C_N exp(-Nk), uniformly every0<a<=b. Common derived half-plane for each N. No finite-height H=0 premise.

3. ThetaCuspHawkingBMOriginalMetricLogMatching.lean (96 lines), namespace D4BMOriginalMetricLogMatching:
- original_log_coordinate: (L-A)/2+log(horizonCoordinate(-L/2))/2=log(1+radialUnit(-L/2))-A/2, all A,L.
- original_log_coordinate_limit: limit log2-A/2 from original_radial_log_shift at L/2.
- metric_trace_joint_limit: arbitrary filter, K→∞, arbitrary external positive time intervals => H→0.
- logarithmicCollarDifference: integral_A^L metricDifference/2 + log(e_L)*H/2 - forcingCountertermDifference.
- logarithmic_collar_identity: exact finite cutoff equality with DI fullCollarDifference + ((L-A)/2+log(e_L)/2)*H.
- full_metric_logarithmic_restoration (line72): derivedG, nonrealRe w>=G+1, commonA>0, arbitrary external positive time-interval nets; literal logarithmicCollarDifference→0 as L,k→∞ independently. Preserves canonical forcing coefficient family and fixed log2. This is full RECTANGULAR collar, NOT full static-time/QNM matching.

Own log F277 upgraded to audited result. Own card Current complete-collar comparison updated. No STATUS/frontier changes.

## New analytical moving-corner result F278 — immediate next target
Own fact log F278 and card carry paper identity/bound, not combined Lean yet. Define E(p)=horizonPeriodError(p,k), P_j(p)=horizontal integral of horizonTransfer_j(p,x,k), lambda=mu-2.
U=lambda*(mu*E-P0), V=2*w*U+w*(mu*P1-P2-P3).
Actual complete H(a,b)=U(b)-U(a)+int_a^b V. Compact time admission and new actual decay yield zeroth/first moments on[a,infinity), all a>0. Define K(a)=-U(a)+int_a^infty V; Q(x)=-int_x^infty U+int_x^infty(p-x)*V(p).
Fubini/splitting yields int_R^S H(a,b)db=(S-R)*K(a)+Q(S)-Q(R), a<=R<=S. Exact retained two-endpoint corner. Bound norm Q(x)<=C_N exp(-Nk-x), since integral_x^infty exp(-p)=exp(-x) and integral_x^infty(p-x)exp(-p)=exp(-x).
Original truncated static collar: S=max(a,T-A/2), R=max(a,T-B/2), B>=A. Original half Jacobian gives int_A^B H(a,max(a,T-L/2))dL/2=int_R^S H(a,b)db. Hence mass subtraction leaves cusp-small Q(S)-Q(R) independently of horizon and terminal cutoffs. R=a gives triangular finite part -Q(a)=int_a^infty U-int_a^infty(p-a)V. Do not substitute rectangular external time nets for this identity. Need formal actual U,V admission/decomposition, attach to actual moving metric/forcing integral, join outer region, then canonical QNM action.

## Existing DI/DH/DG facts not to redo
DI: full_metric_collar_joint_restoration with length subtraction audited; actual full metric and forcing radially admitted; OriginalSourceJointContinuity.static_source_radial_integrable proves actual moving upper=max(a,T-L/2) source endpoint/moment admission. Boundary moving admission still needed; OriginalBoundaryRadialAdmission.radial_transfer_joint_continuousAt already gives full joint(L,p,x) continuity, public. Its endpoint_radial_integrable and moment_radial_integrable only fixed time slices. Its private period_time_integrable pattern in OriginalBoundaryRestoration proves horizontal period admission using compact product/Fubini. horizon_transfer_continuous is public, derived half-plane, nonreal, k>=0; positiveTime={(p,x)|p>0}. DI horizon_period_time_integrable public, derivedG, nonreal and k>=0, exp k>=4. SourceRadialRestoration.exponential_interval_bound is public.
OriginalTemporalCorner.triangle_weighted/triangle_defect/triangle_finitePart are PRIVATE; original_leading_triangle_finitePart and original_radial_log_shift PUBLIC. Original leading density has old complete restored physical source/forcing expression; its first moment and log2 match physicalCornerCandidate. Canonical QNM removability already proved DG; do not mistake it for full original matching or zero action.

## Search status
DJ broad OR transgression renormalization, deep retained trace and deep truncated-triangle endpoint primitive mechanism completed. Inspected declarations, candidate_lemmas, source_arguments/methods and proposed ingredient sets. Partial=false; source coverage ~58080 indexed/1failed, compiler metadata largely pending. Deep corner search returns actual OriginalTemporalCorner plus unrelated discrete endpoint differences; proposed ingredient sets unverified. No alternative complete matching producer established by search. Primary broad web transgression/gluing found only2024 papers (arxiv2405.14846,2401.10117), no proof dependency, no2026 claim.

## Lean lessons
Do NOT raise limits. Missing open D4BMGlobalAngularResponse initially made center resolve to abstract algebra center; fixed namespace. For Fin4 fin_cases, explicitly change goal to horizonTransfer ... 1/2 before rw; otherwise generated Fin proof causes instances-transparency mismatch. gcongr positivity on indexed chosen constants needs local hBi:=hB i,hEi:=hE i. Norm exponent damped inequality: use explicit mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC rather than gcongr guessing signs. Exact log limit: h.congr, explicit change, rw[neg_div],ring. All done at default limits.

Temporary /tmp/hb-dj-* files are being cleaned after completed lint; canonical sources and root oleans must remain. No live owned Lean/search handles; all checks terminal exits. Goal stays active, not complete or blocked.