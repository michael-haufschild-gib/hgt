# HB original incoming Green horizon expansion and full temporal-contact factor
Date 2026-09-11. cwd /Users/michael/Documents/code/hgt, Lean 4.32.2. RH goal remains ACTIVE and UNPROVED.
Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Binding user constraints
NO #print axioms anywhere. Analytical work only: no computations/experiments. Frontier map READ ONLY. No Git or launch.sh. One owned foreground Lean/Lake process at a time. Scratch lake env lean /tmp/file.lean, final exact leaf lake build Module; no full/umbrella/dependency builds. Wire imports. Clean owned temp files/processes. Every new turn state full chain, hardest obstacle, prior actual progress, next attack. Use broad/deep corpus searches and method/source_arguments; directly execute documented research command, no help/implementation reading. No proactive subagents.

## Actual advance
Previous turn integrated the already extracted physical temporal Laurent coefficient, yielding a nonzero Gamma radial factor. THIS work attacks interchange of residue with the horizon finite part of the FULL current.
Six new modules installed, each with exact leaf audit using cached imports only (2 jobs each), umbrella imports wired. Final sources have no new warnings; formal lint passed with existing large-file warnings. Source+5 cached artifacts copied from exact audit (olean,olean.hash,ilean,ilean.hash,trace). No extra axioms checks.
- HTGeometry.NormalizedFirstEndpointMellin (91 lines; audit33s)
- RHTower.ThetaCuspHawkingBMIncomingSourceTransport (200; audit95s)
- RHTower.ThetaCuspHawkingBMLaplaceHorizonGaussBound (87; audit88s)
- RHTower.ThetaCuspHawkingBMIncomingSourceBound (179; audit57s)
- RHTower.ThetaCuspHawkingBMIncomingHorizonExpansion (187; audit92s)
- RHTower.ThetaCuspHawkingBMTemporalContactHorizonFactor (96; audit129s)
All under formal/GaloisForLFunctions/. Do NOT recheck these.

## Exact analytic mechanism / APIs
Let G=continuedResponse(s,chi,a,J,K;z,w), h=z^(w/2)H original incoming mode, S=sourceRemainder(s,w,a,J,K,1,z), O=1/(w-2s)+onsetCorrection(2s,w).
Actual Wronskian: z sqrt(1-z)*(h*n'-h'*n)=-connection/2.
M=firstEndpointMellin(H*S). continuedHorizonMoment=M*O/(-connection).
Therefore Q=G/h has actual spatial derivative
T=M*O/[2 z sqrt(1-z) h²].
Connection denominator cancels exactly. New incomingSourceTransport defines this connection-free expression.
- continuedResponse_div_horizon_hasDerivAt requires Imw!=0, Rew>-2, connection!=0, z∈(0,1), h(z)!=0.
- incomingSourceTransport_analyticAt through connection zeros requires also w-2s!=0, no connection-nonzero premise.
- continuedResponse_div_horizon_derivative_germ derives actual derivative on punctured frequency germ.
- incomingSourceTransport_eq_regular: exact power cancellation T=Mhat*O/[2 sqrt(1-z) H²], Mhat=M/z^(w+1).
- incomingSourceTransport_tendsto_horizon: T→d(w)=S(w,0)O/[2(w+1)].
Physical specializations at both actual physicalFundamentalFrequency(q,side) discharge strip, source-gap, and fundamental mode-nonzero conditions. Correct physicalRate is D4BMModularCore.physicalRate (q−2 or −q−1), not doubled CuspIndicialSelection rate.
 
NormalizedFirstEndpointMellin:
Mhat defined at z=0 as core(w,0)/(w+1).
Remainder norm≤C*z^(Rew+2)/(Rew+2).
normalizedFirstEndpointMellin_sub_zero_bound:
|Mhat-core(w,0)/(w+1)|≤C*z/(Rew+2).
normalizedFirstEndpointMellin_uniform_bound uses beta>-2, beta≤Rew, C≥0 to bound by C*z/(beta+2).
normalizedFirstEndpointMellin_tendsto gives actual right horizon limit.

GaussBound:
horizonGauss_uniform_first_bound: common frequency ball, |H-1|≤CG*z on [0,b].
horizonGauss_uniform_nonzero derives b≤1/2 and 1/2≤|H|≤3/2 uniformly. No assumed horizon mode nonzero.
Proof uses actual Gauss parameter coefficient majorant, nonreal c denominator separation, convergent coefficient tail.

SourceBound:
incomingSourceTransport_uniform_first_bound derives ∃R,b,C>=(0 etc), b≤1/2, all u in ball(w,R), z∈(0,b]:
|T(u,z)-d(u)|≤C*z.
Physical specialization physical_fundamental_incomingSourceTransport_uniform_bound has only actual Xi copy, branch/side, amplitude parameters.
Denominator estimate for D=2 sqrt(1-z)H²:
|D^-1|≤4, |D^-1−1/2|≤(10CG+4)z.
incomingSourceTransport_continuousAt derives spatial continuity from firstEndpointMellin_hasDerivAt.

IncomingHorizonExpansion:
incomingResponseEndpoint(s,chi,a,J,K,w,b)=G(w,b)/h(w,b)−∫0..b T(w,t)dt.
continuedResponse_horizon_quadratic_expansion (line106):
for Imw!=0, Rew>-2, w-2s!=0, ∃R b C, positive R,b, b≤1/2,C≥0, ∀u∈ball(w,R), connection(u,chi)!=0, ∀z∈Ioc0b:
|G(u,z)/h(u,z)−A_b(u)−d(u)z|≤C z².
FTC proof with actual derivative and integrable T. Constant integral bound suffices (C z² rather than sharper C z²/2).
incomingResponseEndpoint_meromorphic (line163):
∃b>0,b≤1/2, AnalyticAt (u↦∫0..b T(u,t)dt) w AND MeromorphicAt A_b w.
Uses actual common uniform bound + spatial continuity + Cauchy-dominated integral theorem. Private helper proves holomorphy on a ball by shrinking around each point, then DifferentiableOn.analyticOnNhd.
IMPORTANT: G is an original Green block, before explicit gradient lift and full physical angular assembly. Do not claim full continuedPhysicalSelfResponse expansion yet.

## New full temporal contact identity
Existing corpus discovery:
reducedPolynomial_affine, reducedPolynomial_horizon, reducedSlope_horizon show both frequency coefficients have a horizon zero.
TemporalContactHorizonFactor defines
reducedHorizonQuotient(s,w,v) =
[reducedHorizonPolynomial(s,v)+w*s*(s−1)*v²*((2s+3)v+3)/2]/(1+v).
Proves reducedPolynomial=(1−v²)*this, using 1+radialUnit(x)>0.
horizonRegularAngularSourceProjection =
sourceAmplitude*reducedHorizonQuotient*scalarResidualPeriod
+sum_{i:Fin3} continuedPrincipalDifference_i*scalarCutoffPeriod_i.
ALL four channels retained.
continuedAngularSourceProjection_horizon_factor (line31): exact F=z*F_hor at every x.
radius_sq_mul_horizonCoordinate: R²*z=R²−1 for x<0.
continuedPhysicalTimeAction_radial_density (line70):
(R²−1) A⁰=[−2w(lambda−2)fg−w*g*F_hor]N.
The apparent extra 1/z in the temporal contact cancels with actual source zero. Uniform bounds for F_hor still require assembly.

## Hard remaining mathematical work
Full-current residue/finite-part interchange remains UNPROVED; so do angular integrated pairing/nonvanishing, all-multiplicity original angular dual, full SS/VV and Peierls identification, fixed Hawking-clock extinction, RH.
1. Derive uniform second-order Gauss and elementary source/lift remainders. New Q expansion applies to each Green block; propagate through actual reducedGreen subtraction and all three principal corrections.
2. For incoming current, with Q=A+d z+O(z²), H=1+h1 z+O(z²),
H²Q/[2 sqrt(1-z)] = A/2 + ((h1+1/4)A+d/2) z + O(z²).
After clearing frequency pole, bound the restored integrand by z^(beta+1), beta>-2.
3. Original normalizable left mode already has exact decomposition:
n=alpha*h+[connection/(2w)]*h(-w).
Read source ThetaCuspHawkingBMOriginalHorizonBasis and OriginalNormalizableHorizonDomain.
The opposite channel yields a logarithmic cutoff term. Establish its frequency regularity from the connection cancellation, retaining its literal coefficient.
CAUTION raw connection*G (and beta*A) at a connection zero is totalized differently from its analytic removable extension. Prove a punctured germ equality to a constructed analytic numerator, not blindly AnalyticAt of the raw pointwise product.
4. Define full current power/log counterterms; include original outer-endpoint bounds; exchange residue with restored actual integral. Recover previous physicalRadialResidueFinitePart Gamma value.
5. Angular/source nonvanishing and causal action identification still substantive afterward.

## Search findings
Broad/deep searches included uniform Frobenius, normalized Mellin, primitive/holomorphic endpoint, Cauchy dominated holomorphy, Taylor remainder Cauchy, --any and --retrieval-views all --max-rounds2. Inspected candidates, methods/source_arguments, proof_ideas, ingredient_sets, coverage. Partial results: last inventory56918files,732101declarations,706466ready methods, incomplete semantic retrieval and pending compiler metadata. Candidate applicability checked in actual new Lean.
Used CauchyDominatedIntegralHolomorphy.differentiableAt_integral_of_cauchy_dominated (source read).
Potential next ingredients READ but not applied:
- RHTower/RiemannGaussian/FiniteToEntireExpandingTaylor.lean:178-193 geometric Taylor remainder; entire premise NOT applicable to Gauss directly. Extract method norm_sub_le_of_geometric_bound_of_hasSum.
- RHTower/BourgainQuadraticTaylorControl: Banach-valued taylor_mean_remainder_bound.
- HTGeometry/HypergeometricEndpointBounds: shift majorant tail again to prove |H−1−coef1*z|≤C*z². Existing gaussParameterMajorant_tail_summable proves shift1 by summable_nat_add_iff then division by radius. Shift2 analogous, tsum_eq_zero_add twice extracts first terms. Parameter neighborhood helper in new GaussBound is private; don't assume callable externally.
Broad arXiv own-word searches Volterra and transmutation were read: arxiv2606.18071 Volterra Generative Models; arxiv2608.10594 Transmutation Timescales, latest Sept7v2. No proof ingredient extracted; no experiment.

## Documentation and cleanup
Updated only working and formalized cards:
docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md
docs/drafts/pipeline/3-formalized/hb-physical-mode-action-contact.md.
Frontier and universal STATUS untouched; new results route-specific.
All owned Lean/Lake/search/lint sessions finished. Cleanup verified no owned Lean/Lake process and removed all 27 owned 0911j scratch/audit/search/lint temporary artifacts.
New source hashes:
NormalizedFirstEndpointMellin 555d643096d48f5b110ba916e3df615ad842c2a9720590621824a01ab69a2d47
IncomingSourceTransport 8b94fdab96481c8259b1137b81b0d1aedcf2e5f45d569a35c94036e5c9118ae6
HorizonGaussBound e25313d2c48a8b8a2768163385b52f70072f419b321e218456e0f1b3571f30a7
IncomingSourceBound 5498d5541996fefc1864ddebbbd85c6ca2458a2e384cc6e276df1f95febd568a
IncomingHorizonExpansion c717aaa3d02f6eaa7cd0ca8e4c2adc8284b89cdc8f9832eb513e16e92393e876
TemporalContactHorizonFactor 141b28a419f5a890e1b75a5bf28a655fdac5f37e013bf7ef32f9a0ac9a14ce27.
