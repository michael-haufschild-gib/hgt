# HB complete-source original joint causal response

RH goal remains ACTIVE and UNPROVED. Do not mark complete/blocked. This batch makes actual formal progress. User frontier map is READ ONLY. Neither frontier map nor universal STATUS was edited by this task; both have concurrent changes. No numerical experiment. No subagents. Broad OR corpus searches first, then AND intersections; spaces default AND.

## Closed current result — do not redo or re-audit

5 new canonical leaves; 28 public theorems;459 source lines.
- HTGeometry.BochnerLaplaceHolomorphy: bochnerLaplaceRay, expRay_smul_norm_le, bochnerLaplaceRay_integrable, bochnerLaplaceRay_norm_le, bochnerLaplaceRay_differentiableAt.
- HTGeometry.HilbertHalfPlaneBoundary: structure CauchyBoundedHilbertMap(value,shift>0,bound,holo,norm_le); namespace methods probe_hardy,line_memLp,lineVector,linePreimage,linePreimage_probe,linePreimage_probe_ae.
- HTGeometry.HilbertHalfPlaneCausal: same namespace causalDatum,causalDatum_probe/support/damping/weighted_memLp/integrable/laplace.
- RHTower.ThetaCuspHawkingBMJointSourceForcedBoundary.
- RHTower.ThetaCuspHawkingBMJointSourceForcedCausal.

Physical namespace RHTower.D4BMJointSource:
c=causalResponseShift q=causalGreenThreshold q+1 >0.
S=causalCuspSourceVector q branch a is full literal source (native square +3 cutoff commutators).
causalCuspLaplace = actual Bochner Laplace of S.
causalJointFrequencyResponse(w) = original waveSpatialResolvent jointEmbedding w (causalCuspLaplace(w)).
causalJointForcedBoundary value(z)=causalJointFrequencyResponse(z+c). All Cauchy/Hilbert/Hardy premises discharged from original source integrability and original inverse bound.
U(t)=causalJointForcedResponse(q,branch,a,t)=exp(c*t) • boundary.causalDatum(t).

causalJointForcedResponse_support: actual AE vanishing t<0.
causalJointForcedResponse_weighted_memLp: expRay(c+1,t) • U(t) is spatial-vector time L² on entire real line.
For Re(w)>c+1, causalJointForcedResponse_integrable/laplace prove absolute original spatial Bochner integral and equality to causalJointFrequencyResponse(w).
causalJointForcedResponse_laplace_original identifies this with jointEmbedding(jointWaveResponse w (cuspResidualVector at onsetTransform(2*physicalRate,w))). No RHS source/inverse supplied.
causalJointForcedResponse_operator: Uhat in actual jointEnergyOperator.domain, A Uhat+(w²-1)•Uhat=actual Bochner Laplace of S.
causalCuspSource_original_joint_response: closed existential capstone with support, weighted L², absolute convergence, original inverse and original operator-domain forced equation; no analytic/causal/response hypotheses supplied. q/branch/amplitude are actual parameters.

Does NOT prove pointwise time regularity, finite propagation, physical meromorphic QNM continuation, advanced/adjoint left residue, retained spin-two/AIME extinction or RH.

## Proof mechanism

Absolute convergence at c bounds source transform on Re>=c. Strict interior margin epsilon gives t exp(-epsilon t)<=1/epsilon and derivative domination, hence vector Bochner holomorphy without time-source derivatives.
Original resolvent operator holomorphy + moving source via clm_apply; sharper mass estimate gives Cauchy bound on shifted family. Every continuous spatial probe Hardy, and one actual vector vertical boundary is L². Probe naturality commutes inverse Fourier. Scalar Paley–Wiener support plus Bochner tensor totality supplies common vector causality, no separability or pointwise operator kernel assumption. Cauchy–Schwarz gives absolute Bochner Laplace convergence for shifted Re>1; all probes identify integral with original frequency vector. Undo fixed source shift; apply previous exact full source identity and original operator graph theorem.

## Validation and installed state — complete

Every canonical new leaf individually lake build <module> in isolated cache-only package, final passes no warnings. Scratch #print axioms exactly28 new public theorems, only propext/Classical.choice/Quot.sound. 5 new oleans only in audit package; all10 installed olean/ilean byte-identical. All5 new leaves uniquely directly wired into appropriate area umbrella. Final source/artifact/import comparison passed. No full/umbrella build.
Small declaration-order issue (docstring before omit) corrected in scratch and canonical; final passes all clean.
Global formal_tools.py lint --check-generated NOT CLEAN, unrelated concurrent work: SelbergMaassTraceRegularized, SelbergModularArcIntegration, SelbergNodalCurvature, FokasLenellsLeftJost unreachable; generated-index drift during concurrent edits. 141 old large-file warnings. No errors against5newleaves. Refreshed indexes again after lint; did not alter unfinished concurrent sources. Do not report global lint passed.

Proof card docs/drafts/pipeline/3-formalized/hb-original-joint-causal-forced-response.md.
Active card docs/drafts/pipeline/1-in-progress/hb-joint-causal-laplace-identification.md updated including all stale next-obligation text.
No frontier edit. No new route-independent STATUS claim justified.

Owned scratch /tmp/hb-forced-response.uicjwktz scheduled for immediate cleanup after memory. No owned Lean/Lake process active. Cached4115 existing owned dependencies via hardlinks, not rebuild. New finalbuilds only5modules.

## Mandatory next direction

State full chain at next turn: literal theta cusp→Xi occurrence→retained spin-two source→original causal response and physical left-QNM pairing→independent Hawking-clock extinction→RH.
Original joint causal response to COMPLETE time source is now constructed and identified. Next work MUST attack continuation of this identified response to the physical QNM divisor and its advanced/adjoint left residue. Do not construct another abstract response or repeat completed source/Green/causal scaffolding. Need original geometry/domain/weighted outgoing spaces before physical continuation; energy branch at Re<0 is not automatically continuation of retarded response. Need source-faithful spin-two/AIME identification and independent extinction after left pairing.

Broad searches this batch:
OR operator convolution Duhamel Hardy resolvent:20061decls4243modules; broad OR Laplace holomorphic differentiable; AND Laplace Bochner:16decls10modules; AND Hardy vector; focused OR causal retarded time dependent BMJoint.
Current full corpus AND resolvent continuation:17decls9modules, no original BM joint continuation theorem found. Focused BMJoint OR left adjoint advanced continuation:5decls5modules, only selfadjointenergy/leftinverse and sourcetimebounds.
Broad OR QNM resonance residue continuation pairing adjoint --module Hawking offset20:843decls190modules. Read first118lines of ThetaCuspHawkingAIMECrossBranchTeukolskyResidue: fixed angular fundamental full boundary Jost residue known; exact massjet -12/(Q+2) nonzero for every Xi descendant, hence nonselective. Its OPEN CORE says coefficientwise second-order cancellation excluded; full third-order ++- projection needed. This does not yet identify joint-source response continuation.
Frontier was concurrently updated to state exactly QNM continuation, left residue, coefficient extinction are current core. Read-only.

## Lean audit/tool cautions

Allnew source autoImplicit false and backward.isDefEq.respectTransparency false.
BochnerLaplaceHolomorphy actually needs no CompleteSpace section (mathlib integral derivatives cover noncomplete); source SpatialSpace complete independently.
Use explicit Integrable.mono hc, not hc.mono (which resolves IntegrableOn.mono set restriction).
Use explicit Filter.EventuallyEq.symm he, not he.symm (can unfold AE into measure-zero equality).
Explicit bind t:ℝ in derivativeintegrands; otherwise negative-coercion parses t:ℂ.
Metric.mem_ball gives dist, convert with simp only[dist_eq_norm].
Place omit BEFORE docstring, not between docstring and theorem.
Original onsetTransform namespace requires open D4BMGlobalAngularResponse/D4BMModularCore as in capstone. Keep autoImplicit false.
Before any dependent build, inspect previous result success. New canonical imports under GaloisForLFunctions need audited artifacts linked into first stable namespace root before lake env lean axiom scratch. LEAN_PATH alone does not override earlier namespace root.
