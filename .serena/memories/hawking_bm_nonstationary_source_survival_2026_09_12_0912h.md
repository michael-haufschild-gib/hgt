# HB original physical source survives above a fixed Xi height — 0912h

Continue after `mem:hawking_bm_exact_physical_source_moment_period_2026_09_12_0912g`. RH remains UNPROVED; goal active. Chain: literal theta-cusp source -> Xi occurrence -> retained spin-two source -> physical causal radial/left-QNM action -> fixed Hawking-clock extinction -> RH.

## Closed new result
Seven new leaves under formal/GaloisForLFunctions/RHTower, namespace RHTower.D4BMJointSource, installed with audited compiler artifacts and wired into RHTower.lean:
- ThetaCuspHawkingBMNonstationaryWeight (exact audit60s)
- ThetaCuspHawkingBMNonstationaryMoment (22s)
- ThetaCuspHawkingBMNonstationaryIntegrationByParts (24s)
- ThetaCuspHawkingBMNonstationaryPolynomial (7s)
- ThetaCuspHawkingBMNonstationaryAsymptotic (31s)
- ThetaCuspHawkingBMPhysicalNonstationarySource (143s)
- ThetaCuspHawkingBMFundamentalSourceSurvival (18s)
All passed lake env lean scratch and exact lake build <module> audits. First isolated audit visited cached dependency jobs and printed only its requested leaf built; later audits2jobs. No umbrella/full/dependency builds. No heartbeat/resource limit increases, axiom checks, mathematical computations, Git or launch.sh.

physicalFundamentalSourceMoment_high_height_lower_bound (Survival line110) proves:
exists H>0, forall q:XiZeroCopy, H <= abs(Im(q)) -> forall a:Complex,
(86/625)*norm(a)^2 <= norm((physicalFundamentalFrequency q true+1)*fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a).
physicalFundamentalSourceMoment_high_height_ne_zero (line162) gives nonzero original source for nonzero amplitude. This is the ACTUAL original finite-part source, not a replacement density or a supplied nonvanishing hypothesis. Does NOT establish full action/pole survival: bounded heights, angular factors/affine Xi collisions, fixed onset, full retained action and Hawking extinction remain open.

## Mathematical mechanism
Use true/true branch: w=-1-q/2, s=q-2=-2w-4; -3/2<Re(w)<-1. v=w+1.
I_n=FP integral_0^1 [x/(2-x)^4]^w (1-x)^n/(2-x)^8 dx.
Phase phi=x/(2-x)^4 monotone. p=phi/phi'=x(2-x)/(2+3x).
T f=(pf)'-f=x*((2-x)/(2+3x)*f'-4*(4+3x)/(2+3x)^2*f).
Original subtraction is retained in exact (w+1)J(f)+J(Tf)=f(1)/5, proved by cutoff FTC and counterterm limit, not by dropping divergent boundary terms.
W(P,j,x)=P.eval(x)/(2-x)^8/(2+3x)^j.
Step(P,j)=X*((2-X)*(2+3X)*P'+(12X-3j*(2-X))*P).
T W(P,j)=W(Step(P,j),j+2). Every Step has factorX. Kernel timesx <=64*x^(-1/2) uniformly on closed strip, so each fixed remainder has a proved uniform integrable bound.
P_n0=(1-X)^n; P_n(k+1)=Step(P_nk,2k). Factor stripping proves P_nk(1)=0 for k<n, P_nn(1)=product_{i<n}(-5*(n-i)). Endpoint constants50 (n2),15000 (n4). No large derivative expansion.
Asymptotic leaf proves existsC>=0: norm(v*(v^3*I2-2/125))<=C, and analogous norm(v*(v^5*I4-24/3125))<=C, uniformly on strip for v!=0.
Actual source coefficients A=5v^2+(5/2)v-3/2, B=(15/2)v^4+(81/4)v^3+15v^2+(9/4)v.
M_a=2a^2(AI2+BI4). Normalized coefficients A/v²,B/v⁴ have bounds9,45 when normv>=1. First corrections have bounds4,75/2. This yields K>=0 with norm(v*(v*M_1-172/625))<=K. Pick R=1+2K/(172/625),H=2R; normv=normq/2>=abs(Imq)/2. Error<=86/625 yields stated positive lower bound. M_a=a² M_1.

## Lean efficiency notes
No new settings except autoImplicit false. Avoid nested inverse mismatch: field_simp normalizes 2+3*x to2+x*3, so supply nonzero fact for normalized spelling. cpow numeral8 required explicit cpow_natCast rewrite; norm_num only did not match. For norm inequalities, normalize all triangle inequalities consistently: norm_num at h1 h2 t1 t2 (and t3), not only some. Use add_le_add le_rfl hb; previous add_le_add_left application reversed operand order here. Prove Measurable explicitly then .aestronglyMeasurable. Preserve low-degree atoms during ring/field_simp.

## Next analytical target (paper candidate, NOT formalised)
Phase coordinate z=x/(2-x)^4 has inverse x(z).
rho_n(z)=(1-x(z))^n/((2-x(z))^3*(2+3*x(z))), theta=z*d/dz.
R=(5theta²-(5/2)theta-3/2)rho2+((15/2)theta⁴-(81/4)theta³+15theta²-(9/4)theta)rho4.
Paper endpoint values R0=-3/32,R1=86/625. Moving source frequency polynomials across the Mellin integral, retaining counterterms and using endpoint vanishing, suggests v*M_a/(2a²)=86/625-integral_0^1 z^v R'(z)dz. Need formalise exact density identity and prove this integral avoids86/625 on -1/2<Re(v)<0, Im(v)!=0. No sign or Stieltjes representation has been proved; do not assume one. Deep inverse-density search confused Lagrange interpolation with inversion; its proposed ingredient set is inapplicable. Exact phrase Lagrange inversion yielded no hits, not evidence corpus exhaustive absence.

## Search/audit/docs
Broad Wronskian and deep Stieltjes/endpoint-asymptotic/inverse-density retrieval inspected candidate_lemmas, source_arguments and available proof_ideas/ingredient_sets. Earlier3requests partialfalse; inverse-density partialtrue with rerankingunfinished; latest coverage57113files,735918declarations, mostlypendingcompiler metadata, semanticcoverageunmeasured. Monotone Stieltjes measures and positive Cauchy transforms must not be conflated.
Broad Pick/univalence primary arXiv abstracts inspected:2607.04377(harmonic Landau bounds),2607.02420(directed univalence), neither used as premise.
Updated docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md, section Monotone-phase source survival. Frontier READ ONLY and untouched. UniversalSTATUS untouched because no new route-independent fact.
Formal lint passed with preexisting large-filewarnings after adding the missing RHTower umbrella import for alreadycompiled ThetaCuspHawkingBMScalarJetQuadraticEinstein (its source unchanged; no re-audit). All7newmodules wired. Lint run twice only because first found this concrete missingimport.
Temporary audit package reused original cached project .olean/.ilean artifacts without dependency sources. Optional .hash/.trace may be absent in legacy caches; don't invent them or rebuild entire closure. Installed only newlyaudited source+5artifacts. Owned0912h scratch/check/search/audit files being cleaned at completion; all owned Lean/Lake/search handles terminal.