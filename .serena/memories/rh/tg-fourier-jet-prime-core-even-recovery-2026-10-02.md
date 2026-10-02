# TG-C9.4/C9.5 complete; C9.6 next (2026-10-02)

Persistent active goal: unconditional actual RH proof or falsification via TG. RH unresolved, no blocker. No subagents, computations/numerical experiments, new axioms/holes, heartbeat hacks, full/umbrella builds, commits or pushes. One owned foreground Lean at a time. Final audits lake --old env lean. Keep goal ACTIVE. User requires each turn route, hard gaps, assessment of last work, actual conjecture/proof loop grounded in corpus.

## This turn's certified advance
New production leaf formal/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetPrimeCore.lean (375 lines):
- primeBurnolSquareGraphCore_closure (line242): every prime's literal columns (e_pn, M e_pn) span a graph core equal to entire even maximal position-square graph.
- primeBurnolFourierJetPrimeGraph_closure (line302): finite prime two-coordinate source graph closure equals entire even maximal source graph closure.
- mem_primeBurnolFourierJetEvenGraph: exact identification with original E(f,g)=(f+Fg,Mf+FMg).
- primeBurnolFourierJetPrimeGraph_no_bounded_recovery (line355): no bounded ambient R:H×H→H recovering first input even just on one prime's finite literal source graph.

Modified own prior production leaf PrimeBurnolFourierJetClosure.lean:
- added private exact Hermite reflection/even/odd projection lemmas and Gaussian weak-test formula.
- new public primeBurnolFourierJet_no_bounded_even_recovery (line469): excludes R on even maximal-domain source (separate parity proof; does NOT merely restrict full-space negative).
- prior five public results unchanged, all re-audited.

All actual Euler amplitudes retained. No added mathematical assumption. Source family precisely prior literal Burnol columns and radial jet2. Physical L2 product has ordinary product norm; no silent Hilbert structure.

## C9.4 proof details / useful APIs
Imports FourierCompletion, FourierJetKernel, FourierJetClosure. Need BOTH open GaloisForLFunctions.HTGeometry and open HTGeometry: BurnolDepthCompletion definitions are root HTGeometry, maximal multiplication is nested GaloisForLFunctions.HTGeometry.

weightedDepth p n := A_pn^-1 • (literal half-line feature + radialJetLp p n 2).
AE representative weightedDepthFun=(1+r²)*burnolDepthFeature(log p)n.
Its base L2 by actual LP sum/scaling, nonzero r>0; real-valued conjugation. Geometric coordinate power relation gives every integer Laplace moment of weightedBase*g. Integrable by MemLp.integrable_mul. ae_eq_zero_of_integer_laplace_moments kills g. Ordinary weighted-source density proven by orthogonal complement zero.
square_mem_even proves M preserves evenness from reflection AE, no derivative premise.
evenWeightedColumn=(e+Me) in evenSubspace. Exact U identity:
evenWeightedColumn(p,n)=(sqrt2*A_pn) • primeBurnolEvenExtension(weightedDepth p n).
Proof via logEvenUnitary/halfLineExpUnitary AE and pullback through exp. Both Euler depth amplitude and sqrt2 restored.

squareResolvent B uses lpBoundedMulCLM with symbol (1+x²)^-1; norm≤1.
squareGraphParam= B.prod(id-B).
AE inverse gives B(f+Mf)=f on maximal domain; G(f+Mf)=(f,Mf).
primeBurnolSquareGraphCore := span range actual (e,Me).
primeBurnolEvenSquareGraph := M.graph ⊓ evenSubspace.prod top.
Closedness: maximalRealL2Mul_isSelfAdjoint.isClosed and fixed point set of l2Reflection.
Density transported through G using closed preimage, closure_minimal; reverse via closed graph.
jetGraphAssembly((f,Mf),(g,Mg))=((f,g),(f+Fg,Mf+FMg)), continuous linear.
PrimeGraph=(core.prod core).map assembly; EvenGraph=(evenGraph.prod evenGraph).map assembly.
closure_prod_eq + Submodule.topologicalClosure_map give equality after closure.
No recovery on finite PrimeGraph extends by closed equality set {w|R w.2=w.1.1}, then contradiction to even-source theorem.

Lean lessons:
- Scalar cast inverse pretty syntax is inverse of complex cast: norm_inv then Complex.norm_real, not reverse.
- Root mem_closure_image exists, not Continuous.mem_closure_image.
- No isClosed_of_complete name in toolchain; fixed-point set isClosed_eq used.
- Every Submodule→Set cast in product must specify Set (SoninL2×SoninL2), Set _ got stuck.
- change with membership must specify target submodule explicitly; ∈ _ got stuck.
- Before rw squareGraphParam_sum at literal column, change input to (primeBurnolSquareColumn pe : SoninL2), since rw does not unfold that user definition automatically.
- MemLp .congr unavailable; use memLp_congr_ae.
- Actual multiplier API MeasureTheory.lpBoundedMulCLM / lpBoundedMulCLM_coeFn.
- Fourier CLM use .toContinuousLinearEquiv.toContinuousLinearMap, NOT finite-dimensional .toContinuousLinearMap shortcut.
- Serena find_symbol rejects ignored Lean paths. Attempt was made; source insertion used checked exact prefix match with audited scratch, then normal file edits.

## C9.5 parity proof
Actual corpus GaloisForLFunctions.hermiteSchwartz_neg:
h_n(-x)=(-1)^n h_n(x).
hL2_reflection via reflection AE plus Schwartz representatives. evenProjection h_(2k)=h_(2k), odd index→0.
Existing W=C²+B² tail:
W h_(n+2)=4π² h_(n+4)+4(n+1)(n+2)h_n.
Also W h0=4π² h2 from ladder and annihilation0.
Given even-source R, channel h=(0,-(8π²)^-1 Fh), T=F^-1 R channel evenProjection.
For even phi and even Wphi, exact admitted pair(Fphi,-phi) yields T Wphi=phi.
For n even apply this to h_(n+2); n odd evenProjection Wtail=0.
Thus u=T.adjoint h0 annihilates all weak Hermite-tail tests, hence u=0 by old tail theorem.
Gaussian h0 recovery contradicts nonzero norm.
Uses Nat.even_or_odd' n: exists k,n=2k or n=2k+1.
No odd source direction smuggled into even graph.

## Verification / cleanup
Scratch C94 and C95 passed. Both modified production leaves FINAL commands:
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean GaloisForLFunctions/RHTower/<leaf>.lean
Both exit0. Closure leaf no output. PrimeCore emits ONE informational 'Try this ring_nf' suggestion, no warning/error; do not claim completely silent.
Separate /tmp audit imports PrimeCore, #print axioms ALL TEN public results (6 Closure+4 Core); exit0 all only propext, Classical.choice, Quot.sound.
Umbrella RHTower.lean wired near17703; never built.
scripts/formal_tools.py index exit0; API/search refreshed.
Final scripts/formal_tools.py lint exit1 exactly12 unrelated unwired RHTower leaves:
CCMApertureChainProfile
CCMApertureTranslationChains
CCMExponentialRampPrimeMoment
CCMExponentialRampSourceDissipation
CCMExponentialRampTerminalEntropy
CCMRetainedChainKernelLower
MobiusDivisorCriticalLogProfile
MobiusDivisorCriticalLogProfilePrimitive
MoebiusMollifiedCriticalMoment
MoebiusMollifiedErrorThreeLines
ThetaMovingShellFirstOrderPhase
ZetaZeroDensityPowerSaving.
No TG leaf error. Whitespace checks clean (git diff --no-index --check exit1 with no output on new leaves means differences only). No stale owned builds.
ALL owned processes terminal, ALL10 tempfiles deleted via apply_patch:
tg-c94-search JSON, core Lean, axioms Lean, lint log, index log;
tg-c95-parity-search JSON, parity-exact JSON, even Lean;
tg-c96-source-search JSON, neutral-search JSON.
Production matching oleans retained.

## Cards/docs
P3 tg-fourier-jet-prime-graph-core.md new canonical positive result.
P5 tg-fourier-jet-even-bounded-recovery.md new canonical negative+positive survivor.
P1 tg-fourier-jet-even-recovery.md deleted/moved to P5.
P1 tg-fourier-jet-prime-graph-core.md retained as COMPLETED RESEARCH RECORD with canonical P3 pointer, not active task.
P3 tg-fourier-jet-closed-graph.md updated current parity/core result and audits.
Parent P1 tg-fourier-radial-jet-completion.md updated.
Main working log P1 tg-source-conjecture-loop-2026-10-01.md checkpoint updated and detailed C9.4/C9.5 entry appended with final lint exact list.
docs/reports/rh-current-frontier-map.md TG closedgraph paragraph updated core/parity result and next neutral gap.
NEXT ACTIVE P1 tg-fourier-jet-neutral-graph.md (C9.6), fully specified paper attempt below.

## Next hard conjecture C9.6
Do NOT re-search/pivot instead of solving.
Question: on G=closed EVEN E-source graph, equipped with norm retaining BOTH inputs and outputs, does the ORIGINAL neutral N(f,g)=(f,0) extend continuously? C9.5 physical-output recovery does NOT answer this. Necessary for using original bounded projection algebra in TG cubic transgression.

Corpus-grounded candidate obstruction:
Actual audited W=8π²Q²+2D²; E(Fφ,-φ)=(0,-(8π²)^-1 F Wφ).
Use even phi_r(x)=sqrt(r)*exp(iπx²)*exp(-πr²x²),0<r≤1.
Derived algebra (not yet Lean):
Wphi_r=4π(i-r²)phi_r+8π²(r⁴-2ir²)x²phi_r.
Unimodular phase and normalized dilation give ||phi_r|| constant and
||x²phi_r||=r^-2||x²h0||, with base norm>0.
Therefore Wphi_r uniformly bounded as r→0 while Mphi_r grows unbounded.
Exact Fourier identity implies ||M Fphi_r|| grows too.
z_r=source graph of(Fphi_r,-phi_r) stays bounded in G (input+output!) but Nz_r diverges through separate first jet M Fphi_r. No numerical experiment or optimized constant is needed.
C9.4 approximates each coordinate WITH M-image, hence would transfer any finite-prime-core neutral bound to this source family. Ordinary L2 density insufficient.
All chirp Schwartz admission, derivative identities, norm transport, divergence need formal proof; BUILD missing infrastructure rather than effort-pivot.

Required positive survivor before retirement:
N on original separately-admitted even D(M)² source embedded in G is CLOSED and densely defined, idempotent.
Proof: z_j→z and Nz_j→w imply first inputs and first individual M-jets converge; closedness M gives f∈D(M). Subtract first jet from total output, apply F^-1: second M-jet converges; closedness M gives g∈D(M). Limit w=Nz, hence closed graph.
Range/kernel are closed individual source-channel graphs; direct sum dense. Unboundedness implies proper domain/nonclosed sum. Formalize exact decomposition, not just negative bound.
No result here yet certified. Gamma–Xi/Hardy/sub-unit/RH gaps still open.

## Searches/read evidence for C9.6
Documented deep query 'Schwartz quadratic chirp dilation' partial: malformed local filter JSON + rerank deadline. Returned:
- RHTower.ccmNormalizedSchwartzDilation, CCMArchimedeanGeometricScaledKernel.lean23; apply27: sqrt rho*g(rho*x).
- RHTower.schwartzDilate, ArchimedeanMellinFourier.lean636.
- fourier_normalized_dilation, SoninEulerCalkinPartialIsometry.lean67.
- evenFourierTransform_evenDilation, SoninLogCoordinateScattering.lean42.
- gaussianSchwartz / Fourier_gaussian existing HTGeometry/GaussianSchwartz.
No claimed absence from partial search.
Actual mathlib source grep: Analysis/Distribution/SchwartzSpace/Basic.lean738 smulLeftCLM uses Function.HasTemperateGrowth; apply theorem743,748. Need construct quadratic phase temperate multiplier if no existing exact one. Could use complex Gaussian directly if suitable current definition exists; inspect first.
Original deep parity search partial irrelevant semrank; lexical followup 'hermiteSchwartz_even hermiteSchwartz_neg' --any --mode lexical --no-refresh found correct source and proof.
C94 search 'positive multiplication resolvent graph core exponential depth dense' partial returned MaximalMultiplicationSelfAdjoint resolvent (source read, but use existing smaller lpBoundedMulCLM instead).
Exploratory 'prime Gamma Fourier Mellin completed source cancellation transgression' partial returned coPoisson/Mellin laws; these alone were NOT taken as new TG producer. Read ArchimedeanMellinFourier header+coPoisson definition685/theorem692; no need redo these reads next turn.
Remember tools no update_plan/multi_tool_use.parallel available; card tracks plan, functions.exec Promise.allSettled for independent reads.
