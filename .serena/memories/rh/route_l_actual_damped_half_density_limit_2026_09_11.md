# Route L C43 closed; next C44 weighted admission / original boundary

Date 2026-09-11. Root /Users/michael/Documents/code/hgt, Lean cwd /Users/michael/Documents/code/hgt/formal.
RH UNPROVED; persistent /goal ACTIVE, no token budget. Do not mark complete/blocked. The last get_goal in this turn reported 9,280,140 used tokens, before C43 implementation. No token usage report required.
Proof chain: complete original Green/BV source -> agreement with fixed physical reader -> conormal vanishing -> RH. C43 constructs an actual weaker source; original boundary admission and reader agreement remain OPEN.

## Critical work rules
Never run #print axioms or substitute print audits (user explicitly banned). None run.
One foreground Lean process per agent; lake env lean scratch, lake build exact leaf only final audit. No full/umbrella builds, numerical experiments, #eval/native_decide/decide, added axioms, sorry/admit. Standard symbolic norm_num/ring used. No commits/pushes/subagents. Shared repo has many other live user tasks; preserve their changes and processes.
Session-init/Serena/manual/mission already done earlier; don't redo wholesale.
Every turn state chain/hard obstacle/last advance/next attack, commentary within60s.
Whole corpus research/deep/method plus broad single-word recent arXiv searches; inspect all candidate/source hits and partial/coverage. Do actual conjecture-proof/pivot work, no search-only packaging.
STATUS entries route-neutral Must/Cannot knowledge.
Avoid oversized/truncated outputs. Use exact sections/fields. STATUS contains enormous paragraphs; never print matching paragraph wholesale. Read exact lines with capped length.
No owned Lean/research/lint/index process remains after this turn.

## Previous work already closed
C41 DeningerDampedPrimeCircleContraction: actual damped prime source, reflected mate, Mellin multiplier A, original circle residual r. Normalized r/A strictly contractive open strip for a>=0; actual repeated prime circle traces ->0 while every finite Gamma/flux discrepancy remains nonzero.
C42 DeningerDampedPrimeMellinGrowth: for a in[0,1], each prime contributes |A(-4)/A(rho)|>=217/128. Full actual normalized source fixed M(-4) diverges as list length->infinity. Original Meyer compact escape/no limit for prime prefixes, repeated factors and explicit a_n=1/(n+1). See mem:rh/route_l_damped_fixed_negative_mellin_growth_2026_09_11. Do not redo.
C38-40 actual finite Green/Mellin source, full Xi/Green/Tate/Sonin transport, original Meyer cofinal escape all closed. C40's old unrelated lint blocker resolved before this turn.

## C43 COMPLETE: actual L2 source, NOT proposed inverse-series wrapper
New module formal/GaloisForLFunctions/RHTower/DeningerDampedHalfDensitySourceLimit.lean.
486 lines,25 public theorems+10defs+1abbrev=36public declarations,7private lemmas.
Imports C42, L2MellinUnitary, Mathlib.Analysis.SpecialFunctions.Log.Summable.
Wired once at RHTower.lean line3117, after C42.
Card moved to docs/drafts/pipeline/3-formalized/route-l-damped-half-density-source-limit.md.
Frontier, STATUS, C42 card and all three former C43 links updated; C44 successor created.

### Exact proof
Weighted embedding H_c(g)(t)=exp(c*t)g(t), via ORIGINAL strong-log->Meyer facade->weighted Schwartz->Lp2.
Exact source flow:
H_c(T_d g)=exp(c*d) * repository additiveTranslation(-d)(H_c g).
Repository additiveTranslation(b) acts f(t+b). Paper U_d acts f(t-d); signs opposite.

At halfdensity c=1/2:
q=exp(-(a+1/2)*L).
D=Id-q*additiveTranslation(L); M=Id-q*additiveTranslation(-L).
Literal paired original source conjugates to D comp M. M=D.adjoint, proved from actual measure-preserving translations.
Energy identity:
Re inner f (E f)=||M f||^2>=0.
For q<=1:
(1-q)^2 ||f|| <= ||E f|| <= exp(2q)||f||.
||E f-f|| <=3q||f||.
No probability normalization or supplied source agreement.

F_N=H_1/2(C42.actualSource a (GaloisForLFunctions.primesLE N).toList).
Actual source step (at N+1 prime apply E, otherwise identity) proved through exact whole Mellin injectivity and Finset.prod_map_toList, retaining original prime presentation.
w_a(n)=if n.Prime then n^(-(a+1/2)) else0.
For a>1/2, w>=0, w<1, summable by real pseries. Sum indexes n>=1 implemented k+1.
B_a=exp(2*tsum_k w(k+1))*||F_0||.
||F_N||<=B_a; increment <=3*w(N+1)*B_a.
cauchySeq_of_dist_le_of_summable => actual Lp2 convergence.
Chosen limit uses subtype a:{a:Real //1/2<a}, no extra convergence hypothesis.
Quantitative distance to limit bounded by tsum_k 3*w(N+k+1)*B_a.
Lower factor R_a=exp(tsum_k log(1-w(k+1)))>0; finite lower product and Real.hasProd_of_hasSum_log give
R_a^2||F_0|| <= ||limit||.
Original weighted reflected Gaussian nonzero, proved from Schwartz representative ae-zero->continuous zero->value at0 contradiction.
Therefore actual limit nonzero for every such a.
Closed concrete theorem deningerDampingOne_original_source_limit (no mathematical premise):
exists h:actual Lp2, h!=0 and H_1/2(original source 1 primesLE N) -> h.

### Scope limits
This is an actual unnormalized ORIGINAL finite Gaussian source limit. C42's sources were Xi-normalized; don't silently identify the two normalization limits.
Actual pointwise weighted L2 embedding and unquotiented L2 carrier, not separate quotient halfdensity L1 completion.
No operator-norm product/inverse arithmetic-series theorem, no infinite positive-operator theorem; only exact positive finite factor energy and actual nonzero vector limit.
No literal Mellin readings of the LIMIT yet, no full XiHilbert packet of limit, no original complete Green/BV boundary or fixed-reader agreement, no zero-damping continuation, no RH.
Original Mobius B,C inverse-series proposal now explicitly left optional in card, replaced by direct whole-source Cauchy proof. Never transfer normalized Mobius average without restoring squarefreeMobiusTotal.
Native Tate depth/copy transport is separate from original prime factor count.

### API lines in final module
30 abbrev DeningerHalfDensityL2=Lp complex2volume
32 deningerStrongLogWeightedSchwartzLM c
41 deningerStrongLogWeightedL2LM c
46 weightedL2LM_flow
66/71/76 halfDensityPrimeFactor/Mate/PairedPrime
81/95 exact halfdensity factor/mate
108 deningerStrongLogHalfDensity_paired
~139 PairedPrime_norm_bounds
~167 PairedPrime_increment
~200 halfDensityPrimeStepWeight and summability/exp identification
~263 DampedHalfDensityPrefix and exact step
~295 Prefix_norm_le
~310 NormBound, Prefix_uniform_bound,Prefix_cauchy
341 DampedHalfDensityLimit (subtype parameter)
344 DampedHalfDensityPrefix_tendsto
348 DampedHalfDensityPrefix_error_bound
~379 LowerFactor,Limit_norm_lower
~401 Prefix_zero,Gaussian_ne_zero
418 DampedHalfDensityLimit_ne_zero
428 deningerDampingOne_original_source_limit
~455 PrimeMate_eq_adjoint
472 PairedPrime_energy
481 PairedPrime_energy_nonneg
Use rg for exact lines beyond verified listed ones.

### Verification FINISHED, don't repeat
Final successful scratch body check6:
lake env lean /tmp/route_l_c43_halfdensity.lean
session47301 exit0; /tmp/route_l_c43_halfdensity_check6.log empty.
A module overview comment was added after that body check; final leaf checks full file. Scratch file and module now byte-identical.
Leaf lake build GaloisForLFunctions.RHTower.DeningerDampedHalfDensitySourceLimit,
session68224 exit0; /tmp/route_l_c43_halfdensity_build.log ONLY new C43 Built40s,11945 dependencygraphjobs. Existing unrelated warnings merely replayed.
Global scripts/formal_tools.py lint session91050exit0, /tmp/route_l_c43_halfdensity_lint.log ends formal lint passed.
scripts/formal_tools.py index session29038exit0,/tmp/route_l_c43_halfdensity_index.log:
3 generated API docs written, DB3changed0removed.
36publicdecls0crossmodulecollisions; oneumbrellaimport; newcardlinks and targeted gitdiff--check passed.
LEAN_API.md34304 lists explicit concrete theorem.
All scratch/leaf/research/lint/index sessions terminal; owned scratch PIDs33929,33992 confirmedgone. No owned process to kill.
Research sessions14860,97186,70832 all exit0.

### Resolved Lean pitfalls
- U.toContinuousLinearMap accidentally selects finite-dimensional LinearMap API. Use U.toLinearIsometry.toContinuousLinearMap.
- To compare adjoint to e.symm, direct typed calc with e.adjoint_eq_symm works; rw can't match coercion transparency.
- For equality of CLMs into Lp, use apply ContinuousLinearMap.ext; intro f. ext f recursively descends to ae equality, defeating vector equality.
- Keep Complex scalar real: simp only map_sub/map_smulₛₗ/adjoint_id/hU then use explicit Complex.conj_ofReal. Broad simp rewrites real exponential to complex exp and loses easy real-conjugation.
- Parenthesize product body (1-w(k+1)); without parentheses Lean parses product of1 then subtracts a FREE autoimplicit k! Kernel failed actual intended induction and we fixed this. Final exact product correct.
- Annotate stand-alone Summable shifted function before comp_injective so +1 inferred.
- Source finset equality via Mellin injectivity: funext s; dsimp only before rw.
- Real.log ((n+1:Nat):Real), not ambiguous Real.log(n+1), to retain exact natural prime cast.
- Namespace is MeasureTheory.Measure.eq_of_ae_eq.
- Gaussian is GaloisForLFunctions.gaussReal.
- Concrete existence theorem explicitly binds a subtype a and changes to Prefix_tendsto; implicit underscores caused heartbeat timeout. No limits increased.
- Scratch files tail helpers in/tmp are stale draft fragments; final authoritative scratch is /tmp/route_l_c43_halfdensity.lean.

## C44 NEXT: actual weighted source and original boundary
Card docs/drafts/pipeline/1-in-progress/route-l-damped-weighted-source-boundary.md.
NO C44 Lean module or scratch yet.
Next action should implement weighted source admission, not more axiom/check wrapping.
Paper mechanism:
H_c E H_c^-1=(Id-u_p U_-logp)(Id-v_p U_logp),
u=p^-(a+c),v=p^-(a+1-c).
For 1-a<c<a both series summable:
||Ef||<=exp(u+v)||f||,
||Ef-f||<=2(u+v)||f||.
Run same actual-prefix source recurrence in weighted L1 and L2.
Need identify compatible representatives on bounded intervals where change of expweight bounded, then exhaustion. Do NOT transfer L2 through unbounded weight globally.
At a1 domain0<c<1. Weighted L1 convergence gives literal M(s) continuity at Re(s)=c, higher jets via two nearby expweights absorbing t^m.
Then actual Euler product limit M(g_a)(s)=G(s)/(zeta(a+s)*zeta(a+1-s)) on1-a<Re(s)<a, derived from actual source, not its definition.
At a1 every actualXi liesinterior, denominatorfinite/nonzero =>retainedXi readingnonzero. Prove fullpacket bounds/nativeTate/Gammanormalizer/leadingcoeff transport separately.

For a>1,e.g2, weightedinterval contains0,1 => startingregion for ORIGINAL unweighted/reflected integrals. Need derivativecontrol and originalperiodization before completeBV.
At a1 endpoints0,1 outsideabsolute estimate; signedcancellation mayrepair; do not inferdivergence or assumeconvergence.
For a>1 wholeclosedstrip scalarbound: each prime amplitude<=p^-a,
|A_p|<=(1+p^-a)^2, |A_p-1|<=3p^-a.
Thus productuniformlybounded/Cauchy onstrip, nonzerointerior. After literalweightedMellin identity, can carry C39 fullXi/Green/provenance/Tate/fixedSonin transport. Expected image=nonzerolimitmultiplier*oldimage, so doesnotcancelinitialphysicaldiscrepancy. No such infinite transport Lean theorem yet.
Dampingcontinuation formal halfdensity multiplier1/|zeta(a+1/2+i*tau)|² with2pi scalematched. Encounteredzeros requireactualsingularsourceprescription retainingmultiplicity/leadingcoeff. No uniformbound excludingpoles asproducer.

## Corpus and arXiv searches this turn
All20candidate+20sourcearguments in each report inspected, includingmethods/coverage/ideas/groups.
1 /tmp/route_l_c43_operator_product_deep.json150s:
generation875394,semantic2354686/2354686,partialsource_refresh.
2generatedideas normedsummability/Schatten diagonal requireownpremises, coupling/Eulerfactor groupunverifiednotadopted.
Used exact mathlib Summable-log-product + Cauchysuccessivedist bodies instead.
2 /tmp/route_l_c43_weighted_pole_deep.json120s:
gen875519,sem2354275/2354825,partialdeadline/filterjudge/source_refresh; emptyideas/groups. No useful directsource admissionhit, rephrased.
3 /tmp/route_l_c44_weighted_mellin_deep.json120s:
gen875564,sem2354579/2354944,partialsame; emptyideas/groups.
Candidate sourcebody NOT yetread/adopted: MeasureTheory.Lp.cauchy_complete_eLpNorm,
formal/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean361-378.
Statement: [CompleteSpace E] hp:1<=p, hf:forallnMemLp(fn)pμ, finiteENNRealtailB with∀N n m≥N eLpNorm(fn-fm)<BN ->existsactualfunctionMemLp limit and normdifference->0.
Obligations explicit; C44 noLeanworkyet.

Broadsingle-wordarxiv factorization/resolvent/damping:
- NoaLavi Sept1 2609.00894 abstract supportordertyperequirements, no transfer.
- A.Chaudhary Sept9 2609.10391 abstract productspectra/symmetricfunctions,no domaintransfer.
- YudaChen Aug26 2608.25458v1 HTML Section3 actuallyread. Weighted/unweightedresolvent equivalenceviaHolder; spectralboundneedsuniformFourierdecayregularlevelsurfaces. No suchRHsourcehypothesisadopted.
- JuanAntonioVegaCoso Aug15 2608.15140v1 HTML intro/III inspected. Resolventdualityequivalenttwistedintertwining, boundaryfluxretained. Doob conjugationactualMarkovmodel,no symmetryorfluxzero transferred.
URLs https://arxiv.org/abs/2609.00894, https://arxiv.org/abs/2609.10391, https://arxiv.org/html/2608.25458v1, https://arxiv.org/html/2608.15140v1.
Cards cite, eachsummary<200words/source.
Previous C41Sept8Chebyshevpaper source remainsdocumentedbutnotreread.

## User-facing ending
Last commentary said C43leafpassedonlynewmodulebuilt; actualweakersourceexistsnonzero; nextweightedMellin/originalBVthenfixedreader.
Final should be brief,selfcontained: RHunproved,chain,C43actualnonzeroL2source+quantitativebound,verificationpassed,hardgap+nextC44link. Don't markgoalcomplete or assumeBVinfiniteadmission.
