# Active unlimited goal: geometric unconditional RH proof/disproof
Never mark complete before unconditional fully formalized RH. Objective attachment /Users/michael/.codex/attachments/b98aa166-7100-44a5-abac-67ea8f93eedb/pasted-text-1.txt; read every continuation. No web, numerical experiments, extra axioms, sorry/admit/opaque/unsafe, heartbeat hacks, positivity/spectral/energy/Fourier/HP route. Actual corpus only; external novelty unverified. No subagents. One owned Lean/compiler/build at a time; inspect terminal status BEFORE starting next. Use lake cwd /Users/michael/Documents/code/hgt/formal, leaf lake build --old +Module only, final actual-source lake env lean. Root filesystem reads prefix formal/; avoid doubling formal prefix when cwd formal. All owned processes terminal at checkpoint; scratch implementation copies removed; audits/logs retained.

Previous central state: mem:research/xi-actual-analytic-completion-2026-10-09. Actual Xi factors analytically through a Hausdorff second-countable noncompact simply connected completed image-cover surface. Any analytic open embedding of that selected surface into C is onto, but EXISTENCE remains unproved. Parent active docs/drafts/pipeline/1-in-progress/xi-capped-surface-uniformization.md. Original target xi-single-mark-infinite-cover-exclusion.md still unproved; RH also unproved.

## Three new fully verified modules, 32 explicit public declarations
1. HTGeometry/FiniteCyclicCoverApproximation.lean (17 declarations), namespace GaloisForLFunctions.HTGeometry.FiniteCyclicCoverApproximation; imports InfinitePacketObstruction.
Sheets n = Option(ZMod(n+1)), x finite translation fixing none, y swap none/some0. finiteStabilizer n at none. Transitive, Nat.card cosets = n+2, always proper. Every fixed word/sheet action eventually agrees with infinite Option Z model after reduction; every finite word set eventually has exactly the same stabilizer membership as infinite proper infinite-index H. Every fixed finite quotient q eventually sees full image of H_n, cutoff depends on q. Not a polynomial monodromy identification.
Card docs/drafts/pipeline/3-formalized/finite-cyclic-cover-approximation.md.
Build /tmp/hgt-FiniteCyclicCoverApproximation-build.log, axiom /tmp/hgt-finite-cyclic-cover-axioms.{lean,log}, final /tmp/hgt-finite-cyclic-cover-final.log empty.

2. HTGeometry/TwoMarkPolynomialApproximation.lean (13 declarations), namespace GaloisForLFunctions.HTGeometry.TwoMarkPolynomialApproximation.
approximant n z=(z-1)*(1+z/(n+1:C))^(n+1); approximantPolynomial eval matches.
hasDerivAt_approximant derivative=((n+2)/(n+1))*z*(1+z/(n+1))^n.
approximant_eq_zero_iff zeros exactly1,-(n+1); approximant_zero=-1.
critical_value_mem_marks and isCoveringMapOn_approximant (line65) give actual covering away from0,-1, using installed Polynomial.isCoveringMapOn_eval.
limitMap z=(z-1)*exp z.
norm_binomial_sub_exp_le m hm hlarge hsq hz: if2R<=m,R²<=m,|z|<=R, error<=2exp(R)R²/m. (No separate R nonneg argument needed here.)
norm_approximant_sub_limit_le n hR hlarge hsq hz: error<=2(R+1)exp(R)R²/(n+1).
tendstoUniformlyOn_approximant_closedBall, tendstoLocallyUniformly_approximant(line183).
Proof logarithm remainder at w=z/m norm<=1/2, delta=m(log(1+w)-w), normdelta<=R²/m<=1, expdelta-1<=2normdelta. No computations.
Card docs/drafts/pipeline/3-formalized/two-mark-polynomial-end-approximation.md.
Build /tmp/hgt-TwoMarkPolynomialApproximation-build.log PASS3388jobs; axiom /tmp/hgt-two-mark-polynomial-axioms.{lean,log}; final /tmp/hgt-two-mark-polynomial-final.log empty.
Exact polynomial monodromy with finiteAction remains OPEN. Matching ramification counts is insufficient. Prototype does not yield Xi finite realizations.

3. HTGeometry/NormalizedEmbeddingDiskBound.lean (2 declarations), namespace GaloisForLFunctions.HTGeometry.
Imports OneFiberDiskGrowth, Bottcher.W4LinWinding, Complex.Schwarz.
exists_nearby_omitted_value_normalized_disk: holomorphic f on ball0R, InjOn, derivative nonzero EVERYWHERE there, f0=0, derivf0=1 => omitted a norm<2R.
exists_normalized_embedding_disk_bound(line50): exists universal C>0, same assumptions => normfz<=CR on normz<=R/2.
Proof: image contains ball0(2R) => checked analytic inverse g maps ball0(2R) into ball0R, g0=0,g'0=1. Schwarz derivative bound <=1/2 contradiction. Apply OneFiberDiskGrowth with omitted a; bound=(B+1)|a|<=2(B+1)R.
Retain derivative-nonzero premise: existing inverse theorem requires it, not removed without proof.
Card docs/drafts/pipeline/3-formalized/normalized-embedding-disk-bound.md.
Build /tmp/hgt-NormalizedEmbeddingDiskBound-build.log PASS3994jobs, rebuilt existing W4LinWinding43s then newmodule12s. Axioms /tmp/hgt-normalized-embedding-axioms.{lean,log} standardonly; final /tmp/hgt-normalized-embedding-final.log empty.

All3 wired HTGeometry.lean; index /tmp/hgt-normalized-embedding-index.log PASS (earlier /tmp/hgt-finite-end-approximation-index.log PASS).
Global lint /tmp/hgt-finite-end-approximation-lint.log exit1 exactly7 unrelated unreachable:
RHTower.MobiusSquareResidueFourier, RHTower.PaperCircleAdaptiveHistory,
HTGeometry.ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra.
No own/forbidden errors. Don't touch others. Prefer rg '^error:' to reading hundreds warninglines.

All3 classified BRIDGE, not novel-science certification. Don't turn theorem counts into RH progress claims. Global existence still hard core.

## Active compactness card and proposed next construction
docs/drafts/pipeline/1-in-progress/normalized-embedding-local-compactness.md retains global conjecture; local result separated as formalized child.
Precise proposed criterion:
M connected Hausdorff second-countable analytic complex surface; U_n increasing open exhaustion; u_n:U_n->C embeddings analytic with analytic inverse; fixed chart at x0 in eventual domains, u_n(x0)=0 and derivative=1. Then subsequence locally uniformly converges to analytic open embedding M->C with same normalization.
CONDITIONAL criterion only; actual finite exhaustion embeddings not constructed.
Detailed argument now recorded on card, pending formal verification:
- S=points with neighborhood V and N,C s.t. all n>=N bounded by C on V. Local disk bound gives x0∈S.
- S open. At y≠x0 in closureS choose small chart disk with compact closure avoidingx0. Compact exhaustion puts closure inU_N. Choose controlled x∈S very near y, center a disk atx whose halfdisk contains neighborhoody and whose full disk staysinchart. Allu_n omit0 there (injective, solezero atx0outside); OneFiberDiskGrowth bounds halfdisk by B|u_n(x)|; x∈S supplies centerbound. ThusSclosed, connectedness => S=M.
- Countable chart disks; localboundedness +compactclosures give chartwise bound and tailindex. Reuse MontelOpenSetSubsequence perchart, nestedsubsequences+diagonal. Coordinate limits agree onoverlaps by pointwise uniqueness; giveglobalanalyticmap. Need exact chart/diagonal adapters.
- Installed LocallyUniformLimit differentiableOn/deriv preserve analytic and normalizedderivative1.
- Limitinjectivity: suppose x≠y sameimage. Diskaroundxavoid y. u_n(·)-u_n(y) nonzero therein. Its limitzeroatx. If germnonconstant, isolatezeroonsphere and HurwitzZeroLimit gives eventualzero contradiction. If locallyconstant, analytic identity theorem connectedM givesglobalconstant contradictionderivative1. Needmanifoldidentitytheoremadapter. Injective holomorphic map locallyopen =>openembedding.
- Separate unresolved: finite planar completion + polynomial realization to supplyu_n, exactprototype monodromy, actualglobalembedding. No missing premise silently added toXi result.

## Exact corpus sources inspected/useful
OneFiberDiskGrowth.lean fullyread currentturn:
exists_one_fiber_omitted_value_disk_bound:
existsB>1 forallf c a R>0, DifferentiableOn f ballcR, unique centerfiber, omitsa => forallz norm(z-c)<=R/2, norm(fz-a)<=B*norm(fc-a).
Bottcher/W4LinWinding.lean lines574-621:
imageInv T U=Function.invFunOn T U.
imageInv_right hz :T(imageInv T U z)=z forz∈T''U.
imageInv_mem hz.
imageInv_analytic(hUo)(AnalyticOnNhd T U)(InjOn T U)(forallw∈U,derivTw≠0): AnalyticOnNhd(imageInv T U)(T''U).
Use existing theorem; don't duplicate.
Complex.Schwarz.norm_deriv_le_div_of_mapsTo_ball hf hmaps hR:
map ballcR1 into closedBall(fc)R2 =>normderivfc<=R2/R1.
API scratch logs /tmp/hgt-normalized-embedding-apis.log; AnalyticAt.hasDerivAt DOES NOT EXIST, use .differentiableAt.hasDerivAt.
Lean EventuallyEq issue: declare hgf : (funz=>f(gz)) =ᶠ[nhds0] id to use .symm; bare forallᶠ equality didn't elaborate field .symm.

HTGeometry/MontelOpenSetSubsequence.lean fullyread earlier inturn; do notneedreread:
exists_tendstoLocallyUniformlyOn_subseq_of_bounded hUopen (foralln,DifferentiableOn(Fn)U)(foralln z∈U,normFnz<=C)
=>existsphi StrictMono phi,existsg,locallyuniform onU.
Contains countable disk cover, recursive extraction, diagonal Phi n=seq n n and convergence glue. Useful genericization for charts with differentbounds/tails; avoid duplicating wholeoldproofblindly.
HTGeometry/HurwitzZeroLimit.lean fullyread95lines:
eventually_exists_zero_of_tendstoUniformlyOn {p}{F}{f}{c}{r} hr
 (hF:forall a,DiffContOnCl(Fa)(ballcr))
 (hcont:ContinuousOn f spherecr)
 (huniform:uniform F f p closedBallcr)
 (hfc:fc=0)(hfne:forallz∈spherecr,fz≠0)
 =>∀ᶠa,existsz∈ballcr,Fa z=0.
Proof maximumprinciple1/F, noRouche needed. For tails mustreindex/dropfiniteinitial.
HTGeometry/HurwitzClosedZeroLocus.lean read1-130: entiregloballimit versions, lesssuitedcharts.
Mathlib/Analysis/Complex/LocallyUniformLimit.lean read134-164:
TendstoLocallyUniformlyOn.differentiableOn [filter.NeBot] hconv (eventuallyholomorphic) hUopen.
TendstoLocallyUniformlyOn.deriv hconv eventuallyholomorphic hUopen -> locallyuniform derivatives.
No general Riemannsurfaceuniformization found; installed RiemannMapping onlypreparatory asprior memory.

## Searches and scoped evidence
/tmp/hgt-intrinsic-meromorphic-realization-search.json lexical allAND0; broadened /tmp/hgt-uniformization-single-search.json irrelevant integrable/spectraluniformizations, don'tfollow forbiddenroutes.
/tmp/hgt-polynomial-local-monodromy-search.json deep60s PARTIAL, candidate/source APIs mostlygeneralmonodromyPerm/multiplication, no usablelocalramificationidentification; coveragecompleteinventory69244files, manycompilerpending/stale. Don'ttreatasabsencecertificate.
/tmp/hgt-normalized-disk-bound-search.json allAND0.
/tmp/hgt-analytic-inverse-injective-search.json found W4LinWinding.imageInv_analytic, inspected actualsource and scratchverified.
No web used.

## Cleanup and process discipline
Owned implementation scratch files removed: finite-cyclic-cover-approximation.lean, two-mark-polynomial.lean,two-mark-uniform.lean,two-mark-apis.lean,normalized-embedding.lean,normalized-embedding-apis.lean all /tmp/hgt- prefix. Allproductionfilespreserved; axiom .lean andlogs retained.
All tool sessions terminal. Brief one-compiler overlap happened accidentally when write_stdin returned stillrunning; both completed, nofileschanged; do NOT repeat. Pollterminal beforelaunch.
Serena initialinstructionsread currentturn. Goal remainsactive, notblocked orcomplete. Continue hardglobalcoordinate/exhaustion construction with corpus/paper/Lean loop.