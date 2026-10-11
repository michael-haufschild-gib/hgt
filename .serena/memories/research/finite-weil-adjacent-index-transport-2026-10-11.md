# Verified adjacent coupling and sharp index transport

PROGRESS. Active infinite local Lean research goal remains ACTIVE. Full exact adjacent transport objective is NOT complete: uniqueness, general ordered-node/logarithmic distance optimality and bounds, and all-mixture exact transport remain. Do not shrink target to index distance or mark goal complete. User restriction: local Lean corpus and installed Lean dependencies ONLY; no web, papers, external novelty claims, numerical experiments. This continuation read the explicitly re-requested goal attachment (user instructions only). No web/paper tools. New code explicitly reuses existing HTGeometry.FiniteNNCoupling type.

## Final verification
Five new leaves,42 public declarations,17 additional APIs. Native sequence2109 (IndexTransport -o plus /tmp/hgt-coupling-final-audit.lean) exited0. All42 #print axioms show exactly standard propext, Classical.choice, Quot.sound. All five final logs empty: /tmp/hgt-WeilLogShiftCanonicalEdgeOrientation.log, /tmp/hgt-WeilLogShiftCanonicalEdgePlan.log, /tmp/hgt-WeilLogShiftCanonicalCoupling.log, /tmp/hgt-WeilLogShiftFiniteCouplingCost.log, /tmp/hgt-WeilLogShiftCanonicalIndexTransport.log. /tmp/hgt-coupling-metadata.py verifies own and all direct dependency source/object freshness and exact umbrella imports; issues=[]. Imports added once to formal/GaloisForLFunctions/RHTower.lean7164-7168, directly after prior six prefix/mass leaves. Exhaustive incoming import scan: only umbrella and these five leaves. Scoped git diff --check passed.
Root lexical local index: finiteWeilCanonicalCoupling_index_optimal at CanonicalIndexTransport.lean104; exact1 eligible1 markers[]; /tmp/hgt-coupling-root-search.json. /tmp/hgt-coupling-final-audit.lean/.log contains full17 API and42 declaration audit.
Latest lint session94027 exit1, /tmp/hgt-coupling-lint.log:11 OUT-OF-SCOPE missing umbrella imports,367 size warnings, NO proof-debt findings now. RHTower: JointAncestryClusterPhase, JointAncestryLogWeightBernoulli, JointAncestryLogWeightExpansion, JointAncestryLogWeightPrimeSum, JointAncestryQuasiRHAmplification, JointAncestryQuasiRHChainExclusion, JointAncestryQuasiRHCore, JointAncestryQuasiRHParameters, JointAncestryZeroTailBound, XiExceptionalPointFoldLaw; HTGeometry.QKrawtchoukCompanionTriangular. Do not modify foreign scope. Previous14 findings are historical, superseded by this run.
No owned jobs left running. Sessions30374,2109,94027 terminal. One foreground owned Lean at a time throughout; no full/umbrella build, heartbeat increase, subagents, commits or pushes.

## Source/API details
All five leaves under formal/GaloisForLFunctions/RHTower/.

1. WeilLogShiftCanonicalEdgeOrientation.lean (9).
finiteWeilBinomialParity_eq_one_or_neg_one r u. Definitions finiteWeilCanonicalEdgeSource/Target r i: left->right if left parity=1, reverse otherwise. Source_parity=1, Target_parity=-1, Edge_difference(f)=sigma_left*(f_left-f_right); Edge_adjacent gives src.val+1=dst.val OR reverse; Edge_ne. finiteWeilCanonicalEdge_pairing r k f:sum_e m_e*(f_src-f_dst)=sum_j(P_j-Q_j)*f_j. Uses prefix-pairing-zero and D_e=sigma_e*m_e, not an assumed marginal.

2. WeilLogShiftCanonicalEdgePlan.lean (13).
def finiteWeilCanonicalEdgePlan r k u v=sum_e if src_e=u AND dst_e=v then m_e else0.
_nonneg, _row_sum, _col_sum reduce to oriented edge sums; _divergence gives row(u)-column(u)=P_u-Q_u using indicator test in Edge_pairing. _row_zero when sigma_u=-1; _col_zero when sigma_u=1. finiteWeilCanonicalPositiveProfile_zero_of_parity and NegativeProfile_zero_of_parity derive disabled endpoint profile from cluster parity. _marginals r k u returns BOTH exact sums, unconditional r,k,u. _zero_of_nonadjacent (two Nat successor inequalities), _diagonal, _total=1. These are actual plan support and marginals, not just a cost definition.

3. WeilLogShiftCanonicalCoupling.lean (8).
Definitions finiteWeilCanonicalPositiveNNProfile and NegativeNNProfile use NNReal.mk of actual real P/Q and existing nonnegativity proof. Their _mass theorems sum to1. finiteWeilCanonicalCoupling r k : HTGeometry.FiniteNNCoupling Pnn Qnn, with plan NNReal.mk(real edge plan,nonneg). _apply real coercion is exact real matrix; _zero_of_nonadjacent, _diagonal.
Existing type: formal/GaloisForLFunctions/HTGeometry/ConstitutiveHierarchicalMaximalCoupling.lean24-28, namespace HTGeometry: structure FiniteNNCoupling {X}[Fintype X](u v:X->NNReal) where plan:X->X->NNReal; row:forallx,sum_y planxy=ux; col:forally,sum_x planxy=vy. Existing source/object and direct PositiveOverlapDefect source/object were fresh. Only other usages: ConstitutiveHierarchicalMaximalCouplingChain.lean. No existing generic finite cost API found there. Do not introduce duplicate coupling structure.

4. WeilLogShiftFiniteCouplingCost.lean (4).
line8 def finiteWeilCouplingCost {I}[Fintype I]{P Q:I->NNReal}(gamma:FiniteNNCoupling P Q)(c:I->I->Real):Real=sum_u sum_v coe(gamma.plan u v)*c u v.
line12 finiteWeilCoupling_pairing gamma f:sum P*f -sum Q*f=cost gamma (funuv=>fu-fv). Derives real row/col equations via congrArg NNReal.toReal and coe_sum; rearranges sums.
line28 Cost_mono for pointwise costs; line37 Coupling_dual_bound gamma c f (foralluv,fu-fv<=cuv): marginal gap<=cost gamma c. Generic structural helpers; analytic potential feasibility is discharged in root below.

5. WeilLogShiftCanonicalIndexTransport.lean (8).
line8 finiteWeilCanonicalCoupling_cost_eq r k c: actual coupling cost for ANY real cost matrix equals sum_e m_e*c(src_e,dst_e). Two finite sum interchanges and ite_mul collapse atomic matrix.
line40 def finiteWeilIndexCost {n}(u v:Fin n)=abs((u.val:Real)-(v.val:Real)).
line43 finiteWeilCanonicalEdge_index_cost=1 via adjacency.
line58 finiteWeilCanonicalCoupling_index_cost r k=1 via edge contraction and sum m=1.
line64 finiteWeilBinomialParity_index_dual r u v: sigma_u/2-sigma_v/2<=indexCost u v. u=v trivial; unequal indices separated by>=1, while |sigma|=1 bounds difference<=1.
line85 finiteWeilCanonicalProfiles_index_dual_pairing r k: Pnn/Qnn pairing against sigma/2=1, from earlier sum(P-Q)*sigma=2.
line96 finiteWeilCanonicalCoupling_index_lower_bound r k gamma: EVERY coupling of actual Pnn,Qnn costs>=1. No analytic premises.
ROOT line104 finiteWeilCanonicalCoupling_index_optimal r k gamma:cost canonical<=cost gamma. Together with line58 proves actual minimum1. Uniqueness NOT yet proved.

## API and proof gotchas
17 extra verified have checks, actual toolchain: Finset.sum_eq_zero.{0,0},sum_nonneg.{0,0},mul_ite.{0},NNReal.coe_sum.{0},NNReal.coe_injective,NNReal.coe_mk,HTGeometry.FiniteNNCoupling.{0},.row.{0},.col.{0},ite_mul.{0},Finset.sum_le_sum.{0,0},mul_le_mul_of_nonneg_left.{0},NNReal.coe_nonneg,NNReal.mk,NNReal.toReal,Fin.ext,abs_of_nonpos.{0}. Scratch /tmp/hgt-edge-plan-api.lean and /tmp/hgt-coupling-cost-api.lean.
Use NNReal.mk, NOT anonymous constructor pair: installed NNReal abstraction deliberately makes simplifier coe_mk fail on subtype-abusing anonymous constructors. Source explicitly advises mk. Use NNReal.coe_nonneg instead of subtype .property. NN fields wrap via coe_injective + coe_sum/coe_mk.
Negative parity if (-1:Real)=1 needs norm_num, simp alone did not discharge. Remove redundant ring after norm_num (final source clean).
Noncomputable section should precede namespace, or close unnamed section before named end; first generic cost scratch only failed on section nesting (fixed in tree).
Index-dual exact division pairing simplification works with Finset.sum_div,sub_mul,sum_sub_distrib,mul_div_assoc,sub_div in forward direction. Generic cost pairing changes second double sum by sum_comm with explicit f:=fun v u=>coe(plan u v)*f v. All final logs empty.

## Local corpus audit
Prior prefix topic audit in research/finite-weil-adjacent-prefix-probability-2026-10-11. This continuation searched 'coupling marginal' lexical module GaloisForLFunctions, no-refresh, per-module0, pages0/20. All30 declaration statements inspected: /tmp/hgt-coupling-marginal-search.json and -tail.json. Symmetric real coupling marginal lemmas concern quadratic Dirichlet budgets, not our oriented coupling. HTGeometry/QuantileCoupling.lean164-213 read (measure monotone coupling,marginals,cost); KantorovichRubinsteinDuality.lean1-90 read (measure IsCoupling and weak duality). Existing FiniteNNCoupling chosen for discrete representation. ConstitutiveHierarchicalMaximalCoupling.lean24-88 and complete declaration inventory read; chain inventory read; exhaustive FiniteNNCoupling usage scan shows only these two existing files and new wrapper. /tmp/hgt-rhtower-coupling-definitions.txt116 definition names inspected, remaining physical interactions unrelated.

## Full pending target and next implementation
Original dependency-closed paper card remains docs/drafts/pipeline/2-fully-proven/finite-weil-adjacent-nodal-transport.md; not reread/changed this turn except prior summary. Full target: unique optimal endpoint coupling for ordered-node absolute cost, actual minimum sum m_i gap_i; index uniqueness; canonical log bounds1/(k+r+3)<=minimum<=1/(k+2), no quadratic width; full mixtures unique cost |a-b|*endpoint minimum.

Suggested next: generic complementary slackness lemma from finite cost duality. If f_u-f_v<=c_uv and cost gamma c equals its marginal pairing, then every coe(gamma.plan uv)*(c_uv-f_u+f_v)=0. Sum slack terms is0 and every term>=0; Finset.sum_eq_zero_iff_of_nonneg or nested single_le_sum should give each term0 (verify actual APIs first). For index dual sigma/2, nonadjacent distinct vertices have cost>=2 while potential gap<=1, so optimum has adjacent support. Every coupling also has zero rows at negative-parity nodes and zero columns at positive-parity nodes: gamma.row/col plus profile-zero lemmas and nonnegative entries. Therefore all nonzero entries follow forced edge orientation; diagonals vanish.

Prove unique adjacent plan via prefix cut net flow: for any gamma, pairing against indicator Iic(cut) fixes crossing outgoing-incoming to D_i. Adjacent support leaves only the two orientations of that one edge. Parity kills one orientation, so remaining entry is m_i. Then matrix ext on arbitrary u,v: off-adjacent0; adjacent u.val+1=v.val identifies edge i=Fin.mk u.val (by omega), use Fin.ext for casts; reverse similarly. FiniteNNCoupling equality follows equality of plan functions and proof irrelevance; inspect whether ext lemma exists rather than guessing.

For general strict ordered-node metric, either potential phi_(i+1)-phi_i=-sigma_i*(x_(i+1)-x_i), or cut-cost decomposition. Potential is1-Lipschitz and strict for nonadjacent pairs: x+phi and x-phi are monotone (alternating slopes0 or2gap), strictly increase over every two edges. Could use actual Fin.monotone_iff_le_succ API if found. Cut alternative: distance=sum positive gap_i*cut-separation indicator; each coupling crossing mass>=|D_i|; canonical attains. Equality requires no opposing flow on each cut. A long edge crosses two successive cuts whose forced directions alternate, impossible. This proves stronger metric-independent uniqueness: the same fixed canonical plan is uniquely optimal for EVERY strictly increasing reembedding of its ordered vertices, not only original log nodes. Keep all geometry/uniqueness requirements intact.

Mixtures a>=b: diagonal bP+(1-a)Q plus (a-b)Gamma; a<b: diagonal aP+(1-b)Q plus (b-a)Gamma transpose. Universal expression uses min(a,b)P+min(1-a,1-b)Q on diagonal and max(a-b,0)Gamma+max(b-a,0)Gamma^T. Parameters can be Set.Icc 0 1 structural inputs. Costs scale |a-b|; signed potential certifies bound. Strict equality allows only diagonal plus one directed adjacent orientation, fixing all entries. a=b unique diagonal since off-diagonal node costs positive.

This is PROGRESS, not completion of full adjacent transport or infinite research goal.