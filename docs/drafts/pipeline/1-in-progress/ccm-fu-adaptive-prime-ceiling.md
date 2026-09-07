# CCM-FU: adaptive original-diagonal ceiling

- **ID:** CCM-FU-PE4
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; unproved
- **Source:** [adaptive stepwise obstruction](../5-failed/ccm-fu-adaptive-prime-energy.md)
- **Goal:** obtain the final signed SD1 bound through a source-selected path that permits necessary local energy increases.

## Frozen statements

Keep the literal source, prime merger and retained energies `Q_P(M)` from the linked card.

**PE4:** for every cutoff M, some ordering of all primes below M satisfies `Q_P(M)<=Q_empty(M)` at every prefix of that order.

**PE4G:** the deterministic greedy order choosing the smallest next energy, breaking ties by smaller prime, satisfies the same original-diagonal ceiling for every cutoff M.

PE4G is a stronger, separate proposal; a greedy failure does not refute PE4. These are separate from PE3's already refuted requirement that each step contract. Both retain factor one and the literal arithmetic source. Neither the ceiling nor the allowed ordering is changed after a failure.

## Protocol

Reuse existing full subset-state energies through M=32 and greedy-stage data through M=1024. Recompute reachability in the fixed original-energy sublevel graph and the exact finite minimax recurrence on the stored energies. This does not regenerate channel values or rerun the expensive greedy search. Finite passes remain guidance, never proof. Before any new Lean machinery, identify either a decisive obstruction with positive survivor or an independently justified arithmetic invariant that could enforce the ceiling.

The final energy equals the squared complete signed sum, so PE4 would imply SD1. No endpoint inequality is assumed to select or verify a path.

## Current evidence and boundary

Reanalysis of every saved subset energy through M=32 finds a path below the original diagonal at every cutoff. The exact finite minimax recurrence on these floating-point values is `c(empty)=Q_empty`, `c(P)=max(Q_P,min_(p in P)c(P\{p}))`; each terminal minimum equals the original diagonal. Every saved deterministic greedy stage through M=1024 also meets that ceiling. The largest recorded post-merge/original ratio is approximately `0.773063650278327`, at M=17, step six, prime eleven. Initial stages and cutoffs with no prime merges are retained separately. These are finite numerical passes, not formal proofs. The [stored-energy reanalysis](../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/README.md) neither regenerates channels nor reruns the expensive greedy screen.

A generic argument from positivity, contracting first steps and a bounded endpoint is unavailable. The [closed four-coordinate cube obstruction](../5-failed/ccm-fu-positive-prime-cube-ceiling.md) has strictly positive unsigned coefficients, initial diagonal `337/16`, every order's energies `20,22,18,0`, and therefore an unavoidable second-stage excess `15/16`. Its entire background family has a sharp, Lean-proved ceiling threshold. This is a source-shape countermodel, not the actual divisor source; it does not refute PE4 or SD1.

**PE4 and PE4G remain open.** The remaining input must control the actual arithmetic overlaps throughout a complete adaptive prime path. Finite success cannot replace that input. An assumed original-diagonal endpoint bound would already be SD1 and cannot be used to produce it through PE4; the generic cube obstruction grants an endpoint bound only to isolate the independent failure of intermediate-order control.

The separate [PE5 independent-subset average](../5-failed/ccm-fu-bernoulli-prime-energy.md) is unconditionally refuted in Lean: after every cutoff, its actual half-probability energy exceeds every fixed multiple of the original diagonal. Its stronger positive survivor is the unbounded normalized magnitude of the literal deformed mean on every tail. The [closed two-Abel transfer and growth proof](../3-formalized/ccm-fu-half-selection-growth-obstruction.md) retains the actual source and uses no numerical premise. This independent-average obstruction does not refute PE4's adaptive path.

## Late-prime blocks: source-derived endpoint control

For a prime p with M<=2p and p<M, the only active source label containing p is p itself. Before processing p, its retained fibre is the singleton coefficient `C_p(M)<=0`; every other nonempty fibre is unchanged by that merger. If `h_P` is the retained cofactor-one head, the exact updates are

`h_(P union {p})=h_P+C_p`,
`Q_(P union {p})-Q_P=2*h_P*C_p`.

Consequently a block consisting entirely of unprocessed late primes has energy at every intermediate processed subset bounded by the maximum of its two endpoint energies. If the intermediate head is nonnegative, all previous heads in that block were nonnegative and each previous step contracted. If it is nonpositive, every subsequent head is nonpositive and each subsequent step increases energy. This gives an order-independent endpoint bound for the actual block, without asserting that either endpoint is below the original diagonal.

The exact fibre isolation, energy identities and arbitrary-subset endpoint theorem are [formal and audited](../3-formalized/ccm-fu-late-prime-block-endpoints.md). Writing `c_L=sum_(p in L)C_p` and `q_L=sum_(p in L)C_p^2`, the complete block law is `Q_(P union L)=Q_P+2*h_P*c_L+c_L^2-q_L`. For any fixed ceiling B, all intermediate subsets meet B if and only if both endpoints do. This reduces the live scheduling issue to coupling smaller-prime steps with late-prime blocks. It does not justify placing the entire late block first or last, and it supplies no final SD1 bound.

## Retained-source recursion under a new prime

For a prime p>N, cutoff pN and a processed set P not containing p, each source label divisible by p is uniquely p*d with d<=N. Exact arithmetic homothety gives `C_(pd)(pN)=-sqrt(p)*C_d(N)`. Its remaining prime label is the remaining label of d with p inserted. Thus every retained fibre containing p is a reflected square-root-scaled copy of the corresponding retained fibre at cutoff N.

If P contains all primes below N, this copy is concentrated in the singleton fibre `{p}`, whose coefficient is exactly `-sqrt(p)*S(N)`. The proved negative complete source at N=7 therefore supplies a positive isolated singleton after primes2,3,5 have been processed, at every cutoff7p with p>7 prime. A blanket nonpositive-fibre rule cannot be extended from the late band to all such merged primes. The [retained-source recursion and orientation reversal](../3-formalized/ccm-fu-prime-fibre-recursion.md) are formal and audited. Positive retained singleton coefficients exceed every fixed bound beyond every cutoff; processing them strictly increases the head. The positive survivor includes the entire retained fibre field and the exact mixed energy law, not only the sign counterexample. This leaves the actual interleaving estimate open.

More precisely, write `F_(M,P)(R)` for the retained fibre at R. For p>N, p unprocessed and p absent from R, Lean proves `F_(pN,P)(R union {p})=-sqrt(p)*F_(N,P)(R)` and `F_(pN,P union {p})(R)=F_(pN,P)(R)-sqrt(p)*F_(N,P)(R)`. For N>=2 the complete energy change is `-2sqrt(p)*sum_R F_(pN,P)(R)*F_(N,P)(R)`, over every p-free cofactor label in the full larger cube. The copied source square cancels exactly with the removed fibre energy. The required signed bound on this mixed inner product remains open; these identities apply at exact integer dilation cutoffs pN, with no terminal block omitted.


## Square-root terminal phase: adaptive scalar ordering

The literal source has a sharp terminal ordering theorem after all primes with `p^2<M` have been processed. An active source index `n<M` cannot then retain two distinct primes: their coprime product divides n, while the smaller prime's square is at least M. Every retained source label is therefore empty or a singleton. Singleton coefficients can have either sign, as the proved retained-source recursion demonstrates.

For a scalar head h and finitely many signed leaves a, the energy is `h^2+sum a^2`, and merging one leaf changes it by `2ha`. Choose a leaf with `ha<=0` whenever one exists. Such a step contracts energy. If none exists, all remaining leaves have the head's strict sign; every subsequent step increases energy to the complete-source square. Induction gives a complete order with peak exactly the maximum of initial and final energies. Both endpoints occur on every complete path, so this is the sharp terminal minimax value. This proof uses no numerical premise and no endpoint ceiling assumption.

**Formal and audited:** the [square-root terminal ordering certificate](../3-formalized/ccm-fu-square-root-terminal-order.md) supplies a complete distinct prime list with every prefix below the maximum of its two actual endpoint energies. A terminal order under any ceiling exists exactly when both actual endpoints satisfy it. This establishes existence; the frozen deterministic greedy policy is not analyzed by this theorem. It does not bound either endpoint by the original diagonal. The small-prime phase and final SD1 cancellation remain open; PE4 and PE4G retain their frozen statements.


## Arbitrary-cutoff prime recursion: clipped square-root interpolation

The retained-field recursion is closed for every prime p and cutoff M, including the overlapping-label phase. Put `N=floor(M/p)` and `theta=(sqrt(M)-sqrt(p*N))/(sqrt(p*(N+1))-sqrt(p*N))`. Then `0<=theta<1`. Splitting the original time sum into complete p-blocks and its clipped last block gives

`K_(pd)(M)=sqrt(p)*K_d(N)+(sqrt(M)-sqrt(p*N))*D(floor(N/d))`.

The exact successor law turns this into `sqrt(p)*((1-theta)*K_d(N)+theta*K_d(N+1))`. For p unprocessed and absent from retained label R, the prime-square exclusions are automatic inside that fibre. Thus its p-containing partner is the negative square-root-scaled convex interpolation of `F_(N,P)(R)` and `F_(N+1,P)(R)`. This requires no inequality between p and N. The last block and newly born source coefficient are retained exactly.

The corresponding merger subtracts that interpolated field. Its complete energy update keeps the mixed inner product with the actual larger field; the copied square cancels the removed partner energy. Convexity also bounds the copied packet energy by p times the interpolated smaller packet energies, with exact nonnegative Jensen defect. **Formal and audited:** the [all-cutoff interpolation certificate](../3-formalized/ccm-fu-prime-fibre-interpolation.md) proves all these identities and the bound `sum_R F_(M,P)(R union {p})^2<=p*((1-theta)*Q_P(N)+theta*Q_P(N+1))` for every finite family of p-free labels. The same processed set P occurs at both smaller cutoffs; separately chosen good paths do not provide that compatibility. This supplies an actual all-cutoff source recursion and packet bound. The signed mixed inner-product estimate, complete adaptive original-diagonal ceiling and SD1 remain open.


## Overlap-phase obstruction and exact two-coordinate ceiling

The frozen diagnostic asks whether every retained state with distinct unprocessed primes p,q satisfying `p*q<M` admits a nonincreasing next merger. **False in Lean:** at M=11 and P={3,7}, the remaining primes are 2 and 5, their joint fibre is strictly positive, and both next mergers increase energy by more than 1/200. Both final mergers also increase energy. Nevertheless every completion subset retains a reserve greater than 1/100 below the original diagonal. Thus mandatory increases are not confined to the scalar terminal phase, and this obstruction does not refute PE4 or PE4G.

The [closed obstruction and positive survivor](../5-failed/ccm-fu-overlap-phase-contraction.md) also classify arbitrary signed two-coordinate completion. For the retained coefficients h,a,b,c at empty,{p},{q},{p,q}, put `I=h^2+a^2+b^2+c^2` and `F=(h+a+b+c)^2`. The minimum peak over both complete orders is exactly `max(I,F,I+(h+c)(a+b)-abs((h-c)(a-b)))`. The sign of `(h-c)(a-b)` selects the better first merger. This gives the exact intermediate constraint alongside the endpoint constraints, without assuming any ceiling. Both this classification and the actual arithmetic reserve are formal and audited.

The stored-data reanalysis examines all saved subset states through M=32 and all greedy stages through M=1024, with the original tolerance `1e-12*max(1,Q_empty)`. It finds 136 forced-growth states among 5720 states with possible prime-pair overlap, first at the formal M=11 witness. Among 70640 greedy stages with possible overlap, 19954 increase; the first is M=16, step three. The greedy-specific observation remains numerical guidance only. No channels or greedy paths are regenerated, and no computed value enters Lean. The missing input remains a source-derived all-cutoff budget for the signed mixed terms along a complete compatible path.

## Frozen common-order diagnostic

**PE4C:** for every cutoff bound B, there exists one ordering of the primes below B such that, for every M<=B, every prefix P of that same ordering has `Q_P(M)<=Q_empty(M)`. Primes at least M act trivially at cutoff M. This is a stronger proposed compatibility input for the all-cutoff interpolation law, separate from PE4 and the deterministic PE4G policy.

The diagnostic reads every stored subset state through B=32. A state is admissible exactly when its restrictions meet the original diagonal ceiling at every smaller cutoff, with the existing tolerance `1e-12*max(1,Q_empty)`. Reachability is tested on the intersection of these sublevel graphs. No source channel or greedy path is regenerated. Finite success does not prove PE4C; a failure does not refute PE4.

**Current evidence:** PE4C passes for every stored bound through 32. One common order at bound 32 is `31,29,23,19,17,13,11,2,7,3,5`. The intersection graph has 1938 admissible states among 2048, and every admissible state is reachable there. These are floating-point guidance results, not a Lean certificate. The complete stored-state check and input hash are retained in `common_order_reanalysis.py` and `common-order-reanalysis.json` in the linked computation directory. PE4C remains open.

## Required growth of late-prime interleaving

A fixed number of late-prime blocks cannot support any fixed original-diagonal multiplier. For a block L of unprocessed primes with `M/2<p<M`, let `t_L=sum_(p in L)K_p(M)`. Its exact head drop and the head-square energy lower bound give

`t_L <= sqrt(Q_P(M))+sqrt(Q_(P union L)(M))`.

Thus K blocks whose endpoint energies are at most B have total capacity `2K sqrt(B)`. Assigning each actual late prime to exactly one block retains its complete positive mass T(M). The source laws `Q_empty(M)<=722M^2` and `T(4N)/(4N)->+infinity` then force an endpoint above `C Q_empty(4N)` for every admissible fixed-K partition, for every fixed C, at all sufficiently large N. The initial processed sets may be arbitrary; the obstruction therefore applies to actual complete orders partitioned into maximal uninterrupted late-prime blocks.

The [closed capacity law and fixed-block obstruction](../5-failed/ccm-fu-fixed-block-prime-schedules.md) retain a nontrivial quantitative survivor: for any valid schedule, `T(M)<=2K sqrt(B)`, and the stronger sum of actual endpoint square roots is available without a common budget. A PE4 proof must permit the number of late/earlier-prime interleavings to grow with the cutoff. It cannot replace them by finitely many uniformly budgeted phases. This necessity does not produce the required growing schedule or decide PE4, PE4G, PE4C or SD1.

## Nonempty-fibre obstruction and signed late-prime steering

Let `V_P(M)=Q_P(M)-F_(M,P)(empty)^2`, the energy carried by all nonempty retained labels. The frozen diagnostic asks whether every literal prime merger contracts V at every retained state; separately, it tests whether some complete V-nonincreasing order exists at every stored cutoff. These claims concern V only, not PE4's complete energy or final signed head.

Read every saved subset state through cutoff 32. Recover the head using the exact isolated late-prime law `Q_(P union {p})-Q_P=2 F_(M,P)(empty) C_p(M)`, with `C_p(M)=-(sqrt(M)-sqrt(p))*(2 gamma-1)` for `M/2<p<M`. If p is already processed, use the incoming edge and its known head increment. This retains the original source; it regenerates no channel table or greedy path. Use the original tolerance `1e-12*max(1,Q_empty)`. Numerical output is guidance only, never a Lean premise. A V-contraction failure does not refute PE4 or SD1.

**Universal stepwise V-contraction is false in Lean.** At M=21, after prime two, merging prime five increases V by more than 1/1000. The positive retained three-singleton is inherited from the exact smaller source at seven. Its constructive overlap with the {3,5} fibre outweighs the removed five-singleton square. Analytic square-root and divisor-defect bounds prove the strict increase independently of the stored values. The [closed obstruction and positive survivor](../5-failed/ccm-fu-nonempty-energy-contraction.md) record the exact proof.

The all-cutoff survivor separates the effects precisely. A late-prime block satisfies `V_(P union L)=V_P-sum_(p in L)C_p^2`, regardless of head sign. For another prime q and consumed positive late mass `t_L`, its full-energy gain satisfies `delta_q Q(P union L)=delta_q Q(P)-2 t_L F_P({q})`. Thus late consumption improves a step with nonnegative retained singleton and worsens a step with nonpositive singleton. These identities and both comparisons are formal. A growing interleaving must retain this sign and control the remaining nonempty mixed products.

The diagnostic examines 41409 saved edges and finds 2472 nonempty-energy increases, first at the formal cutoff-21 witness. A complete V-nonincreasing path exists at every saved cutoff through 32, but this remains finite numerical guidance. Neither V's nonnegativity nor its final value zero bounds the final signed head or supplies SD1.

## Unconditional initial head balancing

The [source-derived head-neutralization construction](../3-formalized/ccm-fu-late-prime-head-neutralization.md) gives a proved initial operation at every sufficiently large cutoff M=4N. A selected active late-prime block L leaves the head in `[-sqrt(M),0]`, with head square at most M and `Q_L(M)<=V_empty(M)=Q_empty(M)-h_empty(M)^2`. Every intermediate subset of L stays below the original diagonal.

The finite selector retains the discrete overshoot: nonnegative weights covering a nonnegative target admit a subset whose excess is at most one maximum weight and whose excess square is paid by the selected weight squares. The exact late-block law therefore releases the entire original head square. Actual availability follows from `0<=h_empty(M)<=27M`, `K_p(M)<=sqrt(M)` for active late primes, and `T(4N)/(4N)->+infinity`. No signed final-energy bound is assumed. Later smaller-prime mergers still need the open joint signed budget, continued mass availability and a growing interleaving; this local construction does not decide PE4, PE4G, PE4C or SD1.

The [oriented initial extension](../3-formalized/ccm-fu-oriented-initial-prime-extension.md) gives a second unconditional construction along those cutoffs: stop below the original head, leaving it in `[0,sqrt(M)]`, with `Q_L<=V_empty+M`. Every original fibre has alternating Möbius parity, and late-only processing preserves that parity on nonempty fibres. A nonnegative head completes this orientation, so every available prime contracts energy after every intermediate subset R of L: `Q_(R union {q})<=Q_R<=Q_empty`. Thus any one additional prime can be interleaved anywhere in the block under the original diagonal, without choosing that prime in advance.

This parity condition is not preserved by arbitrary smaller-prime mergers. The already formal positive three-singleton after prime two at cutoff21 violates its original odd parity. The next required control must therefore permit such sign changes or prove a suitable restoration; repeatedly applying the initial extension theorem is not justified. The full growing schedule and SD1 remain open.

## Quantitative control after parity changes

The [formal parity-defect transport](../3-formalized/ccm-fu-parity-defect-transport.md) splits the actual oriented field `A_P(R)=(-1)^card(R) F_P(R)` into good energy G_P and reversed-sign energy D_P, with `G_P+D_P=Q_P` and `D_empty=0`. At every retained state, every available prime satisfies `delta_q Q(P)<=2 sqrt(G_P) sqrt(D_P)`. This permits changed signs while bounding their possible constructive gain.

A merger from a fully oriented input creates at most its removed prime-containing packet energy in defects. The exact clipped homothety transfers this to the two adjacent smaller retained energies. At the original state, with `N=floor(M/q)` and clip weight w, it yields `D_{q}(M)<=722 q ((1-w)N^2+w(N+1)^2)` unconditionally. For two distinct primes, `Q_{p,q}<=Q_p+2 sqrt(Q_empty) sqrt(D_p)` is formal. A sufficient next comparison would pay this possible growth from the first merger's released energy; no uniform comparison or indefinitely repeatable budget follows from the estimate alone.

The [initial small-subset diagnostic](ccm-fu-initial-small-subset-ceiling.md) passes all 627 stored two-prime states through32 and all stored states of cardinality at most four. Its first unrestricted failure uses five primes at cutoff17. These are finite numerical observations; the all-cutoff two-prime ceiling remains open, and no numerical value is used by the defect-transport proof.

## Uniform source ceiling and the scale of initial reserve

The [uniform square-root channel bound](../3-formalized/ccm-fu-uniform-channel-square-root-bound.md) is unconditional in Lean: `0<=K_d(M)<=7 sqrt(M)` for all natural M,d. Retaining the half-logarithmic Stirling endpoint cancels the harmonic logarithm in the smooth hyperbola boundary; its remainder is at most seven. The nonpositive centered Abel term and exact clipped square-root interpolation give the same ceiling at every dilation.

Consequently `h_empty(M)^2<=49M`. For every initial late block L leaving `h_L>=-sqrt(M)`, the consumed mass is at most `8 sqrt(M)`, its removed singleton squares total at most `8M`, and its complete release satisfies `Q_empty-Q_L<=57M`. Both initial balancing constructions meet this condition. This release is below every positive quadratic multiple eventually, uniformly over L. Initial balancing therefore supplies a linear reserve; any larger reserve needed later must come from actual paired contractions. Neither a quadratic reserve requirement nor a diagonal lower bound is asserted.

The [geometric defect-reserve diagnostic](ccm-fu-geometric-defect-reserve.md) tests the sufficient state budget `Q_P+2 sqrt(G_P D_P)<=Q_empty`. A complete path meeting this budget at every preterminal state exists at every stored cutoff through32. Individual states can fail it: 1478 of 8860 do, first at M=13, P={5,7,11}, despite that state's actual energy remaining below the ceiling. All 192 first-prime states pass the weaker budget with Q_empty replacing G, sufficient there for every second-prime extension. These numerical results retain the original tolerance and regenerate no source channels. The uniform reserve comparison, all-cutoff two-prime bound, complete growing path and SD1 remain open.

## Sharp source-local two-prime comparison

The [formal two-prime criterion](../3-formalized/ccm-fu-two-prime-local-criterion.md) identifies every original oriented fibre with K at its prime product and retains every four-coefficient cofactor block. A nonnegative block a,b,c,e with `b,c<=2a` and `e<=2b,2c` has `(a-b-c+e)^2<=a^2+b^2+c^2+e^2`. Two is the sharp uniform edge factor for that class. This permits sign reversal in a first merged coordinate; it does not require monotonicity of the unsigned channels.

Exact clipped interpolation makes the global dilation comparison `K_(pd)(M)<=2K_d(M)` equivalent to the unit-cofactor comparison `K_p(N)<=2K_1(N)`. The actual arithmetic capstone is an unconditional alternative: either `Q_{p,q}(M)<=Q_empty(M)`, or one of r=p,q violates the unit factor-two bound at an active cutoff `r<N<=M`. No unproved arithmetic comparison is assumed by that alternative.

The [unit-comparison candidate](ccm-fu-two-prime-local-blocks.md) remains open. All 6562 saved cofactor blocks through32 pass. The separately frozen first-prime extension to cutoffs33..1024 passes 617453 active source-pair factor-two tests and 95747 first-prime geometric reserve tests; all original energies agree with the saved greedy data. Those finite checks do not prove the unit comparison, the two-prime ceiling, or any complete growing schedule. Source tables are saved for reuse, and numerical values enter no Lean proof.

The [second-centered arithmetic bounds](../3-formalized/ccm-fu-second-centered-hyperbola.md) give the actual unit source the floor `K_1(M)>=sqrt(M)/16-5log(M+1)-14`. The modular primitive's nonzero mean and moving terminal residue are retained exactly; a second primitive leaves error at most `1/(48d)` per modulus. The complete centered term has negative square-root coefficients between `-5/96` and `-1/48`, up to logarithmic error. Combining its lower bound with the smooth-prefix estimate produces the unit floor without a signed aggregation premise. The [exact smooth mean and bounded-quotient theorem](../3-formalized/ccm-fu-smooth-square-block-mean.md) proves `smoothAbel(M)=a sqrt(M)+O(log(M+1)+1)`, with `a=log(2*pi)/2-gamma-1/6>1/6`. The resulting complete unit coefficient band has a strict factor-two margin. One universal T gives `M/p>=T -> K_p(M)<=2K_1(M)` for all positive dilations; any original two-prime ceiling failure must have a witness `r<N<=M` with `N/r<T`. The [large first-prime orientation theorem](../3-formalized/ccm-fu-large-prime-orientation.md) closes `M<=5p` at every sufficiently large parent cutoff: every child cofactor is dominated by its parent, so every retained sign survives that first prime and every second prime contracts energy. Any two-prime ceiling failure in that parent tail requires both primes below M/5. Large-parent unit failures lie in `5<=M/p<T`. The finite parent regime, remaining middle profiles and complete adaptive ceiling remain open.


## Source-supplied blocks with two active cofactor channels

The [two-channel block certificate](../3-formalized/ccm-fu-two-channel-prime-blocks.md)
is formal and audited. At every sufficiently large M, any block of primes
satisfying `2M<=5p` and `sum_L K_p<=K_1` preserves every retained sign, complete
energy, and nonempty energy at every subset. Exact support removes joint
selected-prime coefficients. The expenditure ratio `2K_(2p)<=K_p` and the
uniform parent comparison `K_1<=2K_2` make the head budget cover the second
changed component; all higher cofactor children vanish.

The actual prime source supplies a nonempty such L from `(8N,9N]` at every
sufficiently large cutoff20N. Its head lies in `[0,sqrt(M)/15]`, its cofactor-two
reserve strictly decreases, and `E_L<=V_empty+M/225`. Every available next prime
contracts at every intermediate subset. This does not assert that L contains
at least two primes, that all source primes are consumed, or that an arbitrary
additional small prime preserves signs. A complete growing schedule remains open.


## Complete quotient subpool orders after arbitrary retained states

The [quotient-window certificate](../3-formalized/ccm-fu-quotient-window-orders.md)
orders an entire selected subpool after any processed state P. Its primes have
one quotient `M/p=N` and `N+1<=p`. Their two adjacent copied fields are inactive
under every operation in the subpool, so all signed packet overlaps stay fixed.
The exact energy marginal is the original interaction plus twice the overlaps
with already processed packets.

The actual transverse source sign fixes a separating part before ordering.
Cauchy–Schwarz makes packet overlaps nonnegative within either sign class;
their insertion marginals increase. Each class admits a complete order below
its larger endpoint energy. Concatenation controls every prefix by the initial,
source-fixed separating, and final energies. The result needs no retained-sign
condition and applies after earlier operations have changed those signs.

These three predetermined endpoint energies still require arithmetic bounds.
The theorem permits arbitrary subpools, so it does not require exhausting a
whole quotient window in one contiguous block. In particular, it does not evade
the proved need for growing late-prime interleavings. A globally bounded choice
of subpools and all required endpoint estimates remain open.


## Actual growing signed batches under a uniform quadratic ceiling

The [growing signed-batch certificate](../3-formalized/ccm-fu-growing-signed-prime-batches.md)
proves positive macroscopic source supply after the fixed prime core below eight.
Clipped reflection of the negative complete source at seven gives a uniform
positive singleton floor on one fixed quotient-seven window. The corpus prime
count theorem makes its total positive mass superlinear; the actual negative
late-prime supply is superlinear along the same cutoffs.

All primes in both pools are isolated after that fixed core. Exact scalar
transport retains the removed singleton-square reserve. Matching opposite
subpools makes this reserve pay the final head square, and a complete distinct
order stays below the starting core energy. For every real T and all sufficiently
large cutoffs `M=7(b+1)(4N)` for one fixed b, the selected batch consumes at least
TM of each sign while every prefix has energy at most `184832M²`. Every partial
preparation of the fixed core has that same bound.

This is an unconditional source-produced growing partial schedule. It does not
claim the original diagonal ceiling, complete prime coverage, or control of
later middle-prime steps and their changed retained fields. Those remaining
interactions, the full growing schedule, PE4, PE4G, SD1, and RH stay open.

## Increasing middle order cannot be rescued by fixed scalar reserves

The [analytic obstruction and positive survivor](../5-failed/ccm-fu-increasing-middle-scalar-reserves.md)
are closed in Lean. At cutoff `M=64N²`, after all primes below `4N`, the
complete energy divided by M² is at least `N/(52428800log(8N)^3)` even after
**every possible selection** of scalar primes `M/8<q<M`. This lower bound
tends to infinity, excluding every fixed quadratic multiplier for that
increasing-middle scheduling class. The selections may depend on the cutoff
and have unrestricted cardinality and mass.

The mechanism is a whole family of retained singleton coordinates inherited
from uniformly large child heads at the two clipped quotient endpoints.
Consuming isolated primes leaves all disjoint nonempty coordinates unchanged,
so scalar head balancing cannot alter this lower bound. A surviving complete
order must move nonisolated primes across the middle front and control their
coupled fields before this state occurs. The previous bounded growing signed
batches remain valid partial schedules. General adaptive PE4, PE4G, PE4C,
SD1 and RH remain open; the obstruction supplies no final signed-source bound.

## Growing coupled prime batches

The [coupled-batch certificate](../3-formalized/ccm-fu-coupled-prime-batches.md)
is unconditional in Lean. A fixed core below fifteen excludes prime two, so
copied fields retain both the head and the {2} coordinate. Actual child
profiles at 2, 7 and 14 positively span this plane, with one margin stable
under small independent clipping. Three macroscopic prime windows at
`M=14(b+1)N`, for one fixed `b>=15`, realize these directions.

Any partial selection leaves all child fields fixed. The exact full-energy
increment is `-2 sqrt(p) dot(x,V_K(w))`, including the cancellation of removed
copied squares with receiving squares. As long as each pool has an unused
prime, one available step does not increase energy. The resulting distinct
batch has length the smallest pool cardinality, with every prefix bounded
by `2^15*722*M^2`; its guaranteed length tends to infinity.

This controls two coupled retained coordinates with actual source supply.
The list still leaves prime two and other source primes unprocessed.
Propagation while changing the retained field, complete compatible coverage,
PE4, PE4G, PE4C, SD1 and RH remain open.
