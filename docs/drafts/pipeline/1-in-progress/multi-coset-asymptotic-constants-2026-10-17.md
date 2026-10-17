# Multi-coset asymptotic constants

- Stage: 1-in-progress
- Type: CANDIDATE
- Scope: independent BiScaleUncertainty; no RH objective, no hgtl7.
- Brief: `/Users/michael/.codex/attachments/14cea3d2-a6f6-463f-bcd2-5d8a6947ba60/pasted-text-1.txt`.
- Objective: 100 significant contributions toward sharp monotone finite-grid energy bounds combining signed collar partition, clique sphere duality, and Schur residual coupling. Auxiliary lemmas are not separate contributions.

## Current plan

1. [x] Read full field motivation and relevant memories; inspect current source and existing claims. Earlier stopped work is prior evidence, not newly completed work.
2. [x] Identify missing transfer: arbitrary physical partitions have a certified convex optimum but no general source-energy theorem.
3. [x] Prove and formalize general extended-energy transport and lower bound, then the optimal-coefficient bound and monotone cutoff envelope, its normalized smooth-source bound, and positive finite convergence.
4. [x] Source-transfer direct leaf audit, all 19 scratch axiom/signature audits, own umbrella wiring, index and whitespace checks pass.
5. [x] Final direct leaf recheck passed, exit 0, no diagnostics. All 35 cutoff theorem axiom/signature audits pass; both compilation logs are empty and compiled outputs are current.
6. [x] Formalize paired signed-coset sphere support, discharge product-zero orthogonality
   on the squared grid, integrate the stronger kernel for actual sources, and build
   the monotone envelope over all product-admitted cutoffs.
7. [x] Prove paired array capacity bounds and padding invariance; reuse exact physical
   extension/retraction to prove Q_K monotonicity and tail stability, identify the
   coupled limit, and establish the product-cutoff N^(−1/4) bound.
8. [x] Prove exact capped-block support and compact two-radius maximization;
   combine whole-coset spheres with low-node product constraints without dropping
   high nodes, then transfer the resulting full-grid coefficient to actual sources.
9. [x] Prove full-grid capped capacity and cutoff comparisons; identify the all-low
   specialization, sandwich its optimized hierarchy between the prior C_N and Q_N,
   and derive monotone convergence and the quantitative actual-source certificate.
10. [x] Formalize exact full-grid activation, scalar quadratic deficit, rationalized
    physical gain, and the almost-everywhere equality/strictness criterion; transfer
    the gain identity to actual source energy.
11. [x] Prove exact two-column Schur support, including the general measured-lag
    rotation bound and zero-lag sharp support/attainment. Derive the actual
    four-coordinate dyadic collar constraint from grid zeros, optimize physical
    coefficient splitting, and combine its certificate with the capped hierarchy.
12. [x] Add a full measured signed-Gram certificate for arbitrary compact continuous
    sources, as required by the updated read-only field README. Keep the blind-grid
    hierarchy explicitly specialized; do not promote it to a general signed theorem.
13. [x] Prove full measured signed-Gram capacity, physical cutoff monotonicity,
    retraction stability, optimized finite limit, and unconditional source receiver.
14. [x] Prove the full measured-Gram physical dual gap, zero-gap complementarity,
    finite-allocation error and quantitative limiting actual-source trial certificate.
15. [x] Construct an explicit compact-source dyadic packet producer and prove its
    sharp anchored minimum and cutoff error; audit finite strict positivity only
    where it supports the concrete construction.
16. [x] Construct a measurable least-price physical response, prove exact linear
    optimality and actual gain, then build an accepted-response cutoff ladder.
17. [x] Prove norm regularization and quantitative damped physical responses;
    reconcile the original objective, construct a monotone producer reaching S∞,
    and verify its unconditional allocation and cutoff errors.
18. [ ] Develop general signed multi-column Schur-coupled growth and matching
    finite-limit asymptotics. These and the full 100-contribution objective remain open.

Package 13 constructs a finite regularized physical response iteration with an
unconditional allocation error. Comparing its original coefficient with the
previous physical extension gives a monotone producer converging to S∞, with
explicit allocation and cutoff errors. This advances the producer direction
required by Trap 10. Equality with S∞ remains open for the older unsmoothed
package-12 ladder. The source-dependent S∞/R is not identified with H∞ or the
unrestricted sharp source infimum. Next: matching cutoff asymptotics and general
nonzero-lag multi-column Schur support.

Updated field context: read all 260 lines of the relocated read-only README after
the user's Trap 10 message; SHA-256
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
It changed externally after the package-10 verification, when its hash was still
`80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507`.
This agent did not edit either version. Do not add receiver-only reformulations
with an unproved external bound, or pre-subtract discrete counterterms before
floor summation. Existing `ExplicitNyquistPolarAndChebyshevFactorialProducer.lean`
already states the requested explicit producers. Its first factorial stencil has
main term 2N log(2): only the centered error is O(log N). The second stencil
cancels that main term. Cell error 1/(16n²) is the integral of the squared error,
not the L² norm. These are prior results, not contributions on this research topic.
The three referenced producer signatures and both factorial proof bodies were inspected.
A scratch import audit could not run because that existing module's `.olean`
is absent; `/tmp/bsu-trap10-reference-audit.log` records the import failure.
No fresh Lean-verification claim is made for it; the temporary failed probe was
removed. This does not affect the completed 49-theorem package-10 audit.

Current mathematical results: P_N is monotone with an explicit tail error; product-zero
coupling gives attained paired-sphere support and a stronger physical coefficient Q_K.
The optimized certificate C_N=max(P_N,max_(K²≤N)Q_K) is positive, monotone, bounded,
and valid for actual smooth grid sources. Paired capacity now proves Q_K saturation
and an explicit N^(−1/4) hierarchy error. Full-grid capped support preserves all
high nodes. Its optimized B_N is now Lean-verified: C_N≤B_N≤Q_N, actual monotonicity,
the same Q_∞ limit, and the inherited N^(−1/4) upper error hold for actual sources.
The exact activation criterion and rationalized physical gain are now verified too:
coupling is strict precisely where squared maximal low fractions sum above one;
integrated gain is strict precisely when inactivity fails almost everywhere.
Exact two-column Schur support now produces an optimized dyadic physical kernel
and monotone H_N≥B_N with Q∞≤H∞≤tailMass. The full measured signed-Gram
receiver applies to arbitrary compact continuous sources, without grid blindness;
it retains every signed cross-coset entry and cancels the singular origin weight.
The new signed-profile hierarchy S_N(f) is monotone and satisfies
0≤S_∞/R−S_N/R≤8·2^(1/4)/(sqrt(N)(1−2/N²)); its limit bounds actual extended
source energy. Full measured-Gram trial prices now give an exact dual-gap identity,
zero-gap complementarity and finite-allocation plus cutoff error for every trial
partition. Package 11 adds a fixed smooth actual-source producer with sharp
anchored Gram minimum R/(m+1), unique positive triangular weights, and exact
squared-distance remainder at signed dyadic cutoff 2^m. Package 12 realizes a pure
measurable minimum-price response and an accepted-response cutoff ladder. The
ladder's coefficients are monotone with finite produced limit; their certified
post-response error is min(gap, curvature remainder) plus cutoff tail. All three
new leaves, all 43 public theorem axiom audits, and the final direct leaf check pass.
Package 13 now proves unconditional regularized curvature, an explicit finite
allocation schedule, and a new monotone producer reaching S∞. Its normalized
allocation error is at most (δ+1)/(n+1), plus the existing cutoff tail to S∞.
All seven new leaves, all 77 public theorem axiom audits, and final direct check pass.
Progress: 13/100. Latest lint reports 15 unrelated concurrent umbrella failures.
Next: nonzero-lag support and sharp asymptotics; full goal remains active.

Current signed-capacity search `/tmp/bsu-signed-capacity-search.log` finds 586
declarations in 83 modules. It supplies actual translation-packet norm identities
and the physical retention construction. Search is partial, source-only hits,
older coverage snapshot, semantic coverage unmeasured; no exhaustive novelty claim.
The following dependency-closed argument is paper-proved and Lean-audited.

### Fixed-source signed-Gram cutoff theorem (package 9, verified)

Fix any compact continuous real source f, R=h_f(0), and δ=log(2)/2. At fixed
offset y let v_t=T_t f in L², so ||v_t||=sqrt(R). For finite signed nodes t_i,
put P(a)=W v_0+Σa_i v_ti and K(a)=R(W+Σa_i)−sqrt(R)||P(a)||. The packet
norm identity identifies this expression exactly with the existing full measured
Gram kernel, including all cross-coset and anchor entries.

For b_i≥0, Q=Σb_i v_ti has norm at most sqrt(R)Σb_i. Both triangle inequalities
give | ||P(a+b)||−||P(a)|| |≤sqrt(R)Σb_i. Hence
0≤K(a+b)−K(a)≤2RΣb_i. This needs neither nonnegative a nor positive W.
Taking b−a as increment proves coordinate monotonicity. If b_i≤a_i+e_i and
e_i≥0, monotonicity and capacity give K(b)−K(a)≤2RΣe_i. Zero-padding leaves
both packet and mass unchanged, hence preserves K exactly.

For physical partitions, extension increases padded weights coordinatewise, so
every incumbent signed-Gram coefficient increases. For a large partition η and
smaller cutoff N, retract below log(N)−δ using the already-proved physical repair.
At each signed node the repaired weight a equals the original b in the protected
region; outside it, b≤a+e with e=b times the retention indicator. Thus the loss
is ≤2R times the retention fibre. Exact physical transport bounds its integral by
T_N=∫_(log(N)−δ)^∞ w. No off-diagonal Gram locality is assumed: packet capacity
controls all changes to the full matrix simultaneously.

Let S_N(f)=sup_ρ ∫K_ρ. Existing 0≤K≤2R mass and exact partition mass transport
give 0≤S_N≤2R∫_(δ,∞)w. Extension gives actual S_N monotonicity; retraction gives
S_M−S_N≤2R T_N for M≥N. Therefore S_N↑S_∞ and
0≤S_∞−S_N≤2R T_N≤8R·2^(1/4)/(sqrt(N)(1−2/N²)). The existing actual-source
receiver bounds each coefficient by the full ENNReal increment energy; supremum
preserves this bound. For compact C² sources, S_∞≤J_arch(f). Dividing by R≥0
also yields the normalized certificate with total division covering R=0.

These are source-dependent certificates for general signed correlations. They
neither identify S_∞/R with H∞ nor give a positive uniform constant on all sources.
The error is an upper bound, not a matching asymptotic or sharp-rate claim.
Plan: [x] finite packet capacity/padding; [x] physical cutoff comparison;
[x] optimized limit and actual-source certificate; [x] direct/axiom/lint audits.
At the package 9 audit, the global gate reported the four unrelated wiring
failures recorded below; package 10 records the latest result.

### Measured signed-Gram trial certificate (package 10, verified)

Corpus search `/tmp/bsu-signed-gram-dual-search.log` finds 1108 declarations in
119 modules, including the independent-coset physical dual certificate and exact
bounded-cost transport. Search is partial, source-only hits, older coverage
snapshot, semantic coverage unmeasured. Exhaustive source-pattern search found
no existing full measured signed-Gram physical dual-gap declaration; this is not
a claim of exhaustive mathematical novelty.

At a fixed fibre write P_a=Wv_0+Σa_i v_i, G_a=||P_a||², H_a=sqrt(RG_a), and
q_i=Re⟨P_a,v_i⟩/H_a with total division. Cauchy gives |q_i|≤1. If R=0 all
translation vectors vanish. If P_a=0 all numerators vanish. In both cases q=0.
Otherwise z_a=P_a/||P_a|| is a unit vector, H_a=sqrt(R)||P_a||, and the norm
support inequality gives the nonnegative exact remainder

    r(a,b)=H_b−H_a−RΣ(b_i−a_i)q_i ≥0.

At P_a=0 the same expression is H_b≥0. Thus no strict packet-positivity premise
is needed. Define p_i=(1+q_i)/2∈[0,1]. The exact kernel difference is

    K_b−K_a=2RΣ(b_i−a_i)−2RΣ(b_i−a_i)p_i−r(a,b).

All q_i are quotients of finite measured-Gram expressions, hence measurable;
their bounds make costs integrable. Pull p_i back to physical x using the actual
signed offset. Let p_min(x) be the finite minimum over active collars, using
masked price 1 outside a collar. Set

    Slack(ρ,η)=∫[Ση_k(x)w(x)p_ρ,k(x)−w(x)p_min(x)]dx ≥0,
    Gap(ρ)=2R Slack(ρ,ρ).

Exact physical transport and equality of total physical mass give

    Cρ+Gap(ρ)−Cη=2R Slack(ρ,η)+∫r(ρ,η) ≥0.

Integrability of r follows from its expression in kernel, mass and bounded-price
cost differences, avoiding separate integration of the singular anchor. Hence
0≤S_N−Cρ≤Gap(ρ), zero Gap certifies optimality, and package 9 yields
0≤S_∞−Cρ≤Gap(ρ)+2R T_N. This is a usable finite-partition certificate retaining
all measured signed cross entries. No optimizer or positive packet is assumed.
Moreover Gap=0 iff R=0 or complementary allocation holds almost everywhere:
every positive incumbent share is placed at a minimum-price active collar.
For R>0 this follows because the slack is the integral of a finite sum of
nonnegative terms ρ_k w(p_k−p_min), and w>0 on the physical interval. Zero
integral forces every positive-share term to vanish; the converse is immediate.
This classifies zero certificate, not necessity of this particular subgradient
certificate for every optimizer. The independent-coset precedent is the existing
`gap_eq_zero_iff_complementary`; the signed prices and explicit R=0 factorization
are new here. This does not assert that R=0 is an exception to complementarity.
Formalization and actual-source receiver audits pass; count this as one package.
Implementation plan: [x] full-Gram covariance, bounded prices and norm-support remainder;
[x] measurable physical prices and exact transport; [x] exact dual gap, finite
optimization and limiting trial certificate; [x] direct and axiom audits, wiring,
lint, ledger. No prior package is counted again.
All three final dependency checks and the final direct trial leaf audit passed,
exit 0 without diagnostics. The finite support leaf imports `SignedGramCapacity`;
only the trial certificate imports the cutoff hierarchy. All 49 public theorems
are audited exactly once by `/tmp/bsu_signed_gram_dual_axioms.lean`, using only
`propext`, `Classical.choice`, and `Quot.sound`. Printed capstones and actual
price/gap/remainder definitions were inspected. Current manifest is
`/tmp/bsu-signed-dual-manifest.json`; all 26 prior hashes and 29 imports checked.
Index/discovery pass. Lint reports twelve foreign unwired modules in
`/tmp/bsu-signed-dual-lint-final.log`. No own module is unwired. Further corpus discovery
of compact-translate independence returned no useful deep hits; the shorter lexical
query `translate independent` also completed, uncounted.

Next structural candidate, uncounted: prove strict positivity of the finite Gram
matrix of distinct translates of a nonzero compact source. Candidate paper
mechanism: take a nontrivial finite relation and its smallest active shift t_min.
The single-active-term case is immediate. Otherwise let s be the supremum of
source support and ε the smallest positive shift gap;
choose u∈(s−ε,s) with f(u)≠0. At x=u−t_min all larger-shift terms vanish,
so the packet equals its nonzero leading coefficient times f(u). Continuity then
gives positive packet L² norm. This works for arbitrary signed coefficients after
discarding zero coefficients, provided shifts are distinct. A realizable singular
Gram boundary at fixed distinct nodes would then require a limit rather than a
nonzero compact source.
With positive fixed origin anchor, equality in the norm triangle inequality
would force proportional packets; translate independence and equality of anchor
coefficients force identical node weights. This suggests strict concavity of the
actual-source allocation kernel and uniqueness of an optimizer, if one exists.
No realization, existence, nonvanishing, strict-concavity or uniqueness claim is
currently formalized. Global deep search returned irrelevant finite-dimensional
hits; the shorter lexical query found 156 declarations but mostly differential
independence of special functions. Further targeted corpus audit is required.

### Conditioning boundary: sharp dyadic candidate (paper derivation, uncounted)

Finite strict positivity would not imply a cutoff-independent lower bound on
anchored packet norms. A concrete candidate obstruction has an exact positive
survivor. Set d=log(2), explicitly define g(x)=max(0,1−4|x|/d), supported in
[-d/4,d/4] with g(0)=1, and fix f=g−T_d g. Integer-d translates of g have disjoint supports,
so they are orthogonal. Write R_g=||g||²; then R_f=2R_g, h_f(d)=−R_g and
h_f(kd)=0 for integer |k|≥2. Thus the actual dyadic Gram form is a discrete
Dirichlet form, retaining its negative adjacent entries.

For coefficients a_k on −m≤k≤m, impose a_0=1 and extend by zero outside this
range. Direct collection of translated g terms gives

    ||Σ_(k=−m)^m a_k T_(kd) f||²
      =R_g Σ_(k=−m)^(m+1) (a_k−a_(k−1))².

The left m+1 differences sum to 1 and the right m+1 differences sum to −1.
Finite Cauchy on each side gives the sharp lower bound R_f/(m+1). Equality
forces all left slopes to be 1/(m+1) and all right slopes to be −1/(m+1),
giving the unique coefficients a_k=1−|k|/(m+1). They are nonnegative. Thus this
one fixed actual source admits positive anchored packets with exact minimum
Gram energy R_f/(m+1), at dyadic cutoff N=2^m (m≥1). Their norms approach zero,
although no finite packet vanishes. With anchor W, scaling gives W²R_f/(m+1).

The smooth refinement below now verifies this sharp classification and actual-source
realization. It does not assert these coefficients are physical
collar partitions: they need not obey physical weight or mass constraints. It
therefore does not contradict the proved S_N tail law or prove its sharpness.
Existing finite-translate and coherent-cancellation source constructions were
audited for reusable exact identities and duplication.
Search `/tmp/bsu-signed-dual-conditioning-search.log`: 219 declarations in 40
modules; search completed, but source-only candidates, older coverage snapshot,
and semantic coverage unmeasured. Hits expose actual packet identities and
Dirichlet/coercivity infrastructure, not this exact anchored minimum among the
reported results. An exhaustive source-pattern search found related triangular
Gram and continuous Dirichlet forms; no exhaustive mathematical novelty claim.
Lean status: the following smooth refinement is verified as package 11. The
tent formulation and general anchor-W scaling above are paper consequences;
the formal capstone uses the explicit smooth source and origin coefficient 1.

Implementation refinement: instantiate a literal smooth `ContDiffBump` centered
at zero with inner radius log(2)/8 and outer radius log(2)/4, instead of the tent.
This preserves the exact orthogonal-translate argument and gives a C∞ source.
No existential seed or supplied orthogonality interface is left in the capstone.
Let e_j=T_(j log2)g, f=g−T_log2 g, and
Z_m=Σ_(k=0)^m(e_(-k)−e_(k+1)). The average of the first m+1 symmetric translation
chains of f telescopes exactly to Q_m=Z_m/(m+1), so Q_m is an explicit producer.
Orthogonality gives ||Z_m||²=(m+1)R_f. Every packet with origin coefficient 1
and arbitrary coefficients at ±k log2, 1≤k≤m, has inner product R_f with Z_m.
Consequently its exact excess over R_f/(m+1) is ||P−Q_m||². This simultaneously
proves a sharp lower bound, attained error, and equality at the packet level.
Coefficient rigidity can be recovered by pairing against partial sums of the
orthogonal e_j. Plan: [x] concrete smooth source and orthogonal atoms;
[x] telescoping producer and exact error/minimum; [x] coefficient rigidity;
[x] full measured-Gram cutoff degeneration; [x] direct/axiom/lint audits and ledger.
The four leaves count once, as package 11.

Current implementation leaves: `DyadicDifferenceSource.lean`,
`DyadicAnchoredProducer.lean`, `DyadicTriangularOptimality.lean`, and
`DyadicGramConditioning.lean`, all wired into the umbrella. All four dependency
checks pass without diagnostics. All 55 public theorem axiom audits pass exactly
once, using only `propext`, `Classical.choice`, and `Quot.sound`. Printed capstone
signatures and concrete source/packet/producer definitions were inspected. The
final direct leaf check passes with an empty log. All 29 previous owned source
hashes are unchanged and all 33 owned imports occur once
(`/tmp/bsu-dyadic-integrity.json`).
Current corpus search `/tmp/bsu-dyadic-producer-search.log`: 387 declarations in
98 modules, partial/source-only/older snapshot with semantic coverage unmeasured.
Finite translation infrastructure was audited; reported tent results concern
Sobolev velocity frames, and the six-packet coherent-cancellation construction
has a different target. No exhaustive novelty claim.

Coefficient rigidity paper audit: for 0≤k<m let L_k=Σ_(j=0)^k e_(-j) and
R_k=Σ_(j=0)^k e_(j+1). Direct orthogonality gives
⟨P,L_k⟩=R_g(1−a_k) and ⟨P,R_k⟩=R_g(b_k−1). For Q_m these are
R_g(k+1)/(m+1) and −R_g(k+1)/(m+1), respectively. Thus P=Q_m forces
a_k=b_k=(m−k)/(m+1), and these coefficients attain Q_m by counting the
symmetric chains containing each node. Therefore equality at the sharp minimum
is equivalent to this coefficient formula on every active node.
At N=2^m, the normalized minimum is exactly log(2)/(log(N)+log(2)); it decreases
to zero. Choosing m>1/c excludes any positive uniform bound c, even for
nonnegative coefficients and this one fixed smooth source. This is an anchored
minimum, not a claimed minimum eigenvalue or condition-number formula. No polar
admission, physical collar allocation, or sharp asymptotic for S_N is inferred.

The constructive direction is now realized in package 12: a measurable least-price
response partition for the actual prices from package 10, with zero cross-slack
and exact gain after curvature loss. Acceptance and extension produce a monotone
cutoff ladder. Strict ascent and equality of produced and optimized limits remain
open. Deep discovery `/tmp/bsu-dyadic-next-physical-producer-search.log` completed
with zero lexical hits but useful actual price/partition/transport candidates;
source-only, older snapshot, semantic coverage unmeasured. No novelty claim.

### Constructive minimum-price response and cutoff ladder (package 12, verified)

Previous goal turn completed package 11. This complete construction is package 12;
its 43 public theorems form one significant contribution, not 43 contributions.

Fix an actual compact continuous source f and physical partition ρ at cutoff n.
Let p_k(x)=ρ.gramPhysicalPrice f k x, q(x)=ρ.gramPriceFloor f x, and Ω be the
physical interval. Define E_k to be the active collar points with k≤n and p_k=q.
All E_k are measurable, because actual prices and their finite floor are measurable.
The finite active minimum is attained at every x∈Ω. Define
F_k=E_k\(union_(j<k) E_j). These measurable cells are pairwise disjoint and cover
Ω; the least minimizing natural index proves coverage, with no chosen optimizer
or analytic premise. Existing `collarPhysicalShare_partition` applies to this
actual cover. Its multiplicity is exactly one, so the resulting response η has
shares 1_(F_k): precisely one selected collar per physical point.

Each positive response share uses p_k=q. Consequently ρ.gramSlack η f=0,
and η attains the pointwise and integrated minimum of the incumbent's physical
linear cost over all admissible partitions. Every other partition has excess
cost equal to its nonnegative cross-slack; equality is exactly almost-everywhere
allocation only to minimum-price active collars. Thus the canonical Gram gap is
the attained greatest feasible linearized gain, not merely an abstract bound.
The existing exact dual identity gives
C(η)−C(ρ)=Gap(ρ)−integral Remainder(ρ,η).
The remainder is actual, nonnegative and integrable; no coercivity lower bound
or asserted full-response improvement is used.

Define the accepted step as η when C(η)≥C(ρ), otherwise ρ. It is an actual
physical partition, with coefficient max(C(ρ),C(η)) and exact gain
max(0,Gap(ρ)−integral Remainder(ρ,η)). This step is explicit in source, prices and
integrals; it does not invoke an unknown optimal partition.
Writing G=Gap(ρ), D=integral Remainder(ρ,η), and C⁺ for the accepted coefficient,
the exact remaining old dual budget is C(ρ)+G−C⁺=min(G,D): if G≤D the step
retains ρ and the deficit is G; if D≤G it accepts η and the deficit is D.
Since C⁺≤S_n≤C(ρ)+G, this proves the unconditional post-response bound
0≤S_n−C⁺≤min(G,D), and adding cutoff tail gives
0≤S∞−C⁺≤min(G,D)+2R·tail_n. This strengthens the produced certificate without
assuming that either the gap or curvature remainder tends to zero.
Starting with equalMultiplicity at cutoff 0, extend the previous physical
partition to cutoff n+1 and apply this step. Existing actual extension monotonicity
then makes the produced full-Gram coefficients monotone in cutoff. They remain
bounded by S_n(f) and hence converge to a finite produced limit ≤S∞(f).
At every cutoff, the computed partition's gap plus the proved cutoff tail bounds
the distance to S∞. Smooth-source normalization supplies actual J_arch lower
bounds. This does not yet prove produced limit=S∞, vanishing gaps, strict ascent,
or sharp error to the unrestricted source infimum.

Implementation plan: [x] `SignedGramMinimumResponse.lean` (measurable pure
selection and admissible response); [x] `SignedGramResponseOptimality.lean`
(attained linear minimum, equality classification and exact actual gain);
[x] `SignedGramResponseLadder.lean` (accepted update, monotone cutoff producer,
finite limit and source certificate); [x] direct leaf/axiom/lint/index/integrity audits.
Keep prior 33 owned leaves unchanged, wire new leaves, preserve read-only README.
All three leaves are written and wired, and all three dependency checks pass
without diagnostics. All 43 public theorem axiom audits pass exactly once, only
`propext`, `Classical.choice`, and `Quot.sound`. Concrete definitions and capstone
signatures inspected; final direct check passes with an empty log. Selection excludes
inactive collars before comparing ties, so an inactive masked-price tie cannot
receive physical mass.

Current deep discovery `/tmp/bsu-minimum-response-search.log` completed in 55.55s:
zero lexical hits, useful actual price, partition and arbitrary-measurable-cover
share identities. Source arguments and proposed ingredients inspected. Source-only
older coverage; semantic completeness unmeasured. Exhaustive field-source search
found no minimum-price response implementation. This is not an exhaustive
mathematical novelty claim.

Historical package-12 candidate, superseded by regularization below: a damped
minimum-price response with a proved curvature
bound at each fixed source and cutoff. The packet nodes in `signedGramShift` do
not depend on the physical fibre variable; only their weights and origin anchor
do. A positive actual finite Gram residual could therefore control every fibre
at a fixed cutoff. Package 11 excludes an unjustified cutoff-uniform constant.
Distinct translates of a nonzero compact continuous source should be independent:
take the smallest shift with nonzero coefficient, then a source point sufficiently
near the supremum of its support that all larger translates vanish. Continuity
passes an L² equality to pointwise equality. The required next contribution is
the actual fixed-cutoff Gram lower bound and curvature consequence, not merely
the generic independence lemma. No positive lower bound, damping theorem,
strict ascent, gap convergence, or optimality of the produced ladder is claimed yet.
Deep search `/tmp/bsu-minimum-response-next-coercivity-search.log` completed in
91.43s with only source-only older candidates and unmeasured semantic coverage.
Both lexical pages `/tmp/bsu-minimum-response-next-independence{,-page2}.json`
were inspected: 31 hits in 14 modules. Field-wide text search found no
`LinearIndependent`/`PosDef` implementation; existing hits include actual
translation Gram energy and division-free residual waves. No exhaustive novelty claim.
Fresh concurrent source `FiniteFilterSchurResidual.lean` was also inspected:
its support-supremum argument proves escape for a particular finite hyperbolic
filter and strict positivity after two specified projections. It does not state
arbitrary finite-translate independence or the full signed-node anchored lower
bound. Reuse that support argument where applicable; do not count the other
agent's filter result. Its source was read, not independently Lean-audited here.

Alternative to conditioning, preferred for the next audit rather than presumed
proved: regularize the actual packet norm by an extra coordinate ε·sqrt(R), ε>0.
For P the actual signed packet, set
K_ε=R(W+mass)−sqrt(R)·sqrt(||P||²+ε²R). The intended reconciliation is
0≤K−K_ε≤εR, hence 0≤C−C_ε≤εδR. Prove integrability from this bounded difference
and the existing combined kernel; never integrate the singular anchor separately.
The augmented norm is at least ε·sqrt(R), so its quadratic remainder should admit
a bound without an assumed Gram lower bound. The zero-energy source must be
handled explicitly.

The candidate physical prices use P/sqrt(||P||²+ε²R); their boundedness,
measurability, transport and actual minimum-price response must all be discharged.
Let M_n=2(n+1)·logarithmicCollarWeightBound(n), and T_n be the common integrated
physical mass. Existing weight bounds suggest ||P_η−P_ρ||² has integral at most
4R M_n T_n, giving quadratic loss Bτ² with B=2R M_n T_n/ε. For a damped minimum
response with τ_t=2/(t+2), the desired regularized-objective gap recurrence is
e_(t+1)≤(1−τ_t)e_t+Bτ_t². If established, e_1≤B and induction gives
e_t≤4B/(t+2), t≥1. The remaining original-objective error would be at most
εδR+4B/(t+2). These rates and the underlying curvature estimate are not yet
formalized or counted; audit every factor and analytic obligation first.
At fixed ε, acceptance in the regularized objective preserves this recurrence.
Across cutoffs or ε changes, compare the produced actual coefficient with the
physical extension of the prior partition to retain monotone original certificates.
This route may avoid conditioning altogether; fixed-source Gram rigidity remains
a useful independent structural question.

Regularization search `/tmp/bsu-minimum-response-next-regularization-search.log`
completed in 57.84s, but proposed Sobolev curvature ingredients do not address this
packet norm problem. Rephrased lexical search returned two unrelated origin
regularization results; field text search found source averaging, not this
augmented packet norm. Source-only older coverage, semantic completeness unmeasured;
no exhaustive novelty claim. No new regularized producer or rate is claimed here.

### Regularized physical producer (package 13, verified)

This contribution discharges curvature for actual signed packets without an
assumed Gram lower bound. Completed plan: [x] regularized packet support and
quadratic remainder; [x] actual physical mixture, integrability and uniform
integrated curvature; [x] measurable regularized minimum response and damped
producer; [x] original-objective reconciliation and quantitative iteration;
[x] direct Lean, all-theorem axioms, wiring, index and ledger audit.

Write R=h_f(0), H(a)=sqrt(R)||P_a|| and
H_e(a)=sqrt(H(a)^2+(eR)^2), e>0. Then
0≤H_e−H≤eR. With z=sum_i(b_i−a_i)covariance_a(t_i), the exact identity is
2H_e(a)[H_e(b)−H_e(a)−Rz/H_e(a)]
=R||P_b−P_a||²−[H_e(b)−H_e(a)]².
Support follows from Cauchy for the augmented packet; the identity yields
0≤remainder≤||P_b−P_a||²/(2e). For R=0 every term vanishes.
This retains every signed Gram entry, even when the original packet vanishes.

For actual partitions with fibre masses A,B≤M, triangle inequality gives
||P_b−P_a||²≤R(A+B)²≤2RM(A+B). Exact mass transport then bounds its integral
by 4RMT. A physical convex mixture has packet difference τ(P_b−P_a), hence
integrated regularized remainder≤(2RMT/e)τ². Every integrated expression is a
combined kernel, bounded price cost or bounded difference; the singular origin
anchor is never integrated separately. These statements, including zero-source
and vanishing-original-packet cases, are now Lean-verified.

For the iteration, avoid introducing an attained regularized optimizer. For each
actual competitor η, its objective difference from the current iterate is at most
the attained regularized linear gain G_e. The schedule τ_t=2/(t+2) gives
C_e(η)−C_e(ρ_(t+1))≤(1−τ_t)[C_e(η)−C_e(ρ_t)]+Bτ_t².
At t=0 the incumbent term vanishes, giving error≤B. Induction gives
C_e(η)−C_e(ρ_t)≤4B/(t+2), t≥1: the induction step reduces to
(t+1)(t+3)≤(t+2)². Take the supremum over actual competitors only afterwards.
Original-objective error is then at most eδR+4B/(t+2).

An explicit source-independent work schedule is e_k=1/(k+1) and
t(n,k)=ceil(8 M_n T_n (k+1)²)+1. Its proved allocation error is
R(δ+1)/(k+1). At cutoff n choose k=n and compare this candidate's original
coefficient with the physical extension of the previous cutoff producer. Keeping
the larger preserves monotonicity and the allocation error. The limiting
coefficient equals S∞ with error at most R(δ+1)/(n+1)+2R tail_n.
This is now Lean-verified for actual compact continuous sources, including zero.
For compact C² sources the normalized coefficients bound J_arch/R from below.
It makes no claim about the unrestricted sharp source infimum or numerical
computational complexity of the finite functional construction.

Implementation now spans seven owned leaves: `RegularizedGramGeometry`,
`PhysicalCollarMixture`, `PhysicalPriceResponse`, `RegularizedPhysicalGram`,
`RegularizedGramDescent`, `RegularizedGramIteration`, `QuantitativeGramProducer`.
All seven compile without diagnostics. The generic minimum-price response
uses equal sharing among all active minimizers; it does not require a pure
tie-breaker. It is instantiated with actual regularized source prices, not supplied
as an analytic oracle. The iteration compares against every admissible physical
partition before taking a supremum. Inner damped steps need no acceptance test;
only the outer cutoff ladder compares original coefficients. The advance is a
source-uniform normalized allocation error and a concrete monotone producer
reaching S∞. It does not establish a sharp
unrestricted source constant or a matching lower asymptotic for the cutoff tail.
Count this construction once: 13/100 after all seven leaves and final audits pass.
Verification checkpoint: `/tmp/bsu-regularized-checkpoint.json`.

`PairedCollarCapacity.lean` now passes direct verification of block/radial capacity,
unordered nonnegative error bounds, and exact padding. `PairedCollarCutoffStability.lean`
implements the extension/retraction comparisons, monotonicity and finite limit of Q_K,
exact largest-admitted-frame reduction, floor-root error, and uniform bound
16·2^(1/4)/N^(1/4) for C_∞−C_N, N≥4. Both direct compilations and all 30 package
axiom audits pass. Final direct recheck passed, exit 0, no diagnostics. The two leaves form one contribution.

`PhysicalCollarCutoffMonotonicity.lean` now passes its direct leaf check, with no diagnostics.
Its explicit extension proves monotonicity of P_N and equality with the running maximum.
`PhysicalCollarCutoffStability.lean` implements the complementary retraction and explicit
inverse-square-root error; direct compilation produced a current compiled output with no
diagnostics. All 35 public theorem axiom audits and the final direct leaf recheck passed.
Global lint passed at that package's final check; see latest package evidence below
for current concurrent umbrella failures.
These two leaves form one contribution package; padding lemmas are not separate contributions.

Current signed-coupling package: `PairedCosetSphereDuality.lean` passes direct
compilation, including exact finite support and attainment. `SignedCosetProductCoupling.lean`
passes direct verification of actual product-zero orthogonality, the coupled physical
kernel and exact gain, and the extended/normalized source bounds.
`ProductCoupledCollarHierarchy.lean` passes direct verification of physical optimization,
the finite envelope with P_N over all K²≤N, and positive bounded monotone convergence.
All 41 public theorem axiom/signature audits pass with only standard axioms. Final
direct recheck passed, exit 0, no diagnostics. All three leaves form one significant package, not three.

`update_plan` and `multi_tool_use.parallel` are unavailable. This card tracks steps; independent reads use awaited parallel promises. Existing modified files belong to other workstreams and are preserved.

## Dependency-closed proof of general partition transfer

Let N=n+2, δ=log(2)/2, L=log N, and let ρ be any PhysicalCollarPartition n.
Its defining data are measurable nonnegative shares, supported on the prescribed physical collars, summing to 1 on (δ,L) and 0 elsewhere. Let f be any compact continuous real source with the literal grid zeros, R=h_f(0), D(x)=R-h_f(x)≥0.

For every measurable nonnegative extended density F, affine substitutions x=t_k±y give

Σ_k [∫_(0,δ) ρ_k(t_k−y)F(t_k−y)dy + ∫_(0,δ) ρ_k(t_k+y)F(t_k+y)dy] = ∫_(δ,L) F.

Use ENNReal.ofReal on the shares. No finite-integral assumption is needed: the two branches recover the whole collar except its singleton center; support removes its complement; finite additivity and the partition identity recover the physical interval. Adding ∫_(0,δ) F recovers ∫_(0,L) F, with the singleton δ negligible.

For F=D w, the existing signed-coset sphere laws and shared-origin support function give pointwise Kρ(y)R≤w(y)D(y)+Σ_k,σ ρ_k(t_k+σy)w(t_k+σy)D(t_k+σy). Integrate the nonnegative inequality and apply the preceding exact transport. Since 0≤Kρ≤massρ and massρ is bounded on (0,δ), its real integral Cρ exists. Thus ofReal(Cρ R)≤∫_(0,L) F, including infinite source energy.

The supremum C*_n over partitions is finite and positive by existing duality. Taking its supremum in the bound yields ofReal(C*_n R)≤∫_(0,L) F. For finite energy and R>0, divide by R and apply the defining least-upper-bound property; R=0 and infinite energy are immediate. This also implies the full-half-line bound.

For a source on grid n, restrict to each smaller grid k≤n. Every C*_k is a valid lower bound for its full energy. Their finite maximum is therefore a positive monotone certificate. This maximum is exact only among this family of certificates; neither optimizer attainment nor equality with the source infimum is asserted.

## Quantitative allocation saturation [Lean-verified]

Write P_N for the supremum of the physical-partition coefficients on nodes 2,...,N.
This is the existing `optimalCoefficient (N-2)`, not the infimum over sources.
Then, for M≥N≥2,

    0 ≤ P_M−P_N ≤ ∫_(log N−δ)^∞ w(x) dx
      ≤ 4·2^(1/4) / (sqrt(N)·(1−2/N²)),   δ=log(2)/2.

Consequently P_N increases to a finite positive P_∞, with the same upper bound on
P_∞−P_N. The maximum over earlier P_k equals P_N by the extension theorem.
The coefficient P_N is optimal within the independent signed-coset sphere allocation
family. No claim of a sharp rate or sharpness in the full autocorrelation cone is made.

Combining this with the existing dual certificate gives, for every admissible trial
partition ρ at cutoff N,

    0 ≤ P_∞−Cρ ≤ Gρ + 4·2^(1/4)/(sqrt(N)·(1−2/N²)).

Here Gρ is its nonnegative canonical dual gap. This separates finite-allocation
optimization error from cutoff error, without an attained optimizer. The interval
encloses the allocation limit only; it does not bound the error to the sharp source
constant. Its proof adds the two existing gap inequalities.

**Finite-array comparison used in both directions.** Pad all smaller node and coset
index sets with zeros into the larger sets. Zero padding leaves mass and the sum of
block Euclidean norms unchanged. For nonnegative coordinate arrays a≤b, put
ΔB=Σ(b−a). Triangle inequality in each block gives 0≤A_b−A_a≤ΔB. For W≥0,
0≤sqrt(W²+A_b²)−sqrt(W²+A_a²)≤A_b−A_a. Thus
0≤K_b−K_a≤ΔB. This is the already formalized finite-array capacity monotonicity
law, applied after padding, not a new source assumption. Integration of ΔB equals
the deleted or added physical weight by exact affine transport.

**Monotonicity.** Given any N-partition ρ, retain its shares on (δ,log N), set its
shares to zero outside this interval, and add an M-partition (e.g. equal multiplicity)
restricted to [log N,log M). Nodes beyond N have zero retained shares. Finite
endpoints may be assigned using the M-partition; they have zero integral. This
defines a measurable supported nonnegative partition on (δ,log M). Its weights
dominate the padded original weights a.e., so its coefficient is at least Cρ.
Taking suprema proves P_N≤P_M without requiring either optimum to be attained.

**Upper comparison.** Put a_N=log N−δ≥δ. For any M-partition η, retain only its
physical shares on x<a_N. A node j>N has log j−δ>a_N, so none of its shares
survive. The retained array is therefore supported entirely on N-nodes. Fill
(a_N,log N) with the equal-multiplicity N-partition, retaining the earlier shares
on (δ,a_N). This gives an N-partition ρ. Values at the two cut points are filled
with the corresponding equal-multiplicity partition and do not change integrals.
If a is the retained padded array, capacity comparison gives

    Cη ≤ C_a + ∫_(a_N,log M)w ≤ Cρ + ∫_(a_N,∞)w ≤ P_N + ∫_(a_N,∞)w.

The identity for the removed mass follows because the original shares sum to
one above a_N. Take the supremum over η. For N=2, a_N=δ and the retained array
vanishes; the argument still applies. There is no summation over overlapping
physical intervals in this estimate.

**Tail estimate.** For x≥a>0,
w(x)=2exp(−x/2)/(1−exp(−2x))≤2exp(−x/2)/(1−exp(−2a)).
Integrating yields 4exp(−a/2)/(1−exp(−2a)). Substitution a=log N−δ gives the displayed
bound since exp(2δ)=2 and exp(δ/2)=2^(1/4). Monotonicity and the common finite mass
bound give P_∞; taking M→∞ in the comparison proves its rate.

## Candidate sharp leading saturation law [paper argument; formal audit pending]

Current implementation plan (uncounted; verified count remains 13/100):
[ ] construct an exact measurable right-node partition and concentrated extension/retraction;
[ ] prove uniform square-root fibre mass bounds and radial penalty comparisons;
[ ] integrate the concentrated penalties and identify the leading tail term;
[ ] direct leaf checks, all-theorem axiom audit, wiring, index and ledger evidence.
Reuse the existing `logarithmicCeilLag_bounds` mesh theorem; its source and compiled
artifact were inspected. Preserve the old 43 owned leaves and read-only README.
The preceding turn made verified progress; no live owned process remains from it.

Concrete formalization refinement (paper-proved, not yet counted): use the existing
ceil mesh `0≤log(ceil(exp x))−x≤exp(−x)` and a right-node partition above log 4,
with equalMultiplicity below. For N≥8, tail filling is supported on y≤1/N;
old-window repair is supported on y≤exp(δ)/N≤2/N. Thus the old 4/N repair width
can be improved without controlling the ceil index separately. Rational constants
suffice: each signed node weight≤8/sqrt(j), every old fibre mass≤32sqrt(N),
and right-cell tail mass≤64/sqrt(y) for 0<y≤1. Also 1≤2y w(y).
The radial increment obeys 2W(r_W(B)−r_W(A))≤2AG+G² when B≤A+G.
On the tail-extension interval this bounds the penalty increment by 8192;
on the repair interval it bounds the increment by 6144. Integrating gives errors
8192/N and 12288/N respectively. These coarser constants preserve leading
coefficient 4 and simplify the proof by avoiding fractional-power integration.
All pending array bounds must be instantiated by the actual extension/retraction;
generic perturbation lemmas alone do not complete this contribution.

The preceding one-sided rate can be sharpened on paper to

    P_∞−P_N = 4/sqrt(N) + O(1/N),   N→∞.

This is a claim about P_N, the independent signed-coset allocation optimum only.
It is NOT asserted for the full Schur-coupled or actual-source constant. It is not
counted as a completed contribution before the construction and bounds are formalized.

Here is a full quantitative argument to audit. Set d=2^(1/4), c=4d, a=4c,
b=2c, g=2sqrt(2)c. For all 0<y<δ and integer j≥2,

    w(log j±y) ≤ c/sqrt(j),       1/w(y) ≤ d y.

The first follows from w(x)=2exp(−x/2)/(1−exp(−2x)), exp(2δ)=2 and j²≥4.
For the second, sinh y=∫_0^y cosh t dt≤y exp y. Every share on an indexed
node is at most 1. Hence any N-partition, and any coordinatewise subpartition,
has aggregate block norm A(y)≤total mass density≤2cΣ_(j=2)^N j^(−1/2)≤a sqrt(N).
The sum inequality follows by integration of decreasing x^(−1/2) on [1,N].

Put r_W(A)=sqrt(W²+A²)−W. Since 0≤r_W(A)≤A≤mass, all finite partition
coefficients can be written as total physical mass minus ∫r_W(A), with both
terms finite. For A,G≥0 and W=w(y)>0,

    0 ≤ r_W(A+G)−r_W(A) ≤ (2AG+G²)/(2W) ≤ d y(AG+G²/2).    (*)

This is rationalization of the two square roots. Blockwise triangle inequality
allows G to be the sum of block norms of any added array, even when old/new
weights lie in the same odd coset.

**Lower bound on the missing tail (N≥4).** Extend any N-partition to M>N by
assigning every cell (log(j−1),log j], N<j≤M, entirely to its right node j.
These cells are valid left collars since log(j/(j−1))≤1/(j−1)≤1/N<δ.
Keep old shares on x<log N. At the junction x=log N, assign unit share to
the old node N; truncate every new cell by the open M-window, so x=log M
receives no share. These singleton corrections are required by the exact
physical partition law: the uncorrected half-closed cells omit log N and include
log M. Old signed fibres are unchanged at every y>0, since the only old-node
correction is at its own zero offset. New densities vanish unless 0<y≤1/N.
An active j also satisfies j≤1+1/y. Therefore their aggregate norm obeys

    G(y) ≤ cΣ_(j=2)^(floor(1+1/y)) j^(−1/2) ≤ g/sqrt(y),

using y≤1/N≤1. By (*) and A≤a sqrt(N), the increase of the integrated
radial penalty is at most

    d∫_0^(1/N) [a g sqrt(N) sqrt(y)+g²/2]dy
      = K_−/N,        K_−=d(2ag/3+g²/2).

Thus P_M≥P_N+∫_(log N,log M)w−K_−/N. No optimizer is required: the construction
works for every old partition, and taking its supremum proves the inequality.

**Upper bound on the missing tail (N≥4).** Given any M-partition, delete all
nodes j>N and all physical shares above log N. Keep the remaining old-node
shares below log N. The missing physical fraction below log N lies only where
x>log(N+1)−δ. Assign that fraction to j=ceil(exp x)≤N, using the half-closed
cells (log(j−1),log j]. Here j>(N+1)/sqrt(2), so j≥4 and j−1>N/4; the
new offset y=log j−x satisfies 0≤y<4/N and is within the collar radius.
This produces a valid N-partition. Zero offsets and cell endpoints are null
for the integral and receive their exact partition values from the same rule.

Let A be the retained aggregate norm and G the filling norm. Then
A≤a sqrt(N), G≤b sqrt(N), and G=0 for y≥4/N. The original M-array dominates
the retained array, so its radial penalty is no smaller than the retained penalty.
The new N-array adds at most

    d(ab+b²/2)N∫_0^(min(δ,4/N)) y dy ≤ K_+/N,
    K_+=8d(ab+b²/2).

Its total physical mass differs from the original by exactly ∫_(log N,log M)w.
Therefore P_M≤P_N+∫_(log N,log M)w+K_+/N. Taking the supremum over M in
both estimates gives, with T_N=∫_(log N,∞)w,

    T_N−K_−/N ≤ P_∞−P_N ≤ T_N+K_+/N.

Finally

    0 ≤ T_N−4/sqrt(N) ≤ (4/5)N^(−5/2)/(1−N^(−2)),

by subtracting 2exp(−x/2) from w and integrating the remainder bound
2exp(−5x/2)/(1−N^(−2)) for x≥log N. This proves the stated leading law
at paper level, subject to formal verification of these explicit constructions.

The key mechanism is concentration of added/repair collars into an O(1/N)
origin-offset interval. Physical tail mass is order N^(−1/2), but its extra
shared-origin radial penalty is only order N^(−1). This identifies why the
independent-sphere allocation hierarchy has a tail-driven leading coefficient.

## Boundaries and next conjecture

- A fixed narrow smooth source gives a finite N-independent upper bound. Divergence as log N→∞ is impossible for this admissible class.
- Arbitrary physical overlap allocation must conserve density. Origin weight cannot be spent once per odd coset.
- Schur residuals are not yet included in C*_n. Its sharp convex allocation certificate is not a proof of global correlation sharpness.
- Compatible partition extension and retraction formalize monotonicity and the explicit
  inverse-square-root upper bound. The leading coefficient 4 still requires formal audit
  of the concentrated collar construction.
- Stronger Schur-coupled certificates require control of actual cross-coset Gram entries.

### Signed Gram constraint activation: next coupling audit

Do not extend the allocation tail law to a full signed Gram model without a new proof.
For positive nodes a,b, equal-sign frame differences are log(a/b); opposite-sign
differences are ±log(ab). Thus a larger cutoff can add constraints between nodes that
were already present: the cross entry between −log2 and +log3 becomes forced zero
when cutoff reaches 6. It is not forced by the cutoff-3 grid alone. A narrow two-packet
source at spacing log6 has h(log2)=h(log3)=0 but h(log6)>0; widths can be chosen below
all the finitely many nonzero separation distances. This source claim is a paper
construction, not a separately audited Lean theorem.

For the symmetric node set {±log j:2≤j≤K}, all integer-log zero-edge data stabilize
once N≥K²: same-sign integer quotients are at most K and opposite-sign products
are at most K². This exact arithmetic observation identifies a second cutoff scale
for a Schur-complete signed Gram relaxation. It does not prove a convergence rate
for that relaxation, and no rate is inferred from it here.

Further Schur coupling must retain all forced quotient/product zero entries and
nonzero Gram compatibility beyond the paired product-zero constraints proved here.
The existing Gram remainder and synchronized
coset sine estimates are inputs. Audit physical overlap and true-source sharpness
separately; a finite PSD completion need not be a translation autocorrelation.

**Verified sign-coupled construction.** If the actual source is pinned through N and
K²≤N, then every translate at +log j is orthogonal to every translate at −log k
for 2≤j,k≤K, because their cross correlation is h(log(jk))=0. For nonnegative
signed collar weights on the K-grid, let A_+ and A_- be the sums of the within-sign
odd-coset Euclidean norms. The two aggregate Hilbert packets are orthogonal, and
each has norm at most sqrt(R)A_±. Their combined norm squared is therefore at most
R(A_+²+A_-²), replacing the old R(A_++A_-)² bound. Both packets are orthogonal to
the origin source as well. One final Hilbert Cauchy–Schwarz inequality gives

    W(R−h(y)) + Σ_(j,σ) a_(j,σ)(R−h(log j+σ y))
      ≥ R[W+B−sqrt(W²+A_+²+A_-²)].

Here W=w(y)>0 and B=Σa. Relative to the same physical partition's independent
signed-coset bound, the pointwise improvement is exactly

    2 A_+ A_- /
      [sqrt(W²+(A_++A_-)²)+sqrt(W²+A_+²+A_-²)].

Signed physical transport is unchanged, so the existing general partition machinery
integrates this bound on (0,log K). This is a direct route to coupling distinct odd
cosets across collar signs, rather than assuming the signed block independence is
sharp. The paired-sphere proof below discharges the actual zero-product constraints
and yields the integrated coefficient; both steps are now Lean-certified.

Guard for a full-N implementation: splitting each existing coset into low/high pieces
can enlarge the sum of block norms. The crude bound
sqrt(A_+low²+A_-low²)+A_high need not dominate the old all-node bound; take the
minimum of the two valid norm bounds or prove a stronger combined estimate. The
pure K-grid construction above has no such splitting loss.

**Finite convex proof avoiding packet expansion.** For every positive-sign coset p
and negative-sign coset q, the union of their signed nodes and the origin is an
orthogonal frame when K²≤N. Bessel gives

    u₀² + ||u_p^+||₂² + ||u_q^-||₂² ≤ R².

Take r_± to be the maxima of the finitely many block norms on each sign. Choosing
the two maximizing blocks shows u₀²+r_+²+r_-²≤R². Blockwise Cauchy–Schwarz bounds
the weighted sum by W u₀+A_+r_++A_-r_-, and the three-dimensional sphere bound
gives exactly R sqrt(W²+A_+²+A_-²). This only requires the paired clique spheres,
so the existing `autocorr_origin_chain_sphere_sub_le` and
`sphere_weighted_sum_le_sqrt_mul` provide a smaller formal route than expanding
all cross-coset packet products. Signed node orthogonality still must be proved
from the literal grid zeros; it is not an input source premise.

This support function is sharp for the finite paired-sphere relaxation. If
Z=sqrt(W²+A_+²+A_-²)>0, choose u₀=RW/Z and each nonzero-weight block on sign σ
parallel to its weight vector with norm RA_σ/Z; choose zero for zero-weight blocks.
All paired constraints hold and the support value is RZ. Z=0 is immediate.
This attainment is a finite-vector statement, not autocorrelation realizability.
The positive-W support theorem and its finite-vector attainment are Lean-certified;
they are counted together with actual source transport and the monotone hierarchy.

## Full-grid coupling without splitting loss [Lean-verified]

The full-grid refinement retains nodes above sqrt(N). In each signed
coset split its coefficient vector into low nodes j≤K and high nodes j>K, K²≤N.
Let L_(σ,m), H_(σ,m) be their Euclidean norms. Existing whole-coset spheres give
u₀²+||u_low||²+||u_high||²≤R²; product zeros add every opposite-sign low-block pair
constraint u₀²+||u_low,+||²+||u_low,-||²≤R².

For t∈[0,1], define the exact capped two-coordinate support

    F_(L,H)(t) = max_{x²+z²≤1, 0≤x≤t, z≥0}(Lx+Hz).

For L²+H²>0, this is sqrt(L²+H²) when t≥L/sqrt(L²+H²), and
Lt+H sqrt(1−t²) otherwise. For L=H=0 it is zero. Put

    Z = max_{t_+²+t_-²≤1, t_±≥0} Σ_(σ,m) F_(L_(σ,m),H_(σ,m))(t_σ).

Then the exact support of the stated finite sphere relaxation is
R sqrt(W²+Z²). To prove the upper bound, fix u₀, divide each residual block by
r=sqrt(R²−u₀²), and choose t_σ as the maximum low-block norm on sign σ. Their
paired constraints give t_+²+t_-²≤1. Blockwise Cauchy gives each capped support.
The r=0 case is immediate. Compactness attains Z; block vectors parallel to their
weight subvectors attain each capped support, and the final two-coordinate sphere
attains the W/Z combination. Zero subvectors cause no difficulty.

Crucially Z≤Σ_(σ,m)sqrt(L_(σ,m)²+H_(σ,m)²), the old whole-coset norm bound.
Thus this construction retains high-node mass and cannot worsen the old coefficient;
it avoids the unjustified separate low/high triangle bound. The exact cap formula,
compact maximization and continuity, upper support, and finite-vector attainment
are certified in `CappedBlockSupport.lean` and `CappedCosetSphereDuality.lean`.
`FullGridCappedCollarEnergy.lean` proves measurable physical composition,
integrability, domination of the original kernel/coefficient, and actual source
transfer on the full interval (0,log N). For every physical partition ρ and
K²≤N, its capped coefficient B_(N,K)(ρ) satisfies

    oldCoefficient_N(ρ) ≤ B_(N,K)(ρ) ≤ J_arch(f)/h_f(0).

The extended-energy version includes zero sources and infinite energy. The ratio
version uses the actual nonzero compact C² grid-source domain. The capstone
`fullGrid_capped_energy` chooses K=floor(sqrt N), N≥4, with no caller-supplied
analytic interface. All three leaves compile, all 41 public theorem axiom/signature
audits pass with standard three axioms, and the final direct source-leaf check
passes without diagnostics. This is one package.

All-low equality with the previous paired support, cutoff monotonicity, and an
upper error estimate for the new coefficient are formalized in the next package.
The activation criterion below is Lean-verified; true source realization remains
unformalized.
General nonzero Schur coupling remains open. The uniform
low cutoff also leaves unused product-zero pairs with unequal node sizes; retaining
those is a further refinement. Corpus searches `/tmp/bsu-capped-block-search.log`
and `/tmp/bsu-fullgrid-cap-search.log` supplied generic support/compactness inputs;
semantic coverage is unmeasured, so no exhaustive novelty claim follows.

## Full-grid cutoff hierarchy [Lean-verified]

At fixed cap t, increasing both nonnegative weights changes F by between zero
and the sum of their increases: evaluate each support on an attained disk point,
whose coordinates lie in [0,1]. Finite sums, the compact maximum, and the final
radial Euclidean norm preserve this unit l1 bound. Block norm changes are at most
added coordinate mass. Thus adding physical capacity increases the capped kernel
by between zero and added mass.

At fixed whole-block norm, moving weight norm from H to L decreases F. If the
old cap is inactive this follows from F≤sqrt(L²+H²). Otherwise both formulas
are boundary formulas. Put b=sqrt(1−t²), ΔL=L'−L≥0, ΔH=H'−H≤0. Sphere
convexity gives LΔL+HΔH≤0, while the binding cap implies bL≥tH. Multiplying
and combining gives H(tΔL+bΔH)≤0. H=0 forces ΔL=ΔH=0; otherwise division
proves the required support decrease. Therefore increasing the admitted low
cutoff increases the kernel, with all high nodes retained.

Zero-padding into a larger physical grid preserves each low/high block norm and
adds only zero-weight coset labels. Actual partition extension then proves the
two-parameter optimized coefficient B_(N,K) is nondecreasing when both cutoffs
increase and K≤N. The all-low identity is B_(N,N)=Q_N because F(L,0,t)=Lt.
It gives B_(N,K)≤Q_N, while extending any K-grid partition gives Q_K≤B_(N,K).
Together with P_N≤B_(N,K), this yields C_N≤B_(N,floor√N)≤Q_N≤Q_∞, hence
the same finite limit and inherited explicit fourth-root upper error. All these
comparisons are now Lean-certified before importing the earlier rate.

Define B_N=B_(N,floor√N) for N≥4 and B_N=P_N for N=2,3. The preceding
comparisons prove actual monotonicity, positivity, and B_N↑Q_∞. In particular,

    0 ≤ Q_∞−B_N ≤ 16 exp(δ/2)/N^(1/4),   N≥4,
    B_N ≤ J_arch(f)/h_f(0)

for every actual nonzero compact C² N-grid source. The ENNReal version retains
the full interval (0,log N), zero sources, and infinite energy. No analytic
interface is a caller premise. The inherited upper error is not asserted sharp;
strict finite improvement over C_N, source realization, and general nonzero
Schur residual coupling remain open. Full-grid retention in this uniform-low
model changes the finite certificate without changing its limiting value.

Current corpus search `/tmp/bsu-capped-capacity-search.log` returned reusable
capped support, paired radial capacity, and array comparison inputs (156 matches
in 45 modules; 68 after the module cap). Retrieval is partial, with older indexed
coverage and unmeasured semantic coverage; this is not exhaustive novelty evidence.

## Full-grid activation criterion [Lean-verified]

For each signed block let U=sqrt(L²+H²), and let its low fraction be L/U
when U>0, otherwise zero. Let α_σ be the maximum low fraction on sign σ
(include zero for an empty family). The capped support equals the independent
whole-block support if and only if α_false²+α_true²≤1. Otherwise it is strictly
smaller. Thus high-node weight can absorb the product constraint: positive low
weights alone do not force improvement.

Proof: each capped block support is at most U. For U>0, equality in the
two-coordinate Cauchy inequality forces the unique normalized direction
(L/U,H/U); this direction is feasible exactly when t_σ≥L/U. Zero blocks impose
no restriction. The finite sum reaches its independent upper bound exactly
when every nonzero block reaches its own upper bound. Compact attainment of
the outer maximum makes this equivalent to simultaneous cap feasibility.
Such caps exist precisely when α_false²+α_true²≤1; choose t_false=α_false
and t_true=sqrt(1−α_false²). The common-origin square root is strictly
increasing in nonnegative angular support, so the same strictness criterion
holds for the pointwise energy kernel. An integrated strict gain additionally
requires strict activation on a positive-measure set. Both finite and physical
leaves compile without diagnostics; all 26 public theorem axiom/signature audits
and final direct physical-leaf check pass. The physical strictness theorem is
stated as failure of the almost-everywhere inactivity condition.

Quantitative form: an attained scalar disk point (x,z) satisfies
2U(U−F)=(Ux−L)²+(Uz−H)². If L>tU, its first square is at least
(L−tU)², giving a division-free positive deficit. At the physical level, write
S for the independent sum of whole-block norms and Z for capped support. The
gain is exactly (S²−Z²)/(sqrt(W²+S²)+sqrt(W²+Z²)), W=w_arch(y)>0.
It is measurable and integrable because it equals cappedKernel−kernel.
Its integral vanishes iff the fraction criterion holds almost everywhere on
(0,δ); strict gain is equivalent to failure of that almost-everywhere condition.
The actual source bound becomes J/h0≥oldCoefficient+integral(gain), with no
caller-supplied analytic premise. This package does not establish a strict gap
between suprema over partitions, or realize a finite optimizer by a source.

Current corpus query `/tmp/bsu-capped-activation-search.log` supplies capped
attainment/formula and the paired rationalization precedent; 213 declarations
in 56 modules, 82 after the cap. Retrieval is partial; no exhaustive novelty claim.

## Quantitative product-coupled saturation [Lean-verified]

Write Q_K for the optimized paired physical coefficient. For nonnegative arrays,
coordinate addition changes each sign's aggregate norm by a nonnegative amount
bounded by the added weight mass. The Euclidean norm of (W,A_+,A_-) is monotone
on its nonnegative coordinates and 1-Lipschitz in their l1 distance. Hence the
paired kernel has the same two capacity bounds used for P_K: it is coordinatewise
nondecreasing and its increase is at most added mass. Zero-padding preserves both
sign norms. The already constructed physical extension and retraction now
prove, by exactly the same physical transport argument,

    Q_K ↑ Q_∞,   0≤Q_∞−Q_K≤∫_(log K−δ)^∞w
      ≤4·2^(1/4)/(sqrt(K)(1−2/K²)).

The paired capacity comparisons are independently proved in Lean; the P_K rate alone
does not prove them. The coupled hierarchy C_N=max(P_N,max_(K²≤N)Q_K) has limit Q_∞:
every Q_K is eventually admitted, while P_K≤Q_K and all admitted Q_K≤Q_∞. Thus for
every admitted K, its error is bounded by the displayed tail at K, yielding an
O(N^(−1/4)) bound on taking K=floor(sqrt N). Lean also proves the exact identity
C_N=max(P_N,Q_floor(sqrt N)) for N≥4, and the uniform upper error
16·2^(1/4)/N^(1/4). Actual smooth grid-source energy is at least Q_∞ minus this
error. This is a quantitative certificate for the product-coupled subhierarchy,
not for the full Gram cone.

The concentrated-tail proof for leading coefficient 4 also appears to extend to
Q_K, using the squared Euclidean sign norm and the same l1 upper estimates. If
both leading laws are proved, the eventual rate of C_N depends on whether
Q_∞>P_∞: a strict gap makes the paired branch dominate with scale N^(−1/4);
equality makes the independent branch dominate with scale N^(−1/2). Strict
improvement of the limiting optimum is presently unproved. Do not infer it merely
from the positive gain for some fixed physical partitions.

## Two-column Schur support and physical splitting [Lean verified]

For two real vectors u,v on a finite frame, write U=Σu², V=Σv², D=Σuv.
The Schur domain is U≤R², V≤R², (Rc−D)²≤(R²−U)(R²−V), R≥0.
For every real r,s, its residual quadratic form is nonnegative, hence

    Σ(ru+sv)² ≤ R²(r²+s²)+2Rc rs.

Proof: set A=R²−U, B=R²−V, C=Rc−D. If A>0, multiply
Ar²+2Crs+Bs² by A to obtain (Ar+Cs)²+s²(AB−C²)≥0.
If A=0, C=0 follows and the claim is immediate. This retains general measured
lag c; zero target lag c=0 makes every unit rotation a simultaneous Bessel pair.

For weight vectors a,b define A=Σa², B=Σb², C=Σab and

    ν(a,b)=sqrt(A+B+2 sqrt(AB−C²)).

The zero-lag Schur support is exactly Rν(a,b). Rotate both weights and states
by the same real unit rotation until the two rotated weight vectors are
orthogonal. The Lean construction uses a polynomial intermediate-value argument:
q(t)=(1−t²)C+t(B−A) takes opposite endpoint values at −1 and 1.
For a root t, use r=1/sqrt(1+t²), s=t/sqrt(1+t²). Then r²+s²=1 and
the rotated pairing is q(t)/(1+t²)=0. The two rotated state norms
are at most R, so support is at most R times the sum of rotated weight norms.
The sum squares to A+B+2sqrt(AB−C²), because trace and Gram determinant are
rotation invariant. For attainment, take the two normalized orthogonal rotated
weight directions (zero on zero blocks), scale by R, and rotate back. This is
finite-vector attainment, not autocorrelation realization. In particular
ν≤sqrt A+sqrt B, with equality exactly when C=0.

Actual source receiver: for d=log2, the frame {0,d,2d} is orthogonal under
N≥4 grid pinning. Targets y and y+d have zero mutual correlation. Their
columns are (u0,u1,u2) and (v,u0,u1), where u0=h(y), u1=h(d−y),
u2=h(2d−y), v=h(d+y). Thus each coefficient split λ,μ∈[0,1] yields

    W u0+a u1+b u2+c v ≤ R ν((λW, μa, b), (c,(1−λ)W,(1−μ)a)).

Optimize the right side over the compact square. Its minimum is continuous in
the four weights, at least W for nonnegative W,a,b,c (test the feasible matrix
with columns (1,0,0),(0,1,0)), and at most W+a+b+c. The corresponding kernel
is therefore nonnegative and at most a+b+c. Use actual physical weights on
the two sides of node2 and the left side of node4; every unselected term in
the physical source fibre is nonnegative. Pointwise max with the existing
capped kernel retains all previous bounds and integrates by exact signed
physical transport. Let Tρ be the integral of this maximum kernel, and let
T_N=supρ Tρ for N≥4, with T_N=P_N for N=2,3. The finite envelope
H_N=max_(2≤K≤N) T_K is monotone. Each source on the N-grid restricts to
every smaller K-grid; applying the K-certificate to that same source proves
H_N≤J_arch(f)/h_f(0). This does not assume monotonicity of the raw T_N.

Both kernels lie between zero and the full allocated mass. Exact transport
therefore gives Tρ≤∫_(δ,log N)w≤tailMass independently of ρ and N.
Suprema and the finite envelope yield 0<B_N≤H_N≤tailMass, where B_N
is the previous full-grid capped coefficient. Thus H_N increases to a finite
H∞, and Q∞≤H∞≤tailMass. No equality with Q∞, rate to H∞, or sharp
actual-source asymptotic follows from this comparison. The extended-energy
theorems retain zero sources and infinite energy; C² and h(0)>0 enter only
when converting to the normalized real-energy ratio.

Strict finite-cone separation: with W=a=b=1,c=0 and λ=μ=1/2, the displayed
support squared is 2+sqrt(3)/2<3, whereas the independent origin/clique sphere
support is sqrt3. This is an exact symbolic comparison, not a numerical
experiment. It does not establish strict improvement for optimized physical
partitions or a sharp actual-source constant. The general nonzero measured-lag
rotation theorem remains distinct from the zero-lag support specialization.

Corpus evidence: `/tmp/bsu-schur-pair-search.log`, 669 declarations in 67 modules,
117 after module cap, partial retrieval and older indexed coverage. The actual
Schur and source Bessel theorems are verified inputs. Scoped exhaustive text
search found no two-column/nuclear-support declaration in BiScaleUncertainty;
no exhaustive mathematical novelty claim is made. Do not broaden searches
into unrelated research cards.

## Accounting

### Updated field guidance and signed receiver [Lean verified]

Read all 242 lines of the relocated, read-only
`formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (SHA-256
`80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507`).
Its homogeneous-blind-subspace obstruction requires retaining measured signed
node correlations. The existing H_N theorem remains a grid-blind specialization,
not a general signed-correlations result. Stay on multi-coset source-energy
constants; do not adopt the README's separate RH/prime-polar research objectives.

The corpus supplies `translationPacket_correlation_le`, which retains the entire
measured Gram matrix. For an arbitrary compact continuous source, put R=h(0),
take signed nodes τ_i and nonnegative weights a_i, and let A=Σa_i. Anchor the
packet at node 0 with weight W≥0. Its full Gram energy is

    G=R W²+2W Σa_i h(τ_i)+Σ_i,j a_i a_j h(τ_j−τ_i).

The packet bound gives W h(y)+Σa_i h(τ_i−y)≤sqrt(RG). Consequently
K=R(W+A)−sqrt(RG) bounds the actual weighted origin-plus-collar increment.
All signed node values and cross-coset entries remain present.

The pointwise envelope |h|≤R gives G≤R(W+A)² and hence K≥0. Evaluating
the same packet bound at y=0 gives sqrt(RG)≥RW+Σa_i h(τ_i)≥RW−RA.
Thus K≤2RA: the singular origin weight cancels exactly, without an origin
cutoff, derivative bound, or artificial truncation of the certificate.
The same origin evaluation gives the stronger capacity law
K≤Σa_i(R−h(τ_i)). It retains the measured signed node deficits and reduces
to RA on the blind grid.

For the full physical array take τ_(false,k)=log(k+2), τ_(true,k)=−log(k+2),
and a_(σ,k)=ρ.weight σ k y. Evenness identifies both signed physical costs.
The bound 2R massρ(y) proves integrability. Exact signed transport yields the
extended-energy bound for every f:C_c(ℝ,ℝ), without grid zeros, supplied Gram
data, or an analytic-energy interface. C² regularity converts it to real energy;
normalization divides both sides by R, including total division at R=0.
On the blind-grid domain, taking the maximum with H_N retains both certificates.
This source-dependent signed coefficient is not a uniform constant for arbitrary
unconstrained sources, and is not identified with the sharp source infimum.

The full signed physical receiver is part of the same Schur package, not a
separate contribution count. Exact nonzero-lag multi-column support and growth
of optimized signed-data certificates remain substantive next targets.

Ten significant packages are Lean-verified, including all axiom/signature audits:
(1) arbitrary-partition energy transfer and optimized certificates;
(2) actual cutoff monotonicity, retraction stability, and quantitative saturation;
(3) paired-sphere support, actual product-zero source transfer, and monotone coupled hierarchy;
(4) paired capacity, cutoff stability, exact frame/limit identification, and fourth-root cutoff control;
(5) exact capped support, finite-vector attainment, and full-grid physical source transfer;
(6) full-grid capped capacity, cutoff monotonicity, optimized hierarchy comparison,
common finite limit, and quantitative actual-source certification;
(7) exact capped activation, quadratic extremal defect, rationalized physical gain,
almost-everywhere equality/strictness classification, and actual-source gain transfer;
(8) exact two-column Schur support, optimized dyadic physical refinement and
monotone hierarchy, plus the unconditional full measured signed-Gram receiver;
(9) full measured signed-Gram capacity, actual physical cutoff monotonicity and
retraction, optimized finite limit, inverse-square-root error, and actual-source receiver;
(10) full measured-Gram dual support, exact physical dual gap and complementarity,
finite-allocation error and quantitative limiting actual-source trial certificates.
At the package-10 audit, the cumulative count was **10/100**. Its three leaves form one package.
At the package-10 audit, global lint reported twelve unrelated unwired modules.
Do not count reused shared-origin geometry or individual helper lemmas. Matching
leading asymptotics remain paper-only. Both activation leaves form one package.
This turn made concrete progress; the full objective
remains active and incomplete.

## Verification evidence

- Leaf: `formal/GaloisForLFunctions/BiScaleUncertainty/PhysicalCollarSourceEnergy.lean`.
- Final direct command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PhysicalCollarSourceEnergy.lean -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/PhysicalCollarSourceEnergy.olean`: exit 0, no diagnostics.
- Source SHA-256: `423ca0e7d1957c5898bac5ff228e6989d255c98e2fe24ec621775f76d3574792`.
- All 19 public theorems pass `/tmp/bsu_physical_source_axioms.lean`, exit 0. Only
  `propext`, `Classical.choice`, and `Quot.sound`; no extra axioms or computation axioms.
  Printed principal signatures and the smooth-source subtype confirm no hidden analytic premise.
- Own umbrella import present. Index regeneration passed; source declarations discoverable.
- At the package 7 audit, `scripts/formal_tools.py lint`: exit 0, `formal lint passed`.
  See package 10 for the latest concurrent missing-import failures. Evidence:
  `/tmp/bsu-capped-activation-lint.log`.
- Logs: `/tmp/bsu-physical-source-{final,axioms,index,lint}.log`.
- No full or umbrella build, numerical experiment, added axiom, heartbeat increase, or commit.
- Cutoff leaves: `PhysicalCollarCutoffMonotonicity.lean` and `PhysicalCollarCutoffStability.lean`.
  Both produced compiled outputs without diagnostics. All 35 public theorem scratch axiom
  audits passed (exit 0), only `propext`, `Classical.choice`, and `Quot.sound`.
  Printed principal signatures confirm no hidden analytic premise.
- Cutoff SHA-256: monotonicity `e9ebaca82b8d817c28826c64ac54fb77e81dc5823f71b3329fea4110e0eb6586`;
  stability `b3d464f73df171bc2e7f8a062697c15518a63df9a8c9b3bdc2ff3ed940264246`.
- Cutoff logs: `/tmp/bsu-cutoff-check.log`, `/tmp/bsu-cutoff-stability-check.log`,
  `/tmp/bsu-cutoff-{axioms,final,index,lint}.log`; scratch `/tmp/bsu_cutoff_axioms.lean`.
- Final cutoff command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PhysicalCollarCutoffStability.lean`, exit 0, no diagnostics.
- All owned processes exited; successful audit scripts/logs are retained. Temporary
  cutoff API probe files are removed. Scoped whitespace checks pass.
- Product-coupling leaves: `PairedCosetSphereDuality.lean`, `SignedCosetProductCoupling.lean`,
  `ProductCoupledCollarHierarchy.lean`; each direct compilation exited 0 without diagnostics.
  All 41 public theorem axiom audits exited 0, only `propext`, `Classical.choice`, `Quot.sound`.
- Product-coupling hashes: geometry `377bf1eef09bb7190e186f533bc5e8c80cc0bd25e426648e219a103c0ff19d9f`;
  source `c26fc3d7f4f1d4e4ad123135d733a59fae96c940ddc9c5821a27c4b0eff029dc`;
  hierarchy `e78c3e45cc9bcd200840dbfcb40d1a41fa3ff49396b875f98a05850eca6b3156`.
- Logs: `/tmp/bsu-paired-geometry.log`, `/tmp/bsu-signed-coupling.log`, `/tmp/bsu-product-hierarchy.log`,
  `/tmp/bsu-product-coupling-{axioms,final,index,lint}.log`;
  scratch `/tmp/bsu_product_coupling_axioms.lean`. Own imports and fresh index entries verified.
- Final direct command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/ProductCoupledCollarHierarchy.lean`, exit 0, no diagnostics.
  All owned processes are terminal; temporary paired API probe removed. No numerical
  experiment, added axiom, heartbeat increase, full build, commit, or push.
- Paired-cutoff leaves: `PairedCollarCapacity.lean`, `PairedCollarCutoffStability.lean`.
  Both direct compilations and all 30 public theorem axiom/signature audits exited 0;
  no diagnostics, only `propext`, `Classical.choice`, `Quot.sound`.
- SHA-256: capacity `215adfa612eb4e9eef6d1025d51de02109b3d2b0a157828441b4068c83030863`;
  stability `e2f4d2b569d6df1efd3e4e65444f9e025408ee34d1c9fe83973e273334eec19c`.
- Logs: `/tmp/bsu-paired-capacity.log`, `/tmp/bsu-paired-stability.log`,
  `/tmp/bsu-paired-cutoff-{axioms,final,index,lint}.log`;
  scratch `/tmp/bsu_paired_cutoff_axioms.lean`. New imports and index entries verified;
  scoped whitespace clean. Final direct command
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PairedCollarCutoffStability.lean`
  exited 0 without diagnostics. All owned jobs exited; temporary API probe removed.

- Full-grid leaves: `CappedBlockSupport.lean`, `CappedCosetSphereDuality.lean`,
  `FullGridCappedCollarEnergy.lean`; all direct compilations and all 41 public
  theorem axiom/signature audits pass. Only `propext`, `Classical.choice`, `Quot.sound`.
- SHA-256: block `3004dced418ed93f074aa177cd75cf7bd841200f6af3328538e5cd2863355406`;
  cosets `b6e3bd890950ae1874e4c4ef87a30d383d1d4360768ffdad607e2b8505d811c5`;
  source `6a8bcfaba9f2647cdeadc59abc68a5cf7724c4a3c58e049120c7922553503b0d`.
- Evidence: `/tmp/bsu-capped-block.log`, `/tmp/bsu-capped-cosets.log`,
  `/tmp/bsu-fullgrid-capped.log`, `/tmp/bsu-fullgrid-capped-{axioms,final,index,lint}.log`,
  `/tmp/bsu_fullgrid_capped_axioms.lean`. All new imports and capstone index entries checked.
  Final command `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FullGridCappedCollarEnergy.lean`
  exited 0 without diagnostics. All eight earlier source hashes remain unchanged.

- Full-grid hierarchy leaves: `CappedSupportComparison.lean`,
  `CappedCollarArrayComparison.lean`, `CappedCollarCutoffComparison.lean`, and
  `FullGridCappedCollarHierarchy.lean`. All compiled without diagnostics; all 58
  public theorem axiom/signature audits pass, only `propext`, `Classical.choice`,
  and `Quot.sound`. Printed capstones and source/coefficient definitions were inspected.
- SHA-256: support comparison `4f6f50c1f75d890d7f06a891dcca531c103eb15c01bbe2cf5cc13b276c1ccca3`;
  array comparison `9656cd0ce211de779e6dbfefd70a35950e7d761b65c93e6418b1be80a200fd43`;
  cutoff comparison `d597b18ce4c9910cccfb22975c72ad6646ff8113781471dbb0795fcd460ec4ec`;
  hierarchy `72320630cda08587f8830f795984fb6c44ab1c98904049f64ec7817f789a8ffa`.
- Evidence: `/tmp/bsu-capped-{support-comparison,array-comparison,cutoff-comparison,hierarchy}.log`,
  `/tmp/bsu-capped-hierarchy-{axioms,final,index,lint-final}.log`, and
  `/tmp/bsu_capped_hierarchy_axioms.lean`. Audit coverage matches all 58 public
  theorem names exactly once. All eleven earlier source hashes remain unchanged.
- Final direct command:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FullGridCappedCollarHierarchy.lean`;
  exit 0, no diagnostics. All fifteen own imports and refreshed capstone index entries
  verified. All owned jobs exited; temporary capacity API scratch removed with
  `apply_patch`. No full build, numerical experiment, heartbeat increase, or commit.

- Activation leaves: `CappedSupportActivation.lean` and `PhysicalCappedActivation.lean`.
  Both compile without diagnostics. All 26 public theorem axiom/signature audits
  pass with only `propext`, `Classical.choice`, and `Quot.sound`. Audit coverage
  matches all public theorem names exactly once; printed capstone and gain/source
  definitions confirm no hidden analytic interface.
- SHA-256: finite activation `1625673ef2d59453edef68fa71f6422b5904c90106d5d0b77e91ce1fb492bce3`;
  physical activation `6495929af4fe9b23b2853cca2c355002b73e5755d3473695f040f9beef3e4d4b`.
- Evidence: `/tmp/bsu-capped-support-activation.log`, `/tmp/bsu-physical-capped-activation.log`,
  `/tmp/bsu-capped-activation-{axioms,final,index,lint}.log`,
  `/tmp/bsu_capped_activation_axioms.lean`. All fifteen earlier source hashes unchanged.
- Final command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PhysicalCappedActivation.lean`;
  exit 0, no diagnostics. New imports and capstone index entries verified; global
  lint passes. All owned jobs exited; temporary API probe removed with `apply_patch`.
  No full build, numerical experiment, heartbeat increase, commit, or push.

- Schur package: `TwoColumnSchurGeometry.lean`, `TwoColumnSchurSupport.lean`,
  `DyadicSchurSupport.lean`, `DyadicSchurCollarEnergy.lean`,
  `SchurCappedCollarHierarchy.lean`, and `SignedPhysicalGramEnergy.lean`.
  All six compile without diagnostics. All 85 public theorem axiom/signature
  audits pass: 69 in `/tmp/bsu_schur_pair_axioms.lean`, 16 in
  `/tmp/bsu_signed_physical_gram_axioms.lean`; every public theorem exactly once,
  only `propext`, `Classical.choice`, `Quot.sound`. General source signatures and
  actual Gram/kernel definitions were printed and inspected.
- SHA-256: geometry `91e66c439bb52ef3cc5f0fb32fc15e47c2614949a8d10d23620e90ae46c29ab9`;
  support `249f9bea751b9ba8c5a5ce8c88fd1c6b3c3cab292266c8cbf95bba37be9e7980`;
  dyadic `37f23f952324a5bc85b3a628e4b2994ccbc99a94a80c6e1cbd2fdf884327ef30`;
  physical `c120590bca4fb721c66ea317804b9631cc90d7e582d7ddbb2664da08212fd5a9`;
  hierarchy `8ef01a80da29ed464c42d9df631539908297b10158cb6c5606967ecf855ee573`;
  signed Gram `9dc409594e17bd54b97b38b351addc11dd869ebea53f14d4c1087c3151383c33`.
- Final direct command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedPhysicalGramEnergy.lean`;
  exit 0, no diagnostics. Evidence: `/tmp/bsu-schur-pair-final.log`,
  `/tmp/bsu-schur-pair-axioms.log`, `/tmp/bsu-signed-physical-gram-axioms.log`,
  `/tmp/bsu-schur-pair-final-manifest.json`, `/tmp/bsu-schur-pair-final-integrity.json`.
  All 23 owned module imports occur once; all 17 earlier source hashes remain
  unchanged. Index refresh and capstone discovery pass; scoped whitespace clean.
- At the package 8 audit, global lint exited 1 for five unrelated concurrent modules unreachable
  from the umbrella, listed in the facts ledger and `/tmp/bsu-schur-pair-lint-final.log`.
  None was modified. The read-only relocated README remains byte-identical.
  All owned jobs exited; both temporary API probes removed with `apply_patch`.
  No full/umbrella build, numerical experiment, heartbeat increase, commit, or push.

- Signed-Gram cutoff package: `SignedGramCapacity.lean` (8 public theorems),
  `SignedGramCutoffComparison.lean` (7), `SignedGramCutoffHierarchy.lean` (19).
  All three compile without diagnostics. All 34 public theorem axiom audits pass
  exactly once, only `propext`, `Classical.choice`, `Quot.sound`. Printed source
  signatures and packet/supremum definitions confirm the actual-source domain.
- SHA-256: capacity `95469f4664f01de5dd302d81a58445005f8d4d020dbe993fb2bc8e85101da435`;
  comparison `6be920f79c818fa42fdde188b73593c1bed983a76d0e52c9f5d8c23321ec4a2e`;
  hierarchy `7a0da76505f74745f800ee50fe6323540464d74274095fc051209cb46782327d`.
- Final command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramCutoffHierarchy.lean`;
  exit 0, empty diagnostics. Durable exit record `/tmp/bsu-signed-gram-final.exit`.
  Evidence `/tmp/bsu-signed-gram-{capacity,comparison,hierarchy,axioms,final}.log`,
  `/tmp/bsu_signed_gram_cutoff_axioms.lean`, and
  `/tmp/bsu-signed-gram-{manifest,integrity,audit-coverage}.json`.
- All 26 own imports occur once; all 23 previous source hashes remain unchanged.
  Index refresh and lexical discovery pass. At the package 9 audit, global lint exited 1 only for
  `ChebyshevGaugeNyquistCellQuadrature`, `DistantCopyCorrelationTopology`,
  `DistantCopyEnergyTopology`, and `SignedCoherentMomentReceiver`, all foreign
  concurrent unwired modules. Evidence `/tmp/bsu-signed-gram-lint-final.log`.
  Read-only README remains byte-identical. No full/umbrella build, numerical job,
  heartbeat increase, commit or push. The dual-gap result is counted at package 10.

- Signed-Gram trial package: `SignedGramDualSupport.lean` (11 public theorems),
  `SignedGramPhysicalPrices.lean` (17), `SignedGramTrialCertificate.lean` (21).
  All three final dependency checks pass without diagnostics. All 49 public
  theorems audited exactly once, only `propext`, `Classical.choice`, `Quot.sound`.
  Printed actual-source signatures and price/gap/remainder definitions inspected.
- SHA-256: support `a082cd5a304a9c32d550f5bc55afdad2bd202fb8d65751ac1c871c90321a2396`;
  prices `f241f55eda32e59665150b4bae5a0e9feba0d4dc701e3ecac2d336fcdd0c75e3`;
  trial `fd195d5c55de946103bb41e241f335655d30f0aabaf535c33f58b90ac883ca8b`.
- Final direct command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramTrialCertificate.lean`;
  exit 0, empty log. Durable exit record `/tmp/bsu-signed-dual-final.exit`.
  Evidence `/tmp/bsu-signed-dual-{support,prices,trial,axioms,final}.log`,
  `/tmp/bsu_signed_gram_dual_axioms.lean`, and
  `/tmp/bsu-signed-dual-{manifest,integrity,audit-coverage}.json`.
- All 29 owned imports occur once, all 26 earlier hashes unchanged. Index refresh
  and discovery pass. At the package-10 audit, global lint reported twelve foreign unwired modules:
  `CausalExponentialResponseAndLaplaceEnergy`, `DistantCopyCompactness`,
  `DistantCopyCorrelationTopology`, `DistantCopyEnergyTopology`,
  `DistantCopyPolarTopology`, `DistantCopySharpness`, `FiniteGridRunLength`,
  `FoldFreeKernelGramAndFranelGcdCancellation`, `RealizedCoherentCancellation`,
  `SignedPrimePolarOptimalCollar`, `SignedPrimePolarScaledCollar`,
  `SuccessorSequenceHilbert`. Evidence `/tmp/bsu-signed-dual-lint-final.log`.
  None was modified. README was byte-identical at the package audit; the subsequent
  external Trap 10 revision was read fully and remains read-only, as recorded above. Temporary
  API probe removed; all owned Lean and search jobs exited. No full/umbrella build,
  numerical experiment, heartbeat increase, commit or push.

- Explicit dyadic producer package: `DyadicDifferenceSource.lean` (14 public
  theorems), `DyadicAnchoredProducer.lean` (19), `DyadicTriangularOptimality.lean`
  (6), and `DyadicGramConditioning.lean` (16). All four dependency checks pass
  without diagnostics. All 55 public theorem axiom audits pass exactly once,
  only `propext`, `Classical.choice`, and `Quot.sound`. Actual source, full-Gram
  signatures, and explicit seed/packet/producer/coefficient definitions inspected.
- SHA-256: source `46205aa0c5a389ec04fedafa6f8d2e4e6c5ee5b1e9d7e73169b0fa1056b7704a`;
  producer `24c9734e4a331075063fe8116e929ef05156554baf3a710dd98adda855f11fe0`;
  uniqueness `e10da9d59fc6c1a32f3f5993e13a869cab781ae3d7854685c5343723b942f00d`;
  Gram cutoff `11fd46aeb8bc791b3883de96a0a3cf4754f47d2bde872df0da8e80af9a614960`.
- Final direct command:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/DyadicGramConditioning.lean`;
  exit 0, empty log. Durable exit `/tmp/bsu-dyadic-final.exit`; evidence
  `/tmp/bsu-dyadic-{source,producer,triangle,gram,axioms,final}.log`,
  `/tmp/bsu_dyadic_gram_axioms.lean`, and
  `/tmp/bsu-dyadic-{manifest,integrity,audit-coverage}.json`.
- Index refresh and all three requested capstone discoveries pass; evidence
  `/tmp/bsu-dyadic-index.log` and `/tmp/bsu-dyadic-discovery.json`.
  All 33 owned imports occur once, all 29 previous source hashes unchanged.
  Read-only README remains byte-identical at the current 260-line hash above.
  Scoped whitespace passes. Global lint exits 1 only for eleven foreign unwired
  modules listed in the facts ledger and `/tmp/bsu-dyadic-lint-final.log`.
  No foreign source was modified. Temporary API probe removed; all owned jobs
  terminal. No full/umbrella build, numerical experiment, heartbeat increase,
  commit or push. This package brought the cumulative count to **11/100**.

- Physical response package: `SignedGramMinimumResponse.lean` (12 public
  theorems), `SignedGramResponseOptimality.lean` (14), and
  `SignedGramResponseLadder.lean` (17). All three dependency checks pass without
  diagnostics. All 43 public theorem axiom audits pass exactly once, only
  `propext`, `Classical.choice`, and `Quot.sound`. Actual selection cells, response,
  linear cost, accepted step and ladder definitions and capstone signatures inspected.
- SHA-256: selector `2f409903d0f7e1e62e3767d985a58e567c5e59bd4eabed71e09d4c7cd000e9db`;
  optimality `ea4d38d015470d288fb2ee6b7bcf009ac573c722e1aa832045a77cfdbc080ec9`;
  ladder `1a5cb7a77fe22c3a88b0ebef726e29561a87b95cd8f02210baf31ca21faa824b`.
- Final direct command:
  `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramResponseLadder.lean`;
  exit 0, empty log. Durable exit `/tmp/bsu-minimum-response-final.exit`; evidence
  `/tmp/bsu-minimum-response-{selection,optimality,ladder,axioms,final}.log`,
  `/tmp/bsu_minimum_response_axioms.lean`, and
  `/tmp/bsu-minimum-response-{manifest,integrity,audit-coverage}.json`.
- Index refresh and all three requested capstone discoveries pass, in
  `/tmp/bsu-minimum-response-index.log` and `/tmp/bsu-minimum-response-discovery.json`.
  All 36 owned imports occur once; all 33 prior source hashes remain unchanged.
  Read-only README remains byte-identical. Scoped whitespace passes. Global lint
  exits 1 for six foreign unwired modules listed in the facts ledger and
  `/tmp/bsu-minimum-response-lint-final.log`; no own failure or foreign edit.
  Temporary API probe removed; all owned Lean, search and index jobs terminal.
  No full/umbrella build, numerical experiment, heartbeat increase, commit or push.
  Count this complete construction once: **12/100** at that audit, full goal active.


## Regularized quantitative producer verification (package 13)

Seven leaves, respectively 13, 10, 15, 14, 7, 5 and 13 public theorems:

- `RegularizedGramGeometry`: `c70f58673b66f62b8eaa10a5a9388875b59b71c159f0248bf083cfe68a69fabf`.
- `PhysicalCollarMixture`: `59e5a05dd8abb8ed2a943fad03a934664ee6a918734c2a2a51429627f5ef811f`.
- `PhysicalPriceResponse`: `19332c0ba583e30daeb39d12bd726b7e37c83d8615eaf2a0c28242b66fe50336`.
- `RegularizedPhysicalGram`: `037a3ecc363d2a919a8ae47f476d9f1b908d275a72ae33ad692996ac59b9aa2e`.
- `RegularizedGramDescent`: `7bb77eb3e38a5a7b302dbec8062b92f2c19211942e7d04049388f74a3d71f65c`.
- `RegularizedGramIteration`: `14b0fb7387867441fb31ee3d1bd1e5d0342a32630e127068e45cd6494df16e2d`.
- `QuantitativeGramProducer`: `1941ad65cb071a04258ae520efbf53f43432e400b3d59e338d76d4dc75e2c111`.

All seven dependency compiles pass with empty logs. All 77 public theorems were
axiom-audited exactly once; only `propext`, `Classical.choice`, and `Quot.sound`.
Nine capstone signatures and eight concrete definitions were printed and inspected.
Audit: `/tmp/bsu_regularized_axioms.lean`, `/tmp/bsu-regularized-axioms.log`, and
`/tmp/bsu-regularized-audit-coverage.json`.
Final direct command:
`lake --old env lean GaloisForLFunctions/BiScaleUncertainty/QuantitativeGramProducer.lean`;
exit 0, empty log, no `-o`. Evidence `/tmp/bsu-regularized-final.{log,exit}`.
Dependency logs: `/tmp/bsu-regularized-{geometry,mixture,response,physical,descent,iteration,producer}.log`.

Index refresh exits 0. Three requested exact capstones are discoverable:
`quantitativeGram_source_certificate`, `iSup_quantitativeGramCoefficient`, and
`quantitativeGramProducer_error`. Evidence `/tmp/bsu-regularized-index.log`,
`/tmp/bsu-regularized-discovery.json`, and discovery-coverage JSON.
All 43 owned imports occur exactly once, all 36 prior source hashes remain
unchanged, all seven current hashes match the manifest, and scoped whitespace
passes. Read-only README is byte-identical at
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
Global lint exits 1 for the 15 foreign unwired modules listed in the facts ledger
and `/tmp/bsu-regularized-lint.log`; no own failure or foreign edit.
Integrity evidence: `/tmp/bsu-regularized-{manifest,integrity}.json`.
Temporary API probe and two obsolete drafts removed; successful audit scratch
and logs retained. All owned jobs terminal. No full/umbrella build, numerical
experiment, heartbeat increase, commit or push. This construction counts once:
**13/100**, full objective active.

Reusable repairs: unfold `IntegrableOn` explicitly when transporting a pointwise
integrable sum. Give real integrands and integration functions explicitly before
`integral_nonneg`, `integral_sub`, and `integral_add`. Normalize successor casts
with selected `Nat.cast_add`, `Nat.cast_one`, `Nat.cast_succ`, and `add_assoc`
lemmas before recurrence inequalities. Annotate old/fresh dependent partitions
in recursive ladder branches; normalize final scalar order using `ring`.

Next sharp-tail candidate remains paper-only and uncounted. Its right-node tail
extension must assign the endpoint x=log N to old node N and truncate each new
cell by the open log M window. This repairs the exact partition law while leaving
old fibres unchanged for y>0. The candidate leading law concerns independent
P_N only, not the full signed-Gram optimum or unrestricted source infimum.
