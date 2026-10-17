# Multi-coset asymptotic constants: facts and unresolved claims

Scope: independent BiScaleUncertainty. Active objective comes from attachment
`14cea3d2-a6f6-463f-bcd2-5d8a6947ba60/pasted-text-1.txt`; 100 significant contributions,
without counting helper lemmas or previous work again. No RH objective or hgtl7.
Plan and complete current paper arguments:
`docs/drafts/pipeline/1-in-progress/multi-coset-asymptotic-constants-2026-10-17.md`.

## Exact source transfer

For N=n+2, every `PhysicalCollarPartition n` has actual source bound

    ofReal(Cρ h_f(0)) ≤ ∫⁻_(0,log N) ofReal((h_f(0)−h_f(x))w(x)) dx.

The source is any `LogarithmicGridSource n`: compact continuous real function with
literal grid zeros. Infinite energy and zero source are included. Share conditions
are only measurability, nonnegativity, support, and exact physical partition.
No extra transport, integrability, or optimizer condition is supplied by the caller.

Mechanism: exact two-branch ENNReal transport of an arbitrary nonnegative density;
signed-coset sphere law; one shared-origin support function; integrable coefficient.
This closes the previous gap between arbitrary-partition convex optimization and
actual source energy. It is one contribution package, not one per lemma.

Status: final direct `lake --old env lean` check passed, with no diagnostics, for
the entire `PhysicalCollarSourceEnergy.lean` module. It includes the supremum,
normalized smooth-source bound, and monotone finite-limit certificate. All 19 public
theorem axiom audits pass: only `propext`, `Classical.choice`, `Quot.sound`.
Principal signatures and the source subtype were printed and inspected. Own import
is present, indexes are refreshed, and scoped whitespace checks pass. Current global
lint status is recorded below.

The original certificate L_N=max_(2≤K≤N) P_K now equals P_N by the verified
partition-extension theorem. It satisfies

    J_arch(f)/h_f(0) ≥ L_N,       0<L_N ↑ L_∞≤∫_(δ,∞)w<∞.

The ratio theorem uses the actual compact C² nonzero grid-source subtype. The more
general extended-energy theorem needs only compact continuity and the prescribed
grid zeros. Smoothness, nonzero radius, and grid data are defining domain conditions;
no desired energy inequality or analytic transfer is a source field.

## Quantitative saturation of the allocation optimum

Let P_N be the supremum over physical partitions, δ=log(2)/2. Lean proves

    0 ≤ P_∞−P_N ≤ ∫_(log N−δ)^∞w
      ≤ 4·2^(1/4)/(sqrt(N)·(1−2/N²)),   N≥2.

The first comparison rests on extending old partitions and truncating any larger
partition below log N−δ. New nodes have no support below that cutoff. Zero-padding
preserves old block norms; nonnegative coordinate addition changes the coefficient
by between zero and the added mass. The existing finite-array capacity theorem is
the analytic input. Full proof, including endpoints and N=2, is in the card.

Status: both `PhysicalCollarCutoffMonotonicity.lean` and
`PhysicalCollarCutoffStability.lean` compiled without diagnostics. All 35 public
theorems passed scratch axiom audits, using only `propext`, `Classical.choice`, and
`Quot.sound`. Printed signatures confirm unconditional cutoff statements. The
required final direct leaf recheck passed, exit 0, no diagnostics. The error rate is an upper bound,
not a proved optimal rate.

For every finite trial partition ρ, the verified dual-gap corollary gives

    0 ≤ P_∞−Cρ ≤ Gρ + 4·2^(1/4)/(sqrt(N)·(1−2/N²)).

This encloses the allocation limit without assuming an attained optimizer. The
finite dual gap Gρ and the cutoff error have distinct roles; neither bounds the
gap to the true source infimum.

## Candidate leading asymptotic

A further paper argument in the card gives

    P_∞−P_N = 4/sqrt(N)+O(1/N).

It compares the deficit to T_N=∫_(log N,∞)w from both sides. Extending old partitions
by right-node cell assignments adds all tail mass but only O(1/N) radial penalty.
Conversely, remove future-node shares and fill their holes below log N using the next
old grid node; these holes occur only above log(N+1)−δ and their new offsets are
O(1/N), so the repair penalty is O(1/N). The explicit constants and endpoint
assignments are in the card. T_N=4/sqrt(N)+O(N^(−5/2)) follows by integrating the
exponential remainder of w.

Status: paper argument requiring formal audit; uncounted. The exact tail-law corpus
query returned finite-array capacity comparison and existing duality, but no matching
earlier asymptotic theorem. Semantic coverage was unmeasured, so this is not evidence
of exhaustive absence or literature-wide novelty. Log: `/tmp/bsu-allocation-tail-search.log`.

Mechanism worth retaining: high-node physical mass costs order N^(−1/2), while
its optimized origin penalty costs only order N^(−1) because it can be concentrated
on a short offset interval. This is specific to the present independent-block
allocation family; the Schur-coupled and true-source asymptotics remain open.

## Signed product coupling

Opposite signed nodes log j and −log k have cross entry h(log(jk)). Thus cutoff
growth can activate constraints between old nodes: the −log2/+log3 entry is first
pinned at N=6. Allocation tail locality does not imply full signed Gram locality.

For a source pinned through N and a collar grid through K with K²≤N, every pair
of opposite-sign odd cosets, together with the origin, forms an orthogonal clique.
Their paired Bessel spheres imply the finite support function

    R sqrt(W²+A_+²+A_-²),

where A_± are sums of within-sign block Euclidean weight norms. Proof: maximize
the correlation block norm on each sign, apply the paired constraint to the two
maximizers, then apply three-dimensional Cauchy–Schwarz. This support is attained
in the paired-sphere finite-vector model; no source realizability follows.

For a fixed physical partition, the improvement over the independent-sign kernel is

    2 A_+A_- / [sqrt(W²+(A_++A_-)²)+sqrt(W²+A_+²+A_-²)].

`PairedCosetSphereDuality.lean` now passes direct Lean verification of this support,
attainment, domination, and exact gain. `SignedCosetProductCoupling.lean` passes
direct verification of actual product-zero orthogonality, measurable integrable
physical kernels, exact gain, and extended/normalized source-energy transfer.
Only defining grid zeros and the arithmetic cutoff K²≤N are required.

The optimized hierarchy is

    C_N = max(P_N, max_{2≤K, K²≤N} Q_K),

where Q_K is the supremum of coupled physical coefficients through K; an empty
inner maximum is zero. `ProductCoupledCollarHierarchy.lean` proves positivity,
monotonicity, source-energy control, and finite convergence, with upper bound
∫_(δ,∞)w. All three direct compilation checks pass without diagnostics, and all
41 public theorem axiom audits pass using only `propext`, `Classical.choice`, and
`Quot.sound`. Printed signatures and definitions confirm the actual source domain
and arithmetic product-admission condition. Final direct recheck passed, exit 0,
without diagnostics.

No strict improvement of C_N over P_N, sharp convergence rate, or equality with the
true source infimum is asserted. Sharpness applies only to the paired-sphere support.
The full-grid capped-support construction below retains high nodes without the
loss caused by separately summing low/high block norms.

## Quantitative product-coupled saturation

Paired capacity has its own proved comparison: nonnegative coordinate addition
increases the kernel by between zero and added mass, for every real origin weight.
An unordered nonnegative array differs from a trial array by at most the supplied
added capacity. Padding preserves both sign norms. Exact physical extension and
retraction therefore prove

    Q_K ↑ C_∞ = sup_K Q_K ≥ P_∞,
    0≤C_∞−Q_K≤∫_(log K−δ)^∞w≤4·2^(1/4)/(sqrt(K)(1−2/K²)).

For N≥4, let s=floor(sqrt N). The finite envelope reduces exactly to

    C_N=max(P_N,Q_s),
    0≤C_∞−C_N≤4·2^(1/4)/(sqrt(s)(1−2/s²))≤16·2^(1/4)/N^(1/4).

Thus every actual nonzero compact C² N-grid source has
J_arch(f)/h_f(0)≥C_∞−16·2^(1/4)/N^(1/4). There is no optimizer or extra analytic
premise. The bound is for the product-coupled subhierarchy, not the full Gram cone.

`PairedCollarCapacity.lean` and `PairedCollarCutoffStability.lean` pass direct Lean
compilation without diagnostics. All 30 theorem axiom/signature audits pass using
only `propext`, `Classical.choice`, and `Quot.sound`. Final direct recheck passed,
exit 0, no diagnostics.
The error exponent is an upper bound, not a proved sharp rate. Matching leading laws
and strict improvement C_∞>P_∞ remain open.

## Exact full-grid capped support

For K²≤N, split each signed odd-coset weight vector into low nodes j≤K and high
nodes j>K, with Euclidean norms L and H. Preserve each whole-coset sphere and add
the opposite-sign low-block pair spheres supplied by literal product-grid zeros.
Their exact finite-vector support is R sqrt(W²+Z²), where

    Z = max_(0≤t≤1) Σ_m [F_(L_false,m,H_false,m)(t)
                       +F_(L_true,m,H_true,m)(sqrt(1−t²))],
    F_(L,H)(t) = sqrt(L²+H²)                  if L≤t sqrt(L²+H²),
                Lt+H sqrt(1−t²)             otherwise.

Lean proves the formula including zero weights, compact attainment, continuity,
the exact finite-amplitude/vector support, and Z≤Σ_(σ,m)sqrt(L²+H²). Thus the
physical capped coefficient B_(N,K)(ρ) satisfies, for every physical partition,

    oldCoefficient_N(ρ) ≤ B_(N,K)(ρ) ≤ J_arch(f)/h_f(0).

The source is the actual nonzero compact C² N-grid source. The ENNReal version
holds for every compact continuous grid source, including zero source and infinite
energy, and uses the full interval (0,log N). No analytic transfer or optimizer
premise is imposed. `fullGrid_capped_energy` supplies K=floor(sqrt N) for N≥4.
Finite support sharpness does not assert autocorrelation realization.

All three leaves and final direct source-leaf check pass without diagnostics.
All 41 public theorem axiom/signature audits use only `propext`, `Classical.choice`,
and `Quot.sound`. This is one contribution package.

## Exact activation and quantitative gain [Lean-verified]

Let α_σ=max_m L_(σ,m)/sqrt(L_(σ,m)²+H_(σ,m)²),
with zero fraction for zero blocks. The angular support equals the independent
whole-block support iff α_false²+α_true²≤1; otherwise improvement is strict.
Proof: equality in each nonzero block's Cauchy bound requires its normalized weight
direction; simultaneous feasibility is exactly the displayed condition. Compact
attainment turns failure of feasibility into a strict support gap. Integrated
strictness requires activation on a positive-measure set. Both
`CappedSupportActivation.lean` and `PhysicalCappedActivation.lean` now compile
without diagnostics; all 26 axiom/signature audits and final direct check pass.

The scalar proof gives an attained disk point (x,z) with the exact identity

    2U(U−F)=(Ux−L)²+(Uz−H)²,    U=sqrt(L²+H²).

When tU≤L, this implies `(L−tU)²≤2U(U−F)`. Thus the cap defect is a
quantified deviation from the uncapped extremal direction, including zero blocks.
For actual physical weights, write S for the independent whole-block norm sum
and Z for capped support. The exact kernel gain is

    G(y)=(S²−Z²)/(sqrt(W²+S²)+sqrt(W²+Z²)),    W=w_arch(y), y>0.

It equals `cappedKernel−kernel`. Its integral adds to the old coefficient to give
the capped coefficient. The verified physical classification is equality iff
α_false²+α_true²≤1 almost everywhere on (0,δ), with strict gain iff that
almost-everywhere condition fails. Measurable physical shares suffice; continuous
shares and an attained optimizer are not required. The source certificate retains
the full gain integral for actual compact smooth grid sources, with an extended
version including zero sources and infinite energy. No analytic transfer premise
is supplied. This criterion does not prove a strict gap between optimized constants.

## Full-grid capped hierarchy [Lean-verified]

Write B_(N,K)=sup_ρ B_(N,K)(ρ). The new comparison package proves

    P_N ≤ B_(N,K),   Q_K ≤ B_(N,K) ≤ Q_N,   B_(N,N)=Q_N,

and B_(N,K)≤B_(M,L) whenever N≤M, K≤N, K≤L≤M. The proof uses exact
zero-padding, actual physical partition extension, and two local support laws:
adding nonnegative weights increases the kernel by at most added coordinate mass;
moving a fixed whole-block norm from high to low nodes tightens the capped support.

Set B_N=B_(N,floor√N) for N≥4 and B_N=P_N for N=2,3. Then

    C_N ≤ B_N ≤ Q_N ≤ Q_∞,    0 < B_N ↑ Q_∞,
    0 ≤ Q_∞−B_N ≤ 16 exp(δ/2)/N^(1/4),   N≥4,
    B_N ≤ J_arch(f)/h_f(0).

The last inequality applies to actual nonzero compact C² N-grid sources. An
extended-energy version covers compact continuous sources, zero sources, and
infinite energy on the full physical interval (0,log N). There is no analytic
interface or optimizer premise. A sharper floor-square-root upper error is also
formalized. All four leaves compile without diagnostics; all 58 public theorem
axiom/signature audits pass with only `propext`, `Classical.choice`, and `Quot.sound`.
The final direct leaf recheck passed, exit 0, no diagnostics.

Full-grid retention in this uniform-low model changes the finite certificate
without changing Q_∞. Neither strict finite improvement over C_N nor sharpness
of the fourth-root error is proved. Unequal-size product-zero pairs, general
nonzero Schur residual coupling, and actual autocorrelation realization remain open.
The package is not a theorem identifying the true sharp source-energy constant.

## Two-column Schur refinement

For finite columns u,v, let U=Σu², V=Σv², D=Σuv. The residual conditions
U,V≤R² and (Rc−D)²≤(R²−U)(R²−V) imply, for every real r,s,

    Σ(ru+sv)² ≤ R²(r²+s²)+2Rc rs.

The zero-lag domain c=0 is invariant under simultaneous unit rotations.
For weights a,b with A=Σa², B=Σb², C=Σab, its exact support is

    R ν(a,b),    ν(a,b)=sqrt(A+B+2sqrt(AB−C²)),    R≥0.

Finite-vector maximizers exist, including degenerate weights. Moreover
ν≤sqrt A+sqrt B, with equality iff C=0. This attainment concerns finite
vectors; autocorrelation realization is not proved.

For actual grid sources with N≥4, d=log2 supplies the orthogonal frame
{0,d,2d} and zero-lag target pair y,y+d. Writing u0=h(y), u1=h(d−y),
u2=h(2d−y), v=h(d+y), every split λ,μ∈[0,1] yields

    W u0+a u1+b u2+c v ≤ h(0)ν((λW,μa,b),(c,(1−λ)W,(1−μ)a)).

The minimum S(W,a,b,c) over that compact square is attained and continuous.
For nonnegative weights, W≤S≤W+a+b+c. Thus W+a+b+c−S is a
nonnegative kernel bounded by a+b+c. Literal physical weights use node2's
left and right sides and node4's left side. All unselected source costs remain
nonnegative. Maximizing this kernel with the old full-grid capped kernel
preserves every old partition certificate, with no duplicated origin interval.

Let T_N optimize this maximum over physical partitions, and H_N=max_(K≤N)T_K,
using P_K for K=2,3. The paper proof gives

    B_N≤H_N≤J_arch(f)/h_f(0),    0<H_N↑H∞≤tailMass,    Q∞≤H∞.

Source restriction proves envelope monotonicity; raw T_N monotonicity is not
claimed. The extended-energy version includes zero sources and infinite energy.
No equality H∞=Q∞, strict optimized gap, rate to H∞, or sharp source infimum
is established. The general nonzero-lag rotation bound does not yet give an
exact nonzero-lag support formula or its physical hierarchy.

Strict finite-cone separation is symbolic: W=a=b=1,c=0 and λ=μ=1/2
give ν²=2+sqrt3/2<3, below the old one-column sphere support squared.
This is not a numerical experiment and does not prove a strict physical optimum gap.

Status: all five Schur leaves compile cleanly; all 69 public theorem axiom/signature
audits pass with standard axioms only. The general signed extension below adds
16 audited theorems. The final direct leaf check passes; all six leaves form one package.

## Full measured signed-Gram receiver

Authoritative field context now lives at the read-only path
`formal/GaloisForLFunctions/BiScaleUncertainty/README.md`. All 242 lines were read;
SHA-256 `80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507`.
Its blind-subspace obstruction requires keeping general signed correlations.
Uniform blind-grid constants remain meaningful specializations, not general
signed-source theorems. Research scope remains multi-coset source-energy bounds.

For any compact continuous source, let R=h(0), A=Σa_i, a_i≥0, W≥0, and
retain every measured signed entry in the origin-anchored Gram energy

    G=R W²+2W Σa_i h(τ_i)+Σ_i,j a_i a_j h(τ_j−τ_i).
    K=R(W+A)−sqrt(RG).

The existing translation-packet Cauchy theorem supplies the pointwise source
bound. The envelope |h|≤R gives G≤R(W+A)², hence K≥0. Evaluating the
same packet at the origin gives sqrt(RG)≥RW−RA, hence K≤2RA.
This is exact singular-origin cancellation; no derivative moment, origin cutoff,
or artificial clipping of the kernel is needed.
More precisely K≤Σa_i(R−h(τ_i)): measured signed node deficits control
capacity, reducing to RA on the blind grid.

Use all physical signed nodes τ_(false,k)=log(k+2), τ_(true,k)=−log(k+2)
with their actual partition weights. Then A=massρ, K is measurable and
integrable, and exact signed transport gives ∫K≤J_arch(f) for actual sources.
The extended-energy formulation applies to every f:C_c(ℝ,ℝ), including zero
and infinite-energy sources. C² gives the real-energy ratio, including total
division at R=0. No grid-zero or caller-supplied Gram estimate enters this result.
On the blind-grid domain, max(H_N,∫K/R) retains both source certificates.

This signed coefficient depends on actual source correlations; it is not a
positive uniform constant for unrestricted sources. Exact general nonzero-lag
multi-column support and asymptotics of optimized signed-data certificates
remain open. Status: compiled and audited, including all 16 public theorems,
the concrete source/kernel definitions, and the final direct leaf check.

## Full signed-Gram cutoff stability for each actual source

For the exact anchored packet P(a)=W T_0f+Σa_i T_tif, the Gram deficit is
K(a)=R(W+Σa_i)−sqrt(R)||P(a)||. Both triangle inequalities prove

    0≤K(a+b)−K(a)≤2RΣb_i,   b_i≥0.

The incumbent weights and anchor W may have either sign. Consequently K is
coordinatewise monotone, and any nonnegative cover b_i≤a_i+e_i gives
K(b)−K(a)≤2RΣe_i. Zero-padding preserves the exact mass and packet. This
controls all signed cross-coset entries simultaneously; no Gram locality is used.

For a fixed actual compact continuous source f, define S_N(f)=sup_ρ ∫K_ρ over
physical partitions through N. Actual extension and retention retraction give

    0≤S_N(f)↑S_∞(f)≤2R∫_(δ,∞)w,
    0≤S_∞(f)−S_N(f)≤2R∫_(log N−δ,∞)w,
    0≤S_∞(f)/R−S_N(f)/R≤8·2^(1/4)/(sqrt(N)(1−2/N²)),  N≥2.

The normalized statement includes R=0 by total division. The limiting extended
energy theorem takes only f:C_c(ℝ,ℝ), covers infinite energy, and has no grid-zero
or assumed analytic interface. Compact C² sources satisfy S_N/R≤S_∞/R≤J_arch/R.
This proves an upper cutoff rate, not a matching asymptotic. S_∞ depends on f;
it is not identified with H∞ or the sharp uniform source constant.

Status: all three leaves compile without diagnostics; all 34 public theorems
pass axiom audits, only propext, Classical.choice, Quot.sound. Final direct
`lake --old env lean` recheck passed, exit 0, empty diagnostics log.

## Full measured-Gram trial certificates

For P_a=W T_0f+Σa_i T_tif and H_a=sqrt(R)||P_a||, define
q_i=Re⟨P_a,T_tif⟩/H_a with total division and p_i=(1+q_i)/2. Cauchy gives
−1≤q_i≤1, so p_i∈[0,1]. At a zero packet q_i=0; no packet-positivity premise
is needed. Norm support gives the exact nonnegative remainder

    r(a,b)=H_b−H_a−RΣ(b_i−a_i)q_i ≥0,
    K_b−K_a=2RΣ(b_i−a_i)−2RΣ(b_i−a_i)p_i−r(a,b).

Pull these actual measured-Gram prices back to physical collars and let p_min
be their minimum over active collars. Prices are measurable bounded finite
expressions; their costs transport exactly. Define

    Slack(ρ,η)=∫[Ση_k w p_ρ,k−w p_min]≥0,
    Gap(ρ)=2R Slack(ρ,ρ).

For every pair of physical partitions and every compact continuous actual source,

    Cρ+Gap(ρ)−Cη=2R Slack(ρ,η)+∫r(ρ,η),
    0≤S_N−Cρ≤Gap(ρ),
    0≤S_∞/R−Cρ/R≤Gap(ρ)/R+8·2^(1/4)/(sqrt(N)(1−2/N²)).

The remainder is integrable through the combined kernel/mass/price expression;
the singular anchor is never integrated separately. Zero Gap certifies finite
optimality. Precisely, Gap=0 iff R=0 or complementary allocation holds almost
everywhere: every positive incumbent share uses a minimum-price active collar.
This classifies the canonical certificate; it does not assert every optimizer
has zero canonical gap.

The extended-energy trial theorem takes only ρ and f:C_c. The normalized theorem
for compact C² sources gives Cρ/R≤S_∞/R≤J_arch/R together with the displayed
trial error. No grid zeros, optimizer, or supplied transport/energy interface.
All three final dependency checks and the final direct leaf audit pass, exit 0
without diagnostics. All 49 public theorems are audited exactly once, using only
`propext`, `Classical.choice`, and `Quot.sound`. Actual-source signatures and
concrete price/gap/remainder definitions inspected. This is package 10.

Next uncounted question: determine nonvanishing of actual nonzero compact-source
translation packets with positive anchor and nonnegative node weights, and whether
it permits a converse from optimality to zero canonical gap. No general-source
nonvanishing or converse claim is currently proved. Search `/tmp/bsu-signed-dual-next-search.log`
finds packet norm/finite-translate infrastructure, but is partial and source-only.

Sharp actual-source conditioning law, Lean-verified package 11: for d=log(2),
instantiate a smooth `ContDiffBump` centered at zero with radii d/8 and d/4, and
fix the actual smooth source f=g−T_dg. Orthogonality of integer-d translates of g
gives R_f=2R_g and h_f(d)=−R_g. The average Q_m of the first m+1 symmetric
translation chains telescopes to (Σ_(k=0)^m(T_(-kd)g−T_((k+1)d)g))/(m+1).
Every anchored packet P with arbitrary signed weights on ±kd, 1≤k≤m, satisfies
the exact law ||P||²=R_f/(m+1)+||P−Q_m||². Equality forces the coefficients
at ±kd to be 1−k/(m+1); these explicit positive coefficients attain Q_m.
The normalized anchored minimum is exactly log(2)/(log(N)+log(2)) at N=2^m,
and tends to zero for this one fixed smooth source. It is not a minimum-eigenvalue
claim. These weights are not asserted to be physical collar partitions, and no
polar admission or sharp S_N asymptotic follows. The source has full lattice
correlation h_f(zd)=R_g(2·1_(z=0)−1_(z=1)−1_(z=−1)). All four leaves and the final
direct leaf check pass without diagnostics; all 55 public theorem axiom audits
pass exactly once using only `propext`, `Classical.choice`, and `Quot.sound`.
The exact minimum, attained positive weights, and unique equality classification
are the positive survivor of the obstruction to cutoff-uniform coercivity.
Consequently, a physical response argument cannot infer cutoff-uniform positive
anchored Gram energy from fixed-source smoothness and positive weights alone.
Search `/tmp/bsu-signed-dual-conditioning-search.log` completed with 219
declarations in 40 modules; source-only candidates, older coverage snapshot,
semantic coverage unmeasured. No exhaustive novelty claim.

Constructive physical response and cutoff ladder, Lean-verified package 12.
For actual source f and incumbent partition ρ, let E_k contain the active points
at which p_k equals the finite minimum price, with k≤n. The cells
F_k=E_k\(union_(j<k) E_j) are measurable, disjoint, and cover the physical interval.
Their characteristic functions define an actual admissible response η, with
exactly one selected collar per physical point. Inactive collars are excluded
before tie-breaking; a masked inactive price tied with the minimum receives no mass.

The response attains the pointwise and integrated minimum of ρ's physical linear
cost. Every minimizing partition allocates only to minimum-price active collars
almost everywhere, and every such partition minimizes the cost. Thus ρ's canonical
gap G is the attained greatest feasible linearized gain over actual partitions.
The actual coefficient gain is C(η)−C(ρ)=G−D, where D is the nonnegative integrated
full-Gram norm remainder. All signed and cross-coset Gram entries are retained.

Accept η when C(η)≥C(ρ), otherwise retain ρ. The accepted coefficient C⁺ satisfies
C⁺−C(ρ)=max(0,G−D) and C(ρ)+G−C⁺=min(G,D). Consequently
0≤S_n(f)−C⁺≤min(G,D), and
0≤S∞(f)−C⁺≤min(G,D)+2h_f(0)·collarCutoffTailMass(n).
This is an unconditional bound for a constructed response, not a supplied error budget.

Starting with equalMultiplicity at cutoff 0, repeatedly apply actual physical
extension and accepted response. The produced A_n(f)=gramResponseCoefficient f n is monotone, lies below
S_n(f), and tends to a finite produced limit L(f)≤S∞(f). At actual cutoff N=n+2,
the normalized error to S∞ is at most the produced partition's gap/h_f(0) plus
8·2^(1/4)/(sqrt(N)(1−2/N²)); the successor also has the sharper min(G,D) certificate
from its explicit extension. Compact C² sources satisfy A_n/h_f(0)≤L/h_f(0)≤J_arch/h_f(0).
The extended-energy lower bound holds for every actual compact continuous source.
No strict ascent, vanishing gaps, or equality L=S∞ is asserted.

All three leaves and the final direct check pass without diagnostics. All 43
public theorem axiom audits pass exactly once with the standard three axioms.
Package 13 below resolves quantitative damping through controlled norm
regularization. Generic finite translate independence and its fixed-cutoff Gram
consequences remain unproved here; cutoff-uniform coercivity is not assumed.
Search `/tmp/bsu-minimum-response-search.log` returned useful source-only price,
partition and cover arguments; older coverage, semantic completeness unmeasured.

Trap 10 constrains the next step: prioritize an explicit source/weight producer
with unconditional error, rather than another interface with an unresolved bound.
The explicit smooth difference producer now supplies that result on this topic. Existing
`ExplicitNyquistPolarAndChebyshevFactorialProducer.lean` states the Nyquist-cell
squared L² error ≤1/(16n²), the centered first-stencil bound
|T(2N)−2T(N)−2N log(2)|≤2log(2N+1)+1, and the second-stencil bound
|T(4N)−4T(2N)+4T(N)|≤5log(4N+1)+1. The first raw stencil is not O(log N).
These existing results are not new contributions here. No pre-floor subtraction
of the discrete counterterm is part of the current multi-coset work.
Producer reference status: source signatures/proofs inspected, but a scratch
import audit failed because its `.olean` is absent. No fresh Lean audit claimed;
`/tmp/bsu-trap10-reference-audit.log`. The failed temporary probe was removed.

## Quantitative full-Gram producer (package 13, verified)

For actual f:C_c(ℝ,ℝ), write R=h_f(0), δ=log(2)/2 and N=n+2. Regularize the
actual signed packet scale H=sqrt(R)||P|| to H_ε=sqrt(H²+(εR)²). The combined
kernel loses between 0 and εR, so 0≤C−C_ε≤εδR. All measured signed Gram entries
are retained. No packet nonvanishing or Gram conditioning premise is required.

The actual regularized price is measurable and lies in [0,1]. Equal sharing
among active minimum-price collars constructs a measurable physical partition
attaining the linear minimum. Physical convex mixtures are actual partitions.
With M_n=2(n+1)·logarithmicCollarWeightBound(n) and
T_n=∫_(δ,log(n+2))w, the integrated norm remainder for a mixture step τ satisfies
0≤D_ε≤Bτ², B=2R M_n T_n/ε. Integrability is proved through combined kernels
and bounded differences, without separately integrating the singular anchor.

Starting from equalMultiplicity, apply the produced minimum-price response with
step τ_t=2/(t+2). For every actual competitor η, the regularized objective error
after t+1 steps is at most 4B/(t+3); original error adds only εδR.
Choose ε=1/(k+1) and run ceil(8M_nT_n(k+1)²)+1 steps. Then

    0 ≤ S_n(f) − C(quantitativeGramProducer f n k) ≤ R(δ+1)/(k+1).

This finite functional construction has a work count independent of f. It is
not a numerical computational-complexity claim. No optimizer attainment or
supplied error assumption enters the producer.

At cutoff n, set k=n and keep the larger original coefficient between this
fresh producer and the physical extension of the previous result. The resulting
A_n=quantitativeGramCoefficient f n is monotone, 0≤A_n≤S_n, and
A_n→S∞ with iSup A_n=S∞. Its normalized certificate is

    0 ≤ S∞/R − A_n/R ≤ (δ+1)/(n+1) + 8·2^(1/4)/(sqrt(N)(1−2/N²)).

Zero sources are included. Arbitrary compact continuous sources have the actual
finite-window extended-energy bound; compact C² sources have
A_n/R≤S∞/R≤J_arch/R. This new ladder reaches S∞; no such equality is established
for the older unsmoothed gramResponseLadder. S∞/R is still not identified with
the blind-grid H∞ or the unrestricted sharp source infimum.

All seven leaves compile cleanly; all 77 public theorem axiom audits and the
final direct leaf check pass. Count this as one significant package.
Deep curvature search was partial (100.31s); all 60 lexical hits across 14 modules
were inspected and supplied existing packet/remainder dependencies, not this
regularized physical producer. Source-only coverage, semantic completeness
unmeasured; no exhaustive novelty claim. Evidence `/tmp/bsu-regularized-curvature-search.log`
and `/tmp/bsu-regularized-lexical{,-page2,-page3}.log`.

## Limits that must remain visible

- P_N optimizes the independent signed-coset sphere relaxation. It is not identified
  with the sharp constant over actual autocorrelations.
- Opposite-sign product-zero coupling is now connected to physical source transport.
  Sharp optimization with general nonzero Schur residuals and full cross-coset
  constraints remains open.
- Fixed narrow smooth sources imply the true finite-grid constants are bounded above
  uniformly in N. Unbounded growth is impossible on this unrestricted-support domain.
- A finite maximum over earlier cutoffs certifies monotonicity immediately. It does
  not by itself prove monotonicity of P_N; use the extension proof for that claim.
- A coefficient sharp in a finite convex relaxation need not have a realizable
  autocorrelation extremizer. Optimizer attainment is not needed for the bounds.
- Tail control of this allocation optimum does not automatically control the error
  to the true source infimum, or the error of a stronger Schur-coupled hierarchy.
- The older unsmoothed response ladder has a finite limit below S∞; equality and
  gap decay remain open for that ladder. Package 13's regularized quantitative
  ladder reaches S∞ with proved allocation and cutoff errors.

## Research accounting

Lean-verified significant packages: **13/100**: (1) general source transfer and
optimized certificates; (2) actual cutoff monotonicity, retraction stability, and
explicit quantitative saturation; (3) attained paired-sphere support, actual signed
product-zero source transfer, and its optimized monotone finite-limit hierarchy;
(4) paired capacity and cutoff stability, exact limit identification and frame
selection, and quantitative fourth-root source-cutoff control; (5) exact capped
support and finite-vector attainment, followed by full-grid physical source transfer;
(6) capped capacity and cutoff comparisons, the optimized monotone full-grid
hierarchy, common finite limit, and quantitative actual-source certification;
(7) exact capped activation, quadratic extremal deficit, rationalized physical
gain, almost-everywhere equality/strictness, and actual-source gain transfer;
(8) exact two-column Schur support, optimized dyadic physical refinement and
monotone hierarchy, plus the unconditional full measured signed-Gram receiver;
(9) measured signed-Gram capacity, actual physical cutoff monotonicity/retraction,
optimized finite limit, explicit inverse-square-root error, and actual-source receiver;
(10) full measured-Gram dual support, exact physical dual gap and complementarity,
finite-allocation error and quantitative limiting actual-source trial certificates;
(11) an explicit fixed smooth dyadic source and packet producer, sharp anchored
full-Gram minimum, unique positive triangular coefficients, exact squared-distance
remainder, and logarithmic cutoff degeneration;
(12) an actual measurable pure minimum-price response, attained linear optimum
and complete equality classification, exact accepted-response error, and a
monotone physical cutoff producer with finite limit and actual-source certificates;
(13) unconditional regularized signed-packet curvature, realized physical minimum
responses and finite iteration, followed by a monotone producer reaching S∞ with
explicit allocation and cutoff errors for actual sources.
Count each package once, not its leaves or helper lemmas.
Previously certified shared-origin and dual-allocation results are dependencies.
The full research objective remains active.

Latest global lint reports 15 unrelated modules unreachable from the umbrella:
`CenteredRamanujanVarianceAndAbelCofactorCancellation`,
`FoldFreeLogMobiusAndPlancherelCausalProducer`, `IntegerBlockAggregation`,
`IntegerBlockCoisometry`, `IntegerBlockVariance`, `IntegerDilationTraceDefect`,
`MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity`, `NyquistWeightCells`,
`NyquistWeightJets`, `NyquistWeightTaylorRemainder`, `PhysicalDilation`,
`RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge`,
`SignedPrimePolarCausalMoments`, `SignedPrimePolarSourceEnergy`,
`SignedPrimePolarSourceFactorization`. Those concurrent files were not modified.
All 43 owned leaves are wired. Evidence: `/tmp/bsu-regularized-lint.log` and
`/tmp/bsu-regularized-integrity.json`.

Final source SHA-256: `423ca0e7d1957c5898bac5ff228e6989d255c98e2fe24ec621775f76d3574792`.
Evidence: `/tmp/bsu-physical-source-{final,axioms,index,lint}.log` and
`/tmp/bsu_physical_source_axioms.lean`.

Cutoff SHA-256 values:

- Monotonicity: `e9ebaca82b8d817c28826c64ac54fb77e81dc5823f71b3329fea4110e0eb6586`.
- Stability: `b3d464f73df171bc2e7f8a062697c15518a63df9a8c9b3bdc2ff3ed940264246`.

Cutoff evidence: `/tmp/bsu-cutoff-check.log`, `/tmp/bsu-cutoff-stability-check.log`,
`/tmp/bsu-cutoff-{axioms,final,index,lint}.log`, `/tmp/bsu_cutoff_axioms.lean`.
All owned processes exited; there is no live job to poll. Temporary API probes are removed.

Product-coupling SHA-256 values:

- Paired geometry: `377bf1eef09bb7190e186f533bc5e8c80cc0bd25e426648e219a103c0ff19d9f`.
- Source transport: `c26fc3d7f4f1d4e4ad123135d733a59fae96c940ddc9c5821a27c4b0eff029dc`.
- Coupled hierarchy: `e78c3e45cc9bcd200840dbfcb40d1a41fa3ff49396b875f98a05850eca6b3156`.

Evidence: `/tmp/bsu-paired-geometry.log`, `/tmp/bsu-signed-coupling.log`,
`/tmp/bsu-product-hierarchy.log`, `/tmp/bsu-product-coupling-{axioms,final,index,lint}.log`,
`/tmp/bsu_product_coupling_axioms.lean`. All 41 public theorems are included in the audit.

Paired-cutoff SHA-256 values:

- Capacity: `215adfa612eb4e9eef6d1025d51de02109b3d2b0a157828441b4068c83030863`.
- Stability: `e2f4d2b569d6df1efd3e4e65444f9e025408ee34d1c9fe83973e273334eec19c`.

Evidence: `/tmp/bsu-paired-capacity.log`, `/tmp/bsu-paired-stability.log`,
`/tmp/bsu-paired-cutoff-{axioms,final,index,lint}.log`, `/tmp/bsu_paired_cutoff_axioms.lean`.
All 30 public theorems are included in the audit; principal signatures and cutoff
definitions were printed and inspected.
All owned jobs exited; the paired-cutoff API probe was removed. Successful audit
scripts and logs remain available; no full or umbrella build was run.

Full-grid SHA-256 values:

- Block support: `3004dced418ed93f074aa177cd75cf7bd841200f6af3328538e5cd2863355406`.
- Coset support: `b6e3bd890950ae1874e4c4ef87a30d383d1d4360768ffdad607e2b8505d811c5`.
- Source transfer: `6a8bcfaba9f2647cdeadc59abc68a5cf7724c4a3c58e049120c7922553503b0d`.

Evidence: `/tmp/bsu-capped-block.log`, `/tmp/bsu-capped-cosets.log`,
`/tmp/bsu-fullgrid-capped.log`, `/tmp/bsu-fullgrid-capped-{axioms,final,index,lint}.log`,
`/tmp/bsu_fullgrid_capped_axioms.lean`. All eight earlier hashes rechecked unchanged.
Final direct command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FullGridCappedCollarEnergy.lean`.
Exit 0, no diagnostics; all 41 public theorem audits pass.

Full-grid hierarchy SHA-256 values:

- Support comparison: `4f6f50c1f75d890d7f06a891dcca531c103eb15c01bbe2cf5cc13b276c1ccca3`.
- Array comparison: `9656cd0ce211de779e6dbfefd70a35950e7d761b65c93e6418b1be80a200fd43`.
- Cutoff comparison: `d597b18ce4c9910cccfb22975c72ad6646ff8113781471dbb0795fcd460ec4ec`.
- Optimized hierarchy: `72320630cda08587f8830f795984fb6c44ab1c98904049f64ec7817f789a8ffa`.

Evidence: `/tmp/bsu-capped-support-comparison.log`,
`/tmp/bsu-capped-array-comparison.log`, `/tmp/bsu-capped-cutoff-comparison.log`,
`/tmp/bsu-capped-hierarchy.log`, `/tmp/bsu-capped-hierarchy-{axioms,final,index,lint-final}.log`,
and `/tmp/bsu_capped_hierarchy_axioms.lean`. All 58 public theorems pass the audit,
each included exactly once; the final direct recheck passed. All eleven earlier source hashes are
unchanged. Corpus search `/tmp/bsu-capped-capacity-search.log` was partial; no
exhaustive novelty claim is made.
Final command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/FullGridCappedCollarHierarchy.lean`;
exit 0, no diagnostics. All owned jobs exited; temporary capacity API scratch removed.
All fifteen own imports and refreshed capstone index entries are verified.

Activation SHA-256 values:

- Finite activation: `1625673ef2d59453edef68fa71f6422b5904c90106d5d0b77e91ce1fb492bce3`.
- Physical gain: `6495929af4fe9b23b2853cca2c355002b73e5755d3473695f040f9beef3e4d4b`.

Evidence: `/tmp/bsu-capped-support-activation.log`, `/tmp/bsu-physical-capped-activation.log`,
`/tmp/bsu-capped-activation-{axioms,final,index,lint}.log`,
`/tmp/bsu_capped_activation_axioms.lean`. All 26 public theorem names audited
exactly once, only `propext`, `Classical.choice`, `Quot.sound`. Printed capstone
and gain/source definitions inspected. All fifteen earlier source hashes unchanged.
Final command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/PhysicalCappedActivation.lean`;
exit 0, no diagnostics. Global lint passes; all owned jobs exited and temporary
API probe removed. Partial search `/tmp/bsu-capped-activation-search.log` reports
213 matches in 56 modules, 82 after cap; source coverage is older, semantic
coverage unmeasured. No exhaustive novelty claim follows.

Reusable proof repairs: expose the explicit function composition before applying
measurability of the compact support map to low/high array maps; leaving it implicit
causes a default-heartbeat definitional-equality timeout. Name the array measurable
maps and keep the compact-map proof separate. Prefer an explicit `change` and
`simp only` over `unfold` plus `simp_rw` across actual-source subtype coercions.
`Finset.sup'_mem` is a closure-under-sup lemma, not finite
maximum attainment; use `Finset.exists_mem_eq_sup'`. Unfold `LogarithmicGridSource.restrict`
when simplifying the source kernel on the right side of a restricted-grid bound.
Expose Ioi membership as an inequality before arithmetic tactics. Import checks can
spend minutes in `lean_mark_persistent` under shared memory pressure; inspect the live
owned process and keep polling its handle instead of restarting after an observation timeout.
For a supremum-range goal left in `(fun ρ => ...) ρ` form, use an explicit `change`
before rewriting the all-low coefficient identity. Natural-number nonlinear
contradictions may need explicit `Nat.zero_le k` and `Nat.zero_le (k ^ 2)` inputs.

Schur package SHA-256 values:

- Geometry: `91e66c439bb52ef3cc5f0fb32fc15e47c2614949a8d10d23620e90ae46c29ab9`.
- Exact support: `249f9bea751b9ba8c5a5ce8c88fd1c6b3c3cab292266c8cbf95bba37be9e7980`.
- Dyadic splitting: `37f23f952324a5bc85b3a628e4b2994ccbc99a94a80c6e1cbd2fdf884327ef30`.
- Physical refinement: `c120590bca4fb721c66ea317804b9631cc90d7e582d7ddbb2664da08212fd5a9`.
- Monotone hierarchy: `8ef01a80da29ed464c42d9df631539908297b10158cb6c5606967ecf855ee573`.
- Full signed-Gram receiver: `9dc409594e17bd54b97b38b351addc11dd869ebea53f14d4c1087c3151383c33`.

All six leaves compile cleanly; all 85 public theorems audited exactly once,
69 in `/tmp/bsu_schur_pair_axioms.lean` and 16 in
`/tmp/bsu_signed_physical_gram_axioms.lean`. Only `propext`, `Classical.choice`,
and `Quot.sound`; general-source signatures and concrete Gram definitions inspected.
Final command: `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedPhysicalGramEnergy.lean`;
exit 0, no diagnostics. Logs `/tmp/bsu-schur-pair-{axioms,final,index,lint-final}.log`
and `/tmp/bsu-signed-physical-gram-axioms.log`; complete integrity manifests
`/tmp/bsu-schur-pair-final-{manifest,integrity}.json`. All 23 owned imports occur
once; all 17 earlier hashes unchanged. README remains byte-identical and read-only.
Both temporary API probes removed; all owned jobs exited. Global lint's unrelated
concurrent failures are listed above. Partial searches `/tmp/bsu-schur-pair-search.log`
and `/tmp/bsu-signed-schur-search.log` do not justify exhaustive novelty claims.

Signed-Gram cutoff SHA-256 values:

- Capacity: `95469f4664f01de5dd302d81a58445005f8d4d020dbe993fb2bc8e85101da435`.
- Physical comparison: `6be920f79c818fa42fdde188b73593c1bed983a76d0e52c9f5d8c23321ec4a2e`.
- Optimized hierarchy: `7a0da76505f74745f800ee50fe6323540464d74274095fc051209cb46782327d`.

All three leaves compile cleanly; all 34 public theorems audited exactly once in
`/tmp/bsu_signed_gram_cutoff_axioms.lean`. Only `propext`, `Classical.choice`,
`Quot.sound`; concrete source, packet and supremum definitions inspected.
Final direct command `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramCutoffHierarchy.lean`
passed with exit 0 and no diagnostics. Evidence `/tmp/bsu-signed-gram-final.exit`,
`/tmp/bsu-signed-gram-{capacity,comparison,hierarchy,axioms,final}.log`, and
`/tmp/bsu-signed-gram-{manifest,integrity,audit-coverage}.json`. All 26 own imports
occur once, all 23 earlier hashes unchanged, read-only README unchanged.
Index and new capstone discovery pass. Current global lint failures are listed
above; no foreign file was modified to clear them. Initial capacity and next dual
searches are partial, with older coverage and unmeasured semantic completeness.

Lean repairs: normalize sqrt(R)*(sqrt(R)*A) by associativity and sq_sqrt before
arithmetic tactics; the nonlinear tactic does not automatically multiply the
square identity by A. For integral_sub, expose the pointwise difference using
`change` before rewriting the integral of a function subtraction. Normalize
signed offsets with `sub_eq_add_neg` before commuting addition.

Signed-Gram trial package SHA-256 values:

- Support: `a082cd5a304a9c32d550f5bc55afdad2bd202fb8d65751ac1c871c90321a2396`.
- Physical prices: `f241f55eda32e59665150b4bae5a0e9feba0d4dc701e3ecac2d336fcdd0c75e3`.
- Trial certificate: `fd195d5c55de946103bb41e241f335655d30f0aabaf535c33f58b90ac883ca8b`.

All three final dependency checks pass with empty logs. All 49 public theorems
audited exactly once in `/tmp/bsu_signed_gram_dual_axioms.lean`, using only
`propext`, `Classical.choice`, and `Quot.sound`. The exact dual identity,
zero-gap factorization, finite and limiting error bounds, actual extended-energy
and smooth normalized receivers, and concrete price/gap/remainder definitions
were printed and inspected.
Final direct command `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramTrialCertificate.lean`
passed, exit 0 without diagnostics. Evidence `/tmp/bsu-signed-dual-final.exit`,
`/tmp/bsu-signed-dual-{support,prices,trial,axioms,final}.log`, and
`/tmp/bsu-signed-dual-{manifest,integrity,audit-coverage}.json`. All 29 own imports
occur once, all 26 earlier hashes unchanged. README was byte-identical at that
audit. The user subsequently updated it to 260 lines with Trap 10; read fully,
still read-only, SHA-256 `dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
Index and capstone discovery pass; global lint failures are listed above.
Temporary API probe removed; all owned Lean and search jobs exited.

Lean repairs: for complex inner products, expand packet sums with `simp only`
before `simp_rw [inner_smul_left]` or `inner_smul_right`; broad simp can coerce
real complex scalars to real scalar actions too early. To combine common
denominators use `← mul_div_assoc` and `← Finset.sum_div`. Give the full target
type for products proved nonnegative before `nlinarith`, avoiding unresolved
numeric metavariables. Use explicit integrands for integral subtraction/addition.

Explicit dyadic producer package SHA-256 values:

- Smooth source: `46205aa0c5a389ec04fedafa6f8d2e4e6c5ee5b1e9d7e73169b0fa1056b7704a`.
- Producer: `24c9734e4a331075063fe8116e929ef05156554baf3a710dd98adda855f11fe0`.
- Coefficient uniqueness: `e10da9d59fc6c1a32f3f5993e13a869cab781ae3d7854685c5343723b942f00d`.
- Full Gram cutoff: `11fd46aeb8bc791b3883de96a0a3cf4754f47d2bde872df0da8e80af9a614960`.

All four leaves compile without diagnostics. All 55 public theorem axiom audits
pass exactly once in `/tmp/bsu_dyadic_gram_axioms.lean`, using only `propext`,
`Classical.choice`, and `Quot.sound`. Printed signatures and concrete smooth
source, anchored packet, producer, triangular weight, and full-Gram definitions
confirm there is no supplied analytic interface.
Final direct command:
`lake --old env lean GaloisForLFunctions/BiScaleUncertainty/DyadicGramConditioning.lean`;
exit 0, empty log. Evidence `/tmp/bsu-dyadic-final.exit`,
`/tmp/bsu-dyadic-{source,producer,triangle,gram,axioms,final,index}.log`, and
`/tmp/bsu-dyadic-{manifest,integrity,audit-coverage}.json`.
All 33 owned imports occur once; all 29 earlier source hashes are unchanged.
Index refresh and three requested capstone discoveries pass
(`/tmp/bsu-dyadic-discovery.json`). At that package-11 audit, global lint reported
eleven foreign umbrella failures (`/tmp/bsu-dyadic-lint-final.log`). Read-only README hash remains
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
Temporary API probe removed; all owned jobs terminal. No full/umbrella build,
numerical experiment, heartbeat increase, commit or push.

Reusable Lean repairs: bind the two signed terms with an explicit `Finset.sum`
lambda when notation otherwise loses the second term's index. Force inversion
in ℝ before coercing the scalar to ℂ. Normalize natural zero casts in integer
indices before rewriting atom pairings. Use an explicit real-valued `change`
for `RCLike.re` of coerced real inner products. Expose beta-redexes before
rewriting antitone function values; use the verified `Nat.pow_le_pow_right`
for natural cutoff bounds.

Physical minimum-response package SHA-256 values:

- Selector: `2f409903d0f7e1e62e3767d985a58e567c5e59bd4eabed71e09d4c7cd000e9db`.
- Linear optimality: `ea4d38d015470d288fb2ee6b7bcf009ac573c722e1aa832045a77cfdbc080ec9`.
- Cutoff ladder: `1a5cb7a77fe22c3a88b0ebef726e29561a87b95cd8f02210baf31ca21faa824b`.

All three leaves compile without diagnostics. All 43 public theorem axiom audits
pass exactly once in `/tmp/bsu_minimum_response_axioms.lean`, using only `propext`,
`Classical.choice`, and `Quot.sound`. Printed capstones and concrete selection,
response, cost, accepted-step and ladder definitions inspected.
Final direct command:
`lake --old env lean GaloisForLFunctions/BiScaleUncertainty/SignedGramResponseLadder.lean`;
exit 0, empty log. Evidence `/tmp/bsu-minimum-response-final.exit`,
`/tmp/bsu-minimum-response-{selection,optimality,ladder,axioms,final,index}.log`, and
`/tmp/bsu-minimum-response-{manifest,integrity,audit-coverage}.json`.
All 36 owned imports occur once; all 33 earlier source hashes remain unchanged.
Index refresh and three requested capstone discoveries pass
(`/tmp/bsu-minimum-response-discovery.json`). At the package-12 audit global lint
had six foreign umbrella failures; see that run's log. README remained byte-identical at the current
260-line hash. Temporary API probe removed; all owned jobs terminal.

Reusable repair: for a measurable selection cell, prove its explicit equality
with the intersection of the active collar and the price-equality set before
applying measurability. Broad simp can turn the target into measurability of a
Prop-valued predicate. Scratch API audits must open the same namespaces used
by unqualified API checks.


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
