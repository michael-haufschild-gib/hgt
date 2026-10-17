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
11. [ ] Develop sharp Schur-coupled growth and matching finite-limit asymptotics. The general transfer does not settle these or the full 100-contribution objective.

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
All 26 new axiom/signature audits and final direct recheck pass. Next: unequal
product pairs, general nonzero Schur residuals, strict optimized gaps, and matching
leading-law audits below.
Previous goal turn is classified as progress: full-grid capped monotonicity,
hierarchy comparison, and quantitative actual-source saturation passed direct Lean
and all 58 axiom audits. Current activation work extends that verified result.

Latest goal turn is classified as progress: all three product-coupling leaves and
41 axiom audits passed, adding actual source coupling and a monotone hierarchy.
Current search `/tmp/bsu-paired-cutoff-search.log` locates reusable physical tail,
array-capacity, and paired-support inputs; semantic coverage remains unmeasured.
The next package must prove its own paired capacity law before using the old tail
argument. A prior independent-allocation rate is not a proof of coupled saturation.

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
Current global lint passes; earlier concurrent missing-import failures are obsolete.
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
Old physical shares are unchanged. New densities vanish unless 0<y≤1/N.
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

## Accounting

Seven significant packages are Lean-verified, including all axiom/signature audits:
(1) arbitrary-partition energy transfer and optimized certificates;
(2) actual cutoff monotonicity, retraction stability, and quantitative saturation;
(3) paired-sphere support, actual product-zero source transfer, and monotone coupled hierarchy;
(4) paired capacity, cutoff stability, exact frame/limit identification, and fourth-root cutoff control;
(5) exact capped support, finite-vector attainment, and full-grid physical source transfer;
(6) full-grid capped capacity, cutoff monotonicity, optimized hierarchy comparison,
common finite limit, and quantitative actual-source certification;
(7) exact capped activation, quadratic extremal defect, rationalized physical gain,
almost-everywhere equality/strictness classification, and actual-source gain transfer.
Count **7/100** mathematical contributions. Global formal lint now passes.
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
- Current `scripts/formal_tools.py lint`: exit 0, `formal lint passed`.
  Earlier concurrent missing-import failures are obsolete. Evidence:
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
