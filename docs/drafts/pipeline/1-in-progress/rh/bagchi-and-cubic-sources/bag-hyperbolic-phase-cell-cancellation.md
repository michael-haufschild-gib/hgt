# BAG: signed cancellation across complete hyperbolic phase cells

- **ID:** bag-hyperbolic-phase-cells-17az
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); full packet formalization pending
- **Source:** bag-covered-global-defect-cancellation.md, turns 16–17az
- **Statement:** For every fixed positive integer M, the actual sharp-band cubic sum restricted by |(p-r)(q-r)| ≤ M r is o(N/log² N), retaining p ≠ r, q ≠ r and allowing p = q.

## Goal

Cancel the positive hyperbolic core together with its complementary signed phase cells. This is a paper analytic advance inside BAG, not the full cubic estimate. The complement outside every fixed phase radius, growing moments/cofactors and deterministic common-height return remain open.

## Gates

- [x] 0 → 1: concrete actual-prime target and corpus-based proof mechanism.
- [x] 1 → 2: detailed paper proof below; prime-window input independently proved in Lean.
- [ ] 2 → 3: exact unconditional Lean theorem, foreground leaf audit, standard axioms only.

## Corpus inputs checked

- `PrimeAlmostAllShortIntervalsAsymptotic.lean`: explicit bad-set bound at line 584 and almost-all multiplicative-window asymptotic at line 717, for θ > 1/6. The latter gives only fixed-tolerance convergence; the new `ChiCubicPrimeWindowLogRate.lean` derives arbitrary logarithmic rates from the former.
- `PrimeAlmostAllShortIntervals.lean`: zero-weight decay beats every logarithmic power, via the unconditional seven-twelfths density specialization.
- `Sieve/PrimePairAverageSharp.lean:126`: uniform averaged shifted-prime-pair upper bound, with explicit sieve remainder. Its parameter specialization is audited on paper below; Lean composition remains.
- `Sieve/PrimeWindowBrunTitchmarsh.lean:38`: uniform prime count bound in integer intervals.
- `ChiPrimeGaussianHyperbolicCore.lean:692`: the actual positive core already has mass at least c N/log² N; taking absolute values cannot settle this target.

## Paper proof overview — packet not yet formalized

Write a = p-r, b = q-r, u = ab/r. The original phase is e(u), since p+q-r is integral. Fix integer M ≥ 1 and retain |u| ≤ M. The exact integral of e(u) over [-M,M] vanishes. A sharp cutoff suffices: its moving boundary is paid explicitly during smoothing. This avoids needing a new smooth phase cutoff construction.

1. Split by |a| < |b|, its p/q transpose, and ties. Symmetry gives twice the first sector. There |a| ≤ L = sqrt(2 M N). Ties have O_M(N sqrt(N)) integer triples, each bounded by O(1/N), hence are negligible after normalization. Both forbidden contractions stay excluded.

2. Average only q on multiplicative windows δ = N^(θ-1), θ = 1/5. Set Pδ(x) = [ψ((1+δ)x)-ψ(x)]/(δ x). The exact dual formula is

   ∫ Pδ(x) f(x) dx = Σ_n Λ(n)/δ ∫_[n/(1+δ),n] f(x)/x dx.

   Its normalization is κδ = log(1+δ)/δ, tending to 1. Do not sample the exceptional set at prime anchors. The new Lean leaf proves instead ∫_[N,2N] |Pδ-1| = o(N/log^A N) for every fixed A, using the explicit bad-set bound and every-log-power zero-weight decay.

3. On the ordered sector the phase slope is O_M(N^(-1/2)). Smooth V, W and 1/log q have controlled derivatives on their fixed compact ranges. Averaging displaces q by O(N^θ). The integer volume of the critical region is O_M(N² log N), so the smooth variation is power-negligible. Each of the sharp q-band, ordering and hyperbolic boundaries has O(N^θ+1) affected q's per (r,p); at most O_M(N sqrt(N)) such pairs occur. Their physical 1/N weight gives O_M(N^(1/2+θ) log^C N), also negligible. This includes the small x-sliver outside [N,2N].

4. Replacing the prime q measure by Λ(q)/log q adds proper prime powers. There are O(sqrt(N) log N) of them. For each fixed q, the number of integer (r,p) with 0 < |a| ≤ L and |ab| ≤ M r is O_M(N log N); each entry is O(1/N). Total prime-power error is power-negligible. The same fixed-q count bounds the kernel testing Pδ-1 by a fixed logarithmic power, so the arbitrary-log L1 rate pays the replacement error without any equidistribution assertion about prime anchors.

5. After replacement q has density dq/log q. In the bulk δ₀N away from both band edges and for |a| ≥ N^ε, change variables b = r u/a. The band contains the entire u interval [-M,M] for sufficiently large N. Freeze only V(q/N)W(pq/(rN))/log q at q=r, keeping p and r literal. Its integrated error is O_M(1/(a²log N)) per prime pair. The frozen full u integral is exactly zero.

6. Ordering removes |u| ≤ a²/r. Its integral has absolute value O(a²/r). The Jacobian r/|a|, physical 1/r, and q density 1/log N give O_M(|a|/(N log N)) per prime pair. Uniform prime interval upper bounds at length sqrt(N), together with O(N/log N) anchors, make this O_M(N/log³ N).

7. For 1 ≤ |a| ≤ N^ε, the q integral is at most O_M(N/(|a| log N)). An averaged shifted-prime-pair bound Σ_{d≤D} # {r ~ N: r,r+d prime} ≤ C N D/log² N, with C independent of D, implies by partial summation an O_M(ε N/log² N + N/log³ N) contribution. The explicit sieve remainder is paid in the audit below.

8. For |a| ≥ N^ε and r within δ₀N of the band endpoints, dyadic interval prime bounds give Σ_p 1/|p-r| ≤ C_ε. There are O(δ₀N/log N) prime anchors, yielding O_M(C_ε δ₀ N/log² N). First let N tend to infinity, then δ₀ tend to zero for fixed ε, then ε tend to zero. This order matters.

## Formalization boundary

- CLOSED IN LEAN: arbitrary-logarithmic L1 short-window rate, for every 1/6<θ<1 and therefore θ=1/5. `RHTower.chiCubicPrimeWindowError_logRate` in `ChiCubicPrimeWindowLogRate.lean`; integrability and exceptional sets included.
- CLOSED IN LEAN,18az: actual ordered hyperbolic kernel, uniform real-anchor count, exact prime-point identity and full signed exceptional-error transfer. `RHTower.chiCubicHyperbolicPrimeDensityError_tendsto` proves eventual integrability and normalized convergence without an analytic premise. Audit: `../../../3-formalized/bag-hyperbolic-prime-error-transfer.md`.
- CLOSED IN LEAN,19az: exact finite dual averaging with explicit integrability and correct half-open windows; its complete difference from the signed continuous kernel is negligible. The actual proper-prime-power correction to the original ordered triple packet is also negligible. `ChiCubicHyperbolicPrimeAveraging.lean`; audit: `../../../3-formalized/bag-hyperbolic-prime-dual-averaging.md`.
- CLOSED IN LEAN,20az: actual global kernel variation, every sharp jump, and uniform o(N/log²N) of the complete von Mangoldt sampled displacement throughout the actual short window. `ChiCubicHyperbolicPrimeVariation.lean` and `ChiCubicHyperbolicPrimeSampling.lean`; audit: `../../../3-formalized/bag-hyperbolic-prime-sharp-sampling.md`.
- CLOSED IN LEAN,21az: actual prime-band cumulative and harmonic-weighted pair counts, uniformly for EVERY natural cutoff; full sieve divisor remainder absorbed. `ChiCubicHyperbolicPrimePairs.lean`; audit: `../../../3-formalized/bag-hyperbolic-prime-pairs.md`.
- CLOSED IN LEAN,21az: exact positive dilation identifies the actual dual average with its integrable displaced trace; the complete dual-to-discrete difference is negligible. Composing all actual errors proves original ordered triple-prime packet minus signed continuous kernel is o(N/log²N). `ChiCubicHyperbolicPrimeDisplacement.lean`; audit: `../../../3-formalized/bag-hyperbolic-prime-displacement.md`.
- CLOSED IN LEAN,21az: actual phase-preserving freezing with gap-independent C|x-r|/(N²logN) error, and zero frozen integral over every complete integer-radius phase cell, both gap signs and degenerate pairs included. `ChiCubicHyperbolicPrimeVariation.lean:632` and `ChiCubicHyperbolicPrimePeriods.lean:27`; audit: `../../../3-formalized/bag-hyperbolic-prime-period-freezing.md`.
- Full fixed-integer-radius signed phase-cell theorem has the detailed paper proof below. Its Lean theorem remains to be built. No conditional wrapper counts as closure.

## Audits during 17az

The averaged-pair sieve specialization is now justified on paper: take P₁=2, h=floor(N^(1/300)), z=h^36. Then h^18=sqrt(z), log(h) is comparable to log(N), and `Sieve/MertensDiffExp.lean:22` bounds exp(mertensS(h)-mertensS(2)) below by a positive constant times log(N). `Sieve/SieveRemainderBound.lean:38` bounds the whole divisor remainder by 2z³ ≤ 2N^(108/300). Thus `sum_card_primePair_le_sharp` gives CND/log²N uniformly for EVERY integer D, once N is large. The original band anchors exceed h, so its lower-anchor exclusion removes none of our pairs. No estimate for each individual shift is being substituted for the averaged theorem.

For smoothing, first use the exact integer recentering identity, THEN extend e((p-r)(q-r)/r) to real q. Extending e(pq/r) directly would introduce the fast factor e(q), invalidating the claimed slow derivative. The recentered interpolant agrees at every integer, including the proper prime powers introduced by Λ/log.

The shrinking-tolerance proof uses the elementary bound zeroShortWeight(x,cY) ≤ c zeroShortWeight(x,Y) for c≥1. Consequently the explicit bad-set bound is at most C ε^(-3) (log(X²)+2)² X Z₀(X), with Z₀ at fixed cutoff coefficient 192/5. Choosing ε=(log(X²)+2)^(-a), every desired logarithmic rate follows from the corpus's every-log-power decay of Z₀. The large-X side condition follows from logarithmic powers being dominated by X^(2θ). `ChiCubicPrimeWindowLogRate.lean` now proves this and the L1 rate; clean foreground leaf audit40319 exited0 with empty output. Imported axiom audit61320 found only standard axioms. Final repeat, index and lint details are recorded in the parent log.

## Detailed paper reduction to the prime-window input

All constants below may depend on the fixed positive integer M and the original fixed V/W profiles. They do not depend on N, the auxiliary exponent ε, or the band-edge fraction η unless indicated. Fix 0<ε<1/4 and 0<η<1/4, and take N sufficiently large depending on these fixed parameters. Set δ=N^(-4/5), H=3N^(1/5), L=sqrt(2MN), and D=floor(N^ε).

The amplitude bounds used here follow from the actual definitions, not an arbitrary-coefficient assumption. `ChiPrimeGaussianProgressionProfile.lean:43` proves a uniform first-derivative bound for V(x)W(ξx), ξ∈[1/2,2], x∈[1,2]. The same compactness proof works on the slightly enlarged positive interval used in a window displacement. The literal cubic entry is `ChiPrimeGaussianCubicMain.lean:35`; its integer phase recentering is theorem 411 there.

### Ordered packet and exact averaging

For fixed prime p,r∈(N,2N], put a=p-r≠0 and retain |a|≤sqrt(Mr). Define, by zero extension outside its displayed support,

f_{p,r}(x) = [2π V(p/N) conj(V(r/N))/r]
  [V(x/N) W(px/(rN))/log x] e(a(x-r)/r)
  1_{N<x≤2N, |a|<|x-r|, |a(x-r)|≤Mr}.

At integer prime q, log(q)f_{p,r}(q) is exactly the original ordered cubic summand. There are at most six boundary points in x. On every continuity interval, |f|≤C/(N log N) and |f'|≤C|a|/(N² log N). The latter bound uses the recentered phase; it would be false for the unrecentered real interpolation.

Write Pδ(x)=[ψ((1+δ)x)-ψ(x)]/(δx) and κδ=log(1+δ)/δ. Finite summation and integration give exactly

∫_[N,2N] Pδ(x) f_{p,r}(x) dx
 = Σ_{n≤3N} Λ(n)/δ ∫_[n/(1+δ),n] f_{p,r}(x)/x dx.

The zero extension makes this formula exact at the band edges too. Since δ≤1/2, 1/2≤κδ≤1. Compare the right side with κδ Σ_n Λ(n)f_{p,r}(n). Every displacement is at most H. Integers whose averaging interval crosses a boundary contribute O(H+1) per boundary, each of size O(1/N) after multiplication by Λ(n). There are O(NL) integer (r,p) pairs, hence the total boundary error is O_M(HL).

Away from boundaries, the number of possibly nonzero n for a given (r,p) is O_M(N/|a|+H+1). The derivative bound and Λ(n)≤log(3N) give total smooth error

O_M[Σ_{r∼N} Σ_{1≤|a|≤L} H|a|/N² · (N/|a|+H+1)]
 = O_M(HL + H(H+1)L²/N).

Both errors are O_M(N^(7/10)+N^(2/5)) and therefore o(N/log²N). This estimate includes every sharp support boundary and uses integer counts only.

### Prime powers and exceptional intervals

For any fixed real x∈[N,2N], the number of integer (r,p) in the ordered hyperbolic support is O_M(N log N), uniformly in x. To see this, group r by j≤|x-r|<j+1. There are at most four r per integer j. For j≥1, at most O(MN/j+1) nonzero integer a occur. The j=0 group contributes O(L), and summing j≤2N gives the asserted bound.

Consequently Σ_{p,r}|f_{p,r}(x)|≤C_M. The complete exceptional-set error is bounded by

C_M ∫_[N,2N] |Pδ(x)-1| dx = o(N/log²N),

using the arbitrary-log L¹ prime-window input. This is a Lebesgue integral bound for the aggregate test kernel; no exceptional set is sampled at prime p or r.

The same counting estimate at integer q bounds the sum of absolute original entries over (p,r) by C_M log N. The total extra coefficient from proper prime powers is

Σ_{N<q≤2N, q nonprime} Λ(q)/log q
 ≤ [ψ(2N)-θ(2N)]/log N = O(sqrt(N)),

by the corpus's unconditional ψ−θ bound. Their whole contribution is O_M(sqrt(N)log N), negligible. Thus the ordered actual-prime packet equals κδ^(-1) times

J_N = Σ_{p,r prime in (N,2N], 0<|a|≤sqrt(Mr)} ∫ f_{p,r}(x) dx

up to o(N/log²N). The original p and r masks and the q≠r exclusion have not been relaxed.

### Cancellation of J_N

For |a|≤D, the x interval has total length O_M(N/|a|), giving an absolute contribution C_M/(|a|log N) per prime pair. The uniform averaged-pair sieve bound proved above implies, by finite summation by parts,

Σ_{1≤d≤D} #{r∼N: r,r+d prime}/d ≤ C N(1+log D)/log²N.

Negative shifts obey the same estimate after reindexing the lower prime. Therefore the small-gap part is at most C_M ε N/log²N + C_M N/log³N.

For |a|>D and N+ηN≤r≤2N-ηN, change variables u=a(x-r)/r. For sufficiently large N, the entire interval [-M,M] lies inside the x band, since |x-r|≤2MN/D<ηN. The remaining ordering constraint deletes exactly |u|≤a²/r. Freeze only the x-dependent amplitude V(x/N)W(px/(rN))/log x at x=r, keeping the p,r weights literal. Its derivative is O(1/(Nlog N)), so the total freezing error for this pair is O_M(1/(a²log N)). Summing over all integer r and a>D bounds the total by O_M(N/(D log N)), hence o(N/log²N).

The frozen integral over [-M,M] is exactly zero because M is integral. The deleted central interval has length 2a²/r. After the Jacobian and original physical 1/r factor, its contribution is at most C|a|/(Nlog N) per prime pair. The actual averaged pair prefix now pays the whole hole directly: with L=floor(sqrt(2MN)), sum_{d≤L} d P_N(d)≤L sum_{d≤L} P_N(d)≤CNL²/log²N. Retaining both gap orientations gives total deleted-center mass O_M(N/log³N). This21az simplification uses the proved actual prefix producer and needs no separate per-anchor prime estimate. Its integral and gap-reindexing assembly remains to formalize.

Finally consider r within ηN of a band endpoint, still with |a|>D. There are O(ηN/log N) such prime r for each fixed η. A dyadic application of Brun–Titchmarsh between D and L gives Σ_p 1/|p-r|≤C/ε, uniformly in r. Bounding the x integral by its support length therefore pays these anchors by C_M η/ε · N/log²N.

Combining the sectors gives

limsup_{N→∞} (log²N/N)|J_N| ≤ C_M(ε+η/ε).

First let η↓0 with ε fixed, then ε↓0. Hence J_N=o(N/log²N). The transpose ordered sector is identical by p/q symmetry. Ties |p-r|=|q-r| have only O_M(NL) integer triples, so their total absolute physical mass is O_M(L), also negligible. **[PROVED HERE, paper]** The prime-window input, uniform real-anchor count, actual exceptional-error transfer, exact dual averaging and prime-power removal are now proved in Lean. The complete discrete-to-continuous transfer and actual averaged/harmonic prime-pair prefixes are now proved in Lean. Completed-period cancellation, freezing error, ordering holes and band edges remain to formalize.

### Boundary of this result

No assertion is made about the complement |(p-r)(q-r)|>Mr. In particular, convergence for every fixed M cannot be exchanged with M→∞ inside the full cubic without a separate uniform tail argument. The hard full BAG cubic remains open.

## 18az — actual exceptional-error transfer in Lean

The 17az prime-window L1 input is verified in the current tree. The next producer is the normalized complex integral of its signed error against the literal ordered hyperbolic prime kernel, retaining V/W, both exclusions and the physical 1/r and 1/log q factors. This should vanish without any kernel-bound premise.

For the uniform fixed-real-q kernel bound, reindex by d=|p-r| rather than rounding q. For each d≥1, the hyperbolic constraint and r≤2N imply |q-r|≤2MN/d. Each sign of p-r determines p from (d,r). Thus an interval-cardinality bound and the harmonic sum give O_M(N log N) pairs, uniformly in real q. This even bounds a larger support without the ordering exclusion; the actual kernel keeps that exclusion. The source has `card_Icc_cast_le` and `sum_Icc_one_div_le_one_add_log`, both inspected. Formalization will attach the counting bound to the actual weights and integrate the complete error, not stop at a counting lemma.

### 18az result

`ChiCubicHyperbolicPrimeKernel.lean` now proves the actual transfer, including
eventual integrability and normalized complex-norm convergence. The
uniform integer count retains both signs of the gap and every real
interpolation point; the literal kernel retains V/W and both exclusions.
Its exact prime-point identity is proved against the original main entry.
Final leaf37885 passed with empty output. Audit details and the exact
statement are in `../../../3-formalized/bag-hyperbolic-prime-error-transfer.md`.

The next unformalized step is exact dual averaging, followed by the
sharp-support displacement and prime-power errors. Corpus search located
`Sieve/CharacterWindowMass.lean:20` (`psi_sub_eq_sum_Ioc`) and
`ChebyshevLagWindow.lean:56` (`psi_sub_psi_eq_sum`); both source statements
were checked. Pointwise dual windows are [n/(1+δ),n), because ψ(x+δx)-ψ(x)
includes the upper integer and excludes the lower integer. Integral
endpoint conventions can be changed only after the measure-zero argument.
Finite integration uses `MeasureTheory.integral_finsetSum`, with each term
proved integrable. None of these facts alone closes the discrete packet.

## 19az — total variation pays sharp averaging boundaries

The exact dual average and proper-prime-power correction are now
formalized in `ChiCubicHyperbolicPrimeAveraging.lean` (leaf52251 and imported
axiom/API1310 passed). The remaining
displacement estimate admits a simpler proof using the actual kernel's
total variation. This is a replacement proof of the same sharp-boundary
step, not a change of route or an assumed regularity premise.

For a fixed prime pair put d=|p-r|≥1. Its ordered support is the union of
at most two intervals obtained by intersecting (N,2N] with
[r-Mr/d,r-d) and (r+d,r+Mr/d]. Empty intervals contribute zero. The total
length is at most2Mr/d≤4MN/d. The actual recentered amplitude has norm
at most C/(Nlog N) and derivative norm at most C(d+1)/(N²log N), uniformly
on the band. Both bounds concern the literal V/W and 1/log x factors.
The derivative claim follows from the compact smooth profile bounds in
`ChiPrimeGaussianProgressionProfile.lean:45` and the recentered phase.
Its proof is private there and must be exposed by an appropriate actual
producer or rebuilt in the new leaf; it is not an available public lemma.

The zero-extended pair kernel therefore has total variation at most

    4C/(Nlog N) + [C(d+1)/(N²log N)]*(4MN/d)
      ≤ C_M/(Nlog N).

The four endpoint jumps are included, regardless of open/closed endpoint
conventions. Nonempty support forces d²<Mr≤2MN. Integer counting alone
gives O_M(N sqrt N) eligible pairs, hence total variation of the complete
actual K(N,M,·) is O_M(sqrt N/log N). It is integrable and zero off the
original band by its actual definition. **[PAPER PROOF; not yet Lean]**

Here is the discrete sampling estimate needed to use this bound. If f
has finite variation V on [0,B], 0<t≤1, and h is a natural number with
(1-t)B≤h, then

    Σ_{1≤n≤B, n integer} ‖f(n)-f(tn)‖ ≤ h V.

Indeed let v(x)=Var(f;[0,x]), which is nonnegative, nondecreasing and
satisfies v(0)=0. For n≤B, max(0,n-h)≤tn≤n, so the summand is at most
v(n)-v(max(0,n-h)). Summing telescopes: the surviving upper tail has at
most h terms, each at most v(B)=V. This argument allows jumps at every
endpoint. The corpus supplies finite-interval additivity of eVariationOn,
its distance bound, and `variationOnFromTo`; the new sampling estimate
still needs a Lean proof.

For δ=N^(-4/5), write x=nt in every dual integral. The dual average is
δ⁻¹∫_[1/(1+δ),1] Σ_{n≤3N} Λ(n)f(nt) dt/t. Its difference from
κδ Σ_{n≤3N} Λ(n)f(n), κδ=log(1+δ)/δ≤1, is at most

    log(3N) * ceil(3Nδ) * Var(f;[0,3N]).

Apply f=K(N,M,·), retaining its zero extension. All sharp boundaries are
paid at once, and the bound becomes O_M((N^(1/5)+1)sqrt N), hence
o(N/log²N). No exceptional set is sampled at primes. The change of
variables, finite integration, explicit actual variation bound and
discrete sampling estimate remain formalization obligations; the exact
dual identity alone does not discharge them.

Corpus evidence: `HTGeometry/BoundedVariationRiemannSum.lean:20,49,124`
provides complex interval quadrature and a bounded-Lipschitz product
estimate; source read. Mathlib `Topology/EMetricSpace/BoundedVariation`
provides `dist_le`, `Icc_add_Icc`, `sum'`; `VariationOnFromTo` supplies
monotone variation primitives. The Lipschitz-only translation suggestion
from deep search cannot handle this sharp kernel's jumps by itself.

## 20az — actual variation producer

The Lean construction uses the actual scaled **logarithmic** profile, whose
existing compact derivative budget controls all V/W and 1/log x factors.
Its uniform Lipschitz producer is now exposed from
`ChiPrimeGaussianProgressionProfile.lean`. For each pair, clamp the amplitude
to the intersection of [N,2N] with [r-Mr/d,r+Mr/d]. The product of the band,
outer interval and complementary inner interval has variation at most6.
This counts all endpoint jumps without depending on their conventions.
The pair variation is at most (8CM+12pi)/(N log N).

For the full sum, reuse the proved hyperbolic integer-pair count at real
anchor0. Nonempty support implies d²≤2MN and hence d≤(M+1)sqrt N. With
L=(M+1)sqrt N, active pairs lie in the integer strip with parameter2LN.
The existing count gives at most28(M+1)N sqrt N log N pairs, so the actual
kernel variation is O_M(sqrt N). This deliberately retains the harmless
extra logarithm: the required displacement is still
O_M((N^(1/5)+1)sqrt N log N)=o(N/log²N). No new sharp pair-count theorem is
needed to close that same mathematical step. Final foreground leaf56733
passed with empty output: `bag-hyperbolic-prime-variation-final-20az.log`.

The sampling proof is also now formalized. The corpus's monotone variation
primitive turns the sampled norm differences into a telescoping sum,
bounded by h times total variation when (1-t)B≤h. Its actual-family
specialization retains every integer through floor(3N), every von Mangoldt
weight, and every t in [1/(1+δ),1], δ=N^(1/5-1). The complete complex
displacement is bounded by C_M(3Nδ+1)sqrt N log(3N). Multiplication by
log²N/N gives a bound by fixed constants times log³N/N^(3/10) and
log³N/sqrt N, proving uniform negligibility throughout the actual window.
Final foreground sampling leaf43723 passed with empty output:
`bag-hyperbolic-prime-sampling-02az.log`. Imported axiom/API92008 passed:
all20 declarations use only propext, Classical.choice and Quot.sound.
Both leaves are wired once; index13677 passed. Lint92001 still fails
outside the four changed BAG leaves; full audit is on the P3 card.
Deep corpus search `bag-variation-sampling-search-20az.json`
returned usable additivity and local-variation arguments. The proposed
sieve overlap ingredient alone does not prove this complex sampling bound;
the new draft's own indexed helper hits were not treated as independent
evidence.

### Next exact integral step

Let a=1/(1+δ), w(t)=1/(δt), c=(1+δ)/δ and V=ΣΛ(n)K(n), summing through
floor(3N) with zero extension. Positive dilation x=nt gives
A=∫_[a,1]w(t)ΣΛ(n)K(nt)dt. The constant weight c has mass exactly1.
On this whole interval, 0≤w≤c and |w-c|≤1. Thus, if E bounds the complete
sampled difference uniformly there,

    ‖A-V‖ ≤ E + (1-a)‖V‖ ≤ E + δ‖V‖.

This follows by integrating w(t)(ΣΛ(n)K(nt)-V)+(w(t)-c)V. The actual
uniform kernel bound and Λ(n)≤log(3N) give
‖V‖≤64pi(M+1)*3N log(3N). Its normalization error is therefore
O_M(δ log³N), negligible. This closes the direct A-to-V comparison on
paper using the newly proved uniform sampling theorem; no reciprocal-log
primitive or division by κ is required. The Lean obligations are global
zero extension/integrability, exact positive dilation of each half-open
dual integral, finite integral exchange, and this comparison. They remain
open; uniform sampled negligibility alone does not identify A with V.

Corpus lexical search found `Sieve/LogPolyRestrict.lean:68`, whose proof
uses `intervalIntegral.integral_comp_mul_left` and endpoint-nullity;
mathlib's exact complex-valued dilation and `Integrable.comp_mul_left'`
were source-read. The continuous-real-only helper in
`Sieve/LogPolySetScaling.lean:28` cannot be applied directly to the sharp
complex kernel. Deep search's tanh/log-derivative proposals were unrelated
and were not used. This is the next actual-family target, followed by the
averaged prime-pair specialization and completed-period cancellation.

## 21az — actual packet transfer and the next arithmetic input

The original ordered prime packet now transfers to the literal signed continuous
kernel at o(N/log²N), for every natural M, without an analytic premise.
Exact positive dilation pays integrability, all half-open boundaries and
normalization debt. Clean leaf and standard-axiom audits:
`../../../3-formalized/bag-hyperbolic-prime-displacement.md`.

Next conjecture: the actual prime-band pair prefixes satisfy CND/log²N
uniformly for every natural cutoff D, and their harmonic-weighted prefixes
satisfy CN(1+log D)/log²N. The source-read public producer
`Sieve/GenericMarkerAnalytic.lean:308` already specializes the complete
averaged sieve at an arbitrary integer base, keeping its full D N^(3/4)
remainder. Identify its bigPrimeSet with the literal primeProfileBand, pay
the floor/log changes and the remainder, then apply finite Abel summation.
This replaces no correlation premise and optimizes no sieve constant; it
is the required small-gap input to the actual continuous integral.

## Log

- 2026-10-06 — 21az: previous turn is verified progress: actual global variation and the complete uniform weighted sampled displacement have clean leaf/standard-axiom audits. Target the actual A-to-V integral comparison, then compose it with19az to transfer the original ordered prime packet to the signed continuous kernel. Use exact positive dilation, all half-open endpoints, literal zero extension and termwise integrability. Constant-weight comparison pays the normalization debt by delta times the actual discrete norm. No generic integral wrapper or new analytic premise counts as closure. Full signed cubic/complement, growing moments/cofactors and common-height return remain open.

- 2026-10-06 — 20az: previous turn is verified progress: exact actual dual averaging and proper-prime-power removal passed leaf and axiom audits. Current target is the actual kernel's total variation, including every support jump, then the dual-to-discrete displacement. Use the existing proved Gaussian profile budget; no regularity premise. A derivative estimate over the full band is too weak: clamp to the hyperbolic support interval before estimating variation, then retain all cutoff jumps. No full cubic or RH closure is claimed.

- 2026-10-06 — 19az: previous turn is verified progress: actual exceptional-error transfer has a clean leaf and standard-axiom audit. Continue the same signed phase-cell proof. Target exact finite dual averaging attached to the literal kernel, with integrability, then control displacement across every sharp boundary and remove proper prime powers at the required scale. The finite dual interval is Ico(n/(1+δ),n); no sampled exceptional-set claim is permitted. Full cubic/complement, growing moments/cofactors and common-height return stay open.

- 2026-10-06 — 17az: discovered this mechanism from the corpus's almost-all short-interval asymptotic and actual positive hyperbolic core. No Lean changes or claimed cancellation theorem yet. Search logs: `/tmp/bag-hyperbolic-complement-search-17az.json`, `/tmp/bag-prime-phase-cell-variance-search-17az.json`; rate search ongoing when this card was created.

### 21az next signed step: retain the phase while freezing

Source factorization in `ChiCubicHyperbolicPrimeVariation.lean:221` gives
actual amplitude = actual constant coefficient × scaled logarithmic profile
× recentered oscillation. Freeze only that profile at x=r. Its proved
Lipschitz producer169 in `ChiPrimeGaussianProgressionProfile.lean` gives

    ‖A(x)-A(r)e(2π(p-r)(x-r)/r)‖ ≤ C |x-r|/(N²logN),

with C independent of the gap and actual V/W retained. On the complete
phase interval |x-r|≤Mr/|p-r| this integrates to O_M(1/(d²logN)).
The frozen complete interval integrates to zero at every integer M;
subtract the exact ordering hole and pay its absolute mass. This is the
next actual signed-cancellation step, not another sampled-error estimate.
The actual freeze producer now passes its foreground variation leaf audit32589
with empty output: `/tmp/bag-hyperbolic-prime-freeze-02az.log`. Imported
axiom/API89494 passed with only standard axioms. Index48075 passed and its
new public row was checked. Lint96327 has367 large-file warnings and21
unrelated unreachable modules; no owned finding, global lint not clean.
Complete-period integration subsequently passed as recorded below.

Exact period identity to formalize next: for d=|p-r|>0, R=Mr/d,
k=2pi(p-r)/r and r>0,

    integral_[r-R,r+R] A(r) e(k(x-r)) dx = 0   (M natural).

Translate x by r; finite real dilation gives k^(-1) times the integral of
e(u) over [-kR,kR]. The corpus's exact complex exponential integral is
2 sin(kR), and kR is either 2piM or -2piM. This works for either gap sign;
no absolute Jacobian may replace the signed interval substitution. Passing
from Icc to Ioc changes only null endpoints. Multiplication by the literal
A(r) retains its V/W/reciprocal/log factors.

For a complete phase interval inside [N,2N], subtract the frozen integral
and bound the actual difference by C |x-r|/(N²logN). Its integral is at
most 2C R²/(N²logN) ≤ 8C M²/(d²logN). Removing the ordering constraint
hole |x-r|≤d costs at most 4pi d/(NlogN). If d>R the actual support is
empty; before summing this error, restrict active pairs to d²≤Mr.
Summing the freeze error over integers d>D is negligible; the hole needs
the actual prime short-interval count already specified in the paper proof.

### 21az new simplification: the complete ordering hole uses the same pair sieve

The newly proved uniform prefix producer eliminates the separate per-anchor
Brun–Titchmarsh input for the ordering hole. Let L=floor(sqrt(2MN)). Every
active pair has d²≤Mr≤2MN, so d≤L. The integral of its removed central
interval has norm at most4pi d/(NlogN), directly from the actual amplitude
norm at every x in that interval. Reindex negative gaps by their lower
prime, retaining both orientations. Consequently the ENTIRE hole budget is

    ≤ 8pi/(NlogN) sum_{1≤d≤L} d P_N(d)
    ≤ 8pi L/(NlogN) sum_{1≤d≤L} P_N(d)
    ≤ 8pi C L²/log³N
    ≤ 16pi C M N/log³N = o(N/log²N).

This follows from the actual unconditional prefix theorem, uniformly in L;
there is no individual-shift decorrelation or unproved local sieve input.
Paper proof is dependency-closed. Lean still must assemble the actual
support-difference integrals and both gap orientations; a standalone
weighted-prefix wrapper would not complete that step. Brun–Titchmarsh
remains needed for the band-edge argument, not for this hole.


### 21az final audited boundary

The complete frozen-period identity is now Lean-proved for EVERY realN and
naturalM,p,r, with no premises. Degenerate pairs give singleton intervals;
all other pairs use the signed dilation and integer sine cancellation above.
`ChiCubicHyperbolicPrimePeriods.lean:27`,79 lines. Final foreground leaf54837
exit0 empty; imported period/freezing axiom90972 exit0, both standard axioms
only. New period import wired once; index34675 passed and both new API rows
checked. Final lint86341 exit1:367 large-file warnings,22 unrelated
unreachable modules, no owned BAG finding. See
`../../../3-formalized/bag-hyperbolic-prime-period-freezing.md`.

No owned process remains running and all seven owned21az API/axiom scratch
sources were removed. Logs/search JSON remain. Next target is the literal
sharp-support integral difference, followed by the aggregate freezing error,
small-gap harmonic bound, ordering-hole reindexing and band-edge control.
Full signed cubic/complement, growing moments/cofactors, common-height
return and RH remain open. The goal is still active.

## 22az — actual sharp-support integral assembly

Previous21az turn is verified progress: actual transfer, cumulative/harmonic
prime-pair producers, gap-independent phase-preserving freezing and exact
complete frozen periods all passed leaf and standard-axiom audits. Target
now: the LITERAL integral over each sharp ordered support, its exact outer
minus central-hole identity in the bulk, then complete finite aggregation.
No assumed integral comparison or regularity budget is acceptable.

Use the actual kernel's already proved continuity/measurability for finite
integral exchange. For p≠r put d=|p-r|, R=Mr/d. Its support lies in
[r-R,r+R], so the actual amplitude norm gives integral norm≤8pi M/(dlogN)
without a bulk restriction. When the complete outer interval lies strictly
above N and below2N and d≤R, actual support equals outerIcc minus innerIcc.
The proved frozen full-period integral is zero. Integrate the actual
freezing error on the outer interval and retain the entire inner integral.
Inactive R<d cells are empty. The new21az prefix producer pays the complete
hole through its first gap moment; preserve both gap orientations.

The continuous-kernel limit and original fixed-radius packet remain
unproved in Lean. Full cubic/complement, growing moments/cofactors and
common-height return remain hard open mathematical problems.

### Complete actual hole mass, including clipped edge holes

Define the hole integral for each original pair as the actual amplitude
integrated over [r-d,r+d] intersect [N,2N]. Sum its NORM over EVERY original
prime pair p≠r with d²≤Mr, not only bulk anchors. The norm bound on the
actual band and interval measure give4pi d/(NlogN) for every such pair;
clipping at the band only decreases the measure. The21az first-moment
argument therefore proves this full nonnegative mass is o(N/log²N).
This stronger actual mass producer will dominate every bulk ordering hole.

To formalize it, first reindex the literal finite pair sum into both gap
orientations and the already proved count P_N(d). The required identity is
sum_{p,r in band,p≠r,d≤D} f(d) = 2 sum_{1≤d≤D} P_N(d) f(d), with d=|p-r|.
For the positive orientation use the bijection (p,r)↔(p-r,r), inverse
(d,r)↦(r+d,r); obtain the negative orientation by swapping p,r. No pair,
cutoff endpoint or orientation may be sampled or dropped. This identity
also transfers the proved harmonic count to actual small-gap integrals.

### 22az actual support-integral producer now compiled

`ChiCubicHyperbolicPrimeIntegral.lean` proves the literal pair integral,
its integrability, exact finite decomposition of the original continuous
kernel, emptiness of inactive cells, and the all-cell norm bound
8pi M/(dlogN). In each complete bulk cell it proves the exact outer-minus-hole
identity and the actual bound C M²/(d²logN)+4pi d/(NlogN), deriving C from
the proved profile rather than assuming a regularity or cancellation budget.
Both signs, original amplitude factors, sharp endpoints and the central
hole remain. Final foreground leaf49931 exit0 with empty output:
`/tmp/bag-hyperbolic-prime-integral-03az.log`.

The kernel's existing support measurability and amplitude continuity proofs
were exposed publicly without changing their bodies; kernel42580 exit0,
empty output. New integral leaf wired once. Imported axiom/API3108,
index35627 and lint are being audited. Failures01/02 were a missing local
projection in gcongr and unspecified measure metavariables, not a changed
mathematical claim. No heartbeat changes or admitted premises.

### 22az new endpoint-window mechanism: eliminate the band-edge prime debt

Source evidence: LogPhasePhysicalWindow:121 defines the actual W as a
ContDiffBump centered at3/2 with outer radius1/2. Thus W(1)=W(2)=0.
ChiPrimeGaussianCubicRowCancellation:50 proves these boundary zeros;
ChiPrimeGaussianCubicSharpEdges:86 derives its Lipschitz bound on[0,4].
The smoothAFECutoff itself is NOT zero at these endpoints. Retain the
literal physical W(px/(rN)); do not replace it by a generic bounded weight.

NEW conjecture and paper proof: every truncated active cell is paid by
the vanishing of this actual W, with no per-anchor Brun--Titchmarsh input.
Write d=|p-r|>0,R=Mr/d. If the outer interval fails the complete-bulk
conditions, some e in{1,2} satisfies |r/N-e|<=R/N. For every x in the
actual support, |x-r|<=R and p/r<=2, whence
|px/(rN)-e|<=3R/N+d/N. Its argument lies in[0,4]. Therefore
W(px/(rN))<=L(3R+d)/N. Keeping this factor in the amplitude norm and
integrating over length2R gives O(M^2/(d^2 logN)+M/(N logN)).
Since integer d>=1, the second term is dominated by O(M*d/(N logN)).
Together with the already proved bulk bound, EVERY active pair satisfies
C(M+1)^2*(1/(d^2 logN)+d/(N logN)), with no bulk restriction.

The actual prefix A(D)<=CND/log^2N also implies sum P(d)/d^2<=C'N/log^2N
by finite Abel summation, INCLUDING all small gaps. The first moment
through floor(sqrt(2MN)) pays the second term as before. Hence the
ENTIRE signed continuous kernel should be O_M(N/log^3N). This removes
the small-gap/edge double limiting argument altogether, if Lean verifies
every geometric and weighted-sum step. This is stronger than the earlier
paper cancellation proof, not a claim of formal completion. Full cubic
complement, growing moments/cofactors, common-height return and RH remain open.

GapIntegrals final foreground14178 exit0, empty output03az. Both gap
orientations and the actual small-gap mass bound now compile; wired once.
Hole first leaf is running. Imported axioms and remaining index/lint pending.

### 22az current verified leaves and aggregate audit

Hole49596 exit0 empty02az; imported axiom/API46110 exit0, all six public
declarations standard axioms only. Gap imported axiom/API81038 exit0,
all four public declarations standard axioms only. All three finished
Integral/Gap/Hole leaves wired once; index25383 passed and all17 public
API rows checked. P3:bag-hyperbolic-prime-integral-assembly records them.

NEW endpoint-window theorem now passes Lean:
`exists_chiCubicHyperbolicPrimePairIntegral_all_bound` in
ChiCubicHyperbolicPrimeEdges.lean. It derives the actual window boundary
zeros and Lipschitz bound, retains W in the amplitude norm, and proves
the all-pair inequality above without a band-edge or analytic premise.
Final foreground43417 exit0, empty04az log. Wired once. Imported axiom
audit is queued with the final cancellation leaf, not yet claimed.
Failures01/02 were only local inequality tactics/one old name;03 passed
with an unused-tactic warning, removed and rechecked in04.

Moments01 checked the actual moment argument except a misplaced tactic
separator; repaired. Moments02 is running. Cancellation draft assembles
the ENTIRE norm-sum of pair integrals, proves its O_M(N/log³N) bound and
normalized limit, then actual kernel cancellation and composition with
the original ordered prime-packet transfer. It has not yet been compiled.
The resulting ordered theorem will still leave transpose/ties for the
full fixed-radius packet. Full cubic/complement, growing moments/cofactors,
common-height return and RH remain open.

Moments final foreground18316 exit0, empty03az. One constant and threshold
now pay EVERY reciprocal-square gap prefix and first gap moment. Wired
once. Its earlier02 passed with one tactic-style warning; removed in03.
Cancellation first actual leaf audit is now running. The next finite
completion after ordered cancellation is p/q exchange plus the complete
equal-gap sector: |p-r|=|q-r| forces q=p or q=2r-p, hence at most two q
per active pair. This sector is bounded by its actual norm, including
the allowed p=q collision; do not discard it by using the full collision
cancellation theorem on a restricted subset.

### 22az final audited result: ORIGINAL ordered packet cancels

Cancellation85493 exit0, empty03az. Imported axiom98243 exit0: all seven
Edges/Moments/Cancellation public declarations use only propext,
Classical.choice,Quot.sound. Combined with3108/81038/46110, all24 new
public declarations plus two exposed Kernel proofs have standard-axiom
audits. All six new leaves wired exactly once. Index85131 passed; all
new API rows checked. Final authoritative lint11134 exit1:367 large-file
warnings,18 unrelated unreachable modules, no owned BAG finding.
Global lint is not clean. P3:bag-hyperbolic-prime-ordered-cancellation
records the actual theorem and new source mechanism. Frontier and P2
status updated. Earlier pending-audit statements above are superseded.

This turn created and verified the missing signed cancellation producer:
for EVERY naturalM, the ORIGINAL ordered sharp hyperbolic prime packet
has complexnorm o(N/log²N). Stronger intermediate result: the entire
norm-sum of actual pair integrals is O_M(N/log³N), including ALL small
gaps, both signs, complete holes and every truncated edge. The source
window's endpoint zeros eliminate the formerly open edge-prime budget.
No auxiliary cutoff/double limit or analytic premise remains.

All owned jobs terminal. Six owned22az scratch Lean sources removed;
logs and research JSON retained. No full/umbrella builds, raised
heartbeats, admissions/new axioms, numerical experiments, subagents,
commits or pushes. Goal remains active and unmet: transpose/ties for the
FULL fixed-radius packet are next; full cubic/complement, growing
moments/cofactors, deterministic common-height return and RH remain open.

## 23az — full fixed-radius packet, including EVERY equal-gap tie

Previous22az is verified progress: the original ordered prime packet
cancels, with complete source-window edge control and actual gap moments.
Current source inspection confirms this theorem and the frontier boundary.
Goal now: exact full=2*ordered+ties, then actual tie cancellation. Keep
p=q and the reflected tie p+q=2r. No subset may be paid merely by the
whole allowed-collision cancellation theorem.

Paper argument: fix actual p,r in the sharp band and write d=|p-r|.
The equality |q-r|=d forces q=p or q=2r-p, hence at most TWO q for
each pair. The actual main-entry norm is at most2pi/N for realN>0,
by the original V/W bounds and r>N. Thus the complete inner tie sum
has norm at most4pi/N. Its active pairs satisfy d²<=Mr, hence lie
in BOTH orientations of the gaps1..D with D=floor(sqrt(2MN)).
The proved pair prefix and exact two-sign reindexing bound their
cardinality by2A DN/log²N. Consequently the entire tie norm is at
most8pi A D/log²N and its cubic normalization is at most
8pi A sqrt(2M)/sqrtN, which tends to zero. Actual p/q symmetry then
completes the full fixed-radius packet for every naturalM.

This finite completion does NOT pay the full complement |ab|>Mr.
Full signed cubic/tail, growing moments/cofactors and deterministic
common-height return remain the hard open BAG problems after it.

### 23az final audited completion

Both new leaves passed: Ties37784 exit0, empty02az; FullPacket6429
exit0, empty02az. The COMPLETE original fixed-radius packet now cancels
for every natural M, real N→∞. Exact full=2*ordered+ties and original
off-diagonal cubic=full+entire complementary tail are both Lean theorems.
No tie, collision, sign, original source factor or contraction exclusion
is dropped. Imported axiom audit42526 exit0: all eight public declarations
use only propext, Classical.choice and Quot.sound. Both leaves wired once.
Index88869 passed and all eight API rows checked. Final lint38578 exit1:
367 large-file warnings,22 unrelated unreachable modules, no owned BAG
finding. Global lint is not clean. Full evidence and exact source lines:
../../../3-formalized/bag-hyperbolic-prime-full-cancellation.md.

This closes the full fixed-radius paper theorem. Next hard source target
is recorded in bag-full-band-continuous-cubic-cancellation.md: twice
integrate the literal moving profile while retaining both boundaries,
then sum every original p,r row. Its new candidate boundary mechanism
is |p/r-1|/|frequency|=1/(2πN), with a reciprocal-square remainder.
It is not yet a Lean theorem and does not supply full prime sampling.
The full original complementary tail, growing moments/cofactors,
common-height return and RH remain open. Goal active, not achieved.
