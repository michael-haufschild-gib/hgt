# BAG: signed cancellation across complete hyperbolic phase cells

- **ID:** bag-hyperbolic-phase-cells-17az
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean); full packet formalization completed in 23az
- **Source:** ../1-in-progress/bag-covered-global-defect-cancellation.md, turns 16–17az
- **Statement:** For every fixed positive integer M, the actual sharp-band cubic sum restricted by |(p-r)(q-r)| ≤ M r is o(N/log² N), retaining p ≠ r, q ≠ r and allowing p = q.

## Goal

Cancel the positive hyperbolic core together with its complementary signed phase cells. This is a paper analytic advance inside BAG, not the full cubic estimate. The complement outside every fixed phase radius, growing moments/cofactors and deterministic common-height return remain open.

## Gates

- [x] 0 → 1: concrete actual-prime target and corpus-based proof mechanism.
- [x] 1 → 2: detailed paper proof below; prime-window input independently proved in Lean.
- [x] 2 → 3: exact unconditional full-packet theorem, foreground leaf audits37784/6429, imported axiom audit42526; standard axioms only. See ../3-formalized/bag-hyperbolic-prime-full-cancellation.md.

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
- CLOSED IN LEAN,18az: complete signed prime-window error against the literal ordered hyperbolic kernel is o(N/log²N), with eventual integrability, actual V/W, both exclusions and no discarded exceptional set. `RHTower.chiCubicHyperbolicPrimeDensityError_tendsto` in `ChiCubicHyperbolicPrimeKernel.lean`. Uniform real-anchor counting and exact original-entry recovery at prime points are also proved. Audit: `../3-formalized/bag-hyperbolic-prime-error-transfer.md`.
- CLOSED IN LEAN,19az: exact finite dual averaging, with integrability and half-open endpoints, and unconditional negligibility of its complete difference from the continuous kernel. Also closed: actual proper-prime-power correction to the original ordered triple packet. `ChiCubicHyperbolicPrimeAveraging.lean`; audit: `../3-formalized/bag-hyperbolic-prime-dual-averaging.md`.
- CLOSED IN LEAN,20az: actual global kernel variation including all sharp jumps, and uniform o(N/log²N) of the complete weighted sampled displacement throughout the actual dual window. `ChiCubicHyperbolicPrimeVariation.lean` and `ChiCubicHyperbolicPrimeSampling.lean`; audit: `../3-formalized/bag-hyperbolic-prime-sharp-sampling.md`.
- CLOSED IN LEAN,21az: actual prime-band cumulative and harmonic-weighted pair counts, uniformly for EVERY natural cutoff; full sieve divisor remainder absorbed. `ChiCubicHyperbolicPrimePairs.lean`; audit: `../3-formalized/bag-hyperbolic-prime-pairs.md`.
- CLOSED IN LEAN,21az: exact positive dilation identifies the actual dual average with its integrable displaced trace; the complete dual-to-discrete difference is negligible. Composing all actual errors proves original ordered triple-prime packet minus signed continuous kernel is o(N/log²N). `ChiCubicHyperbolicPrimeDisplacement.lean`; audit: `../3-formalized/bag-hyperbolic-prime-displacement.md`.
- CLOSED IN LEAN,21az: actual phase-preserving freezing with gap-independent C|x-r|/(N²logN) error, and zero frozen integral over every complete integer-radius phase cell, both gap signs and degenerate pairs included. `ChiCubicHyperbolicPrimeVariation.lean:632` and `ChiCubicHyperbolicPrimePeriods.lean:27`; audit: `../3-formalized/bag-hyperbolic-prime-period-freezing.md`.
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

The frozen integral over [-M,M] is exactly zero because M is integral. The deleted central interval has length 2a²/r. After the Jacobian and original physical 1/r factor, its contribution is at most C|a|/(Nlog N) per prime pair. The actual averaged pair prefix now pays the whole hole directly: with L=floor(sqrt(2MN)), sum_{d≤L} d P_N(d)≤L sum_{d≤L} P_N(d)≤CNL²/log²N. Retaining both gap orientations gives total deleted-center mass O_M(N/log³N). This21az simplification uses the proved actual prefix producer and needs no separate per-anchor prime estimate. Its actual integral and gap-reindexing assembly is now Lean-proved in22az, including edge-clipped holes.

Finally consider r within ηN of a band endpoint, still with |a|>D. There are O(ηN/log N) such prime r for each fixed η. A dyadic application of Brun–Titchmarsh between D and L gives Σ_p 1/|p-r|≤C/ε, uniformly in r. Bounding the x integral by its support length therefore pays these anchors by C_M η/ε · N/log²N.

Combining the sectors gives

limsup_{N→∞} (log²N/N)|J_N| ≤ C_M(ε+η/ε).

First let η↓0 with ε fixed, then ε↓0. Hence J_N=o(N/log²N). The transpose ordered sector is identical by p/q symmetry. Ties |p-r|=|q-r| have only O_M(NL) integer triples, so their total absolute physical mass is O_M(L), also negligible. **[PROVED HERE, paper]** The complete ORIGINAL ordered packet, including prime-window transfer, sharp displacement, periods, freezing, all gap moments, ordering holes and band edges, is now Lean-proved. The stronger22az argument below eliminates this double limit. Only the transpose/tie finite completion remains for the full fixed-radius packet.

### 22az stronger source-window proof of the continuous step

The earlier small-gap/edge split can be removed for the LITERAL physical
window. This new argument uses its proved compact support and smoothness,
not an arbitrary bounded replacement. Let d=|p-r|>0,R=Mr/d. In a complete
bulk cell the exact frozen period and actual freezing bound give

    |I_{p,r}| <= C M²/(d² logN) + 4pi d/(N logN).

If that outer cell is truncated, some e in{1,2} has |r-eN|<=R. For every
x in the actual support, |x-r|<=R and N<=x<=2N. The actual window argument
y=px/(rN) belongs to[0,4]. Since r>N and x<=2N,

    |y-x/N| <= 2d/N,
    |x/N-e| <= (|x-r|+|r-eN|)/N <= 2R/N.

The corpus's source W has W(1)=W(2)=0 and a Lipschitz constant L on[0,4].
Thus W(y)<=2L(d+R)/N. The original amplitude norm, retaining W, is at
most2pi W(y)/(NlogN). Its support has measure at most2R. Consequently

    |I_{p,r}| <= 32pi L M²/(d² logN) + 16pi L M/(NlogN).

The integer gap satisfies d>=1. A single source constant C therefore
bounds EVERY pair, bulk or truncated, by

    C(M+1)² [1/(d² logN) + d/(NlogN)].

Inactive d²>Mr cells are exactly empty. Put D=floor(sqrt(2MN)); every
active pair lies among both orientations of the gaps1..D. If A(k) is the
actual positive-gap pair prefix, the proved bound A(k)<=B kN/log²N gives

    sum_{d<=D} P(d)/d² <= 2B N/log²N,
    sum_{d<=D} dP(d) <= B D²N/log²N.

For the first assertion use finite Abel summation and decreasing weight
1/d², compare with the constant sequence BN/log²N, and use
1/d²<=2(1/d-1/(d+1)). The second is the exact first-moment comparison.
The previously proved two-orientation bijection then gives

    sum_{p,r} |I_{p,r}| = O_M(N/log³N).

This proves the continuous-kernel cancellation with a full logarithm to
spare; no cutoff exponent, edge-prime theorem or double limit is needed.
Composition with the Lean-proved actual prime-packet transfer gives the
ordered fixed-radius packet theorem. Paper proof dependency-closed;
22az final leaf audits43417/18316/85493 and imported axiom audit98243
all passed, with standard axioms only. The exact original ordered packet
limit is `ChiCubicHyperbolicPrimeCancellation.lean:165`. See
`../3-formalized/bag-hyperbolic-prime-ordered-cancellation.md`.

### Full-cubic boundary remains

23az completed both strict gap orders and EVERY equal-gap tie in Lean,
including p=q. The theorem is
`RHTower.chiCubicHyperbolicPrimeFullPacket_tendsto` in
`ChiCubicHyperbolicPrimeFullPacket.lean`, valid for every natural M and real N→∞.
Exact original off-diagonal cubic=full packet+entire tail is also proved.
All previous statements of pending full-packet formalization are superseded.

No assertion is made about the complement |(p-r)(q-r)|>Mr. In particular, convergence for every fixed M cannot be exchanged with M→∞ inside the full cubic without a separate uniform tail argument. The hard full BAG cubic remains open.

## Log

- 2026-10-06 — 17az: discovered this mechanism from the corpus's almost-all short-interval asymptotic and actual positive hyperbolic core. No Lean changes or claimed cancellation theorem yet. Search logs: `/tmp/bag-hyperbolic-complement-search-17az.json`, `/tmp/bag-prime-phase-cell-variance-search-17az.json`; rate search ongoing when this card was created.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeAveraging` | `chiCubicHyperbolicVonMangoldtAverage_eq`, `chiCubicHyperbolicVonMangoldtAverage_tendsto`, `chiCubicHyperbolicPrimePowerError_tendsto` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeCancellation` | `exists_chiCubicHyperbolicPrimeIntegralMass_bound`, `chiCubicHyperbolicPrimeIntegralMass_tendsto`, `chiCubicHyperbolicPrimeKernel_integral_tendsto`, `chiCubicHyperbolicPrimePacket_tendsto` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeDisplacement` | `chiCubicHyperbolicPrimeTrace_one`, `chiCubicHyperbolicVonMangoldtAverage_dilation`, `chiCubicHyperbolicVonMangoldtDisplacement_tendsto`, `chiCubicHyperbolicPrimePacket_integral_tendsto` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeEdges` | `exists_chiCubicHyperbolicPrimePairIntegral_all_bound` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeFullPacket` | `chiCubicHyperbolicPrimeFullPacket_eq`, `chiCubicHyperbolicPrimeFullPacket_tendsto`, `primeGaussianCubicOffDiagonal_eq_hyperbolic_add_tail` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeGapIntegrals` | `chiCubicPrimeGapPairs_sum`, `exists_chiCubicHyperbolicPrimeSmallGapMass_bound` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeHole` | `integrableOn_chiCubicHyperbolicPrimeHole`, `norm_chiCubicHyperbolicPrimeHoleIntegral_le`, `chiCubicHyperbolicPrimeHoleMass_tendsto` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeIntegral` | `integrableOn_chiCubicHyperbolicPrimePair`, `chiCubicHyperbolicPrimeKernel_integral_eq`, `chiCubicHyperbolicPrimePairIntegral_zero_of_inactive`, `norm_chiCubicHyperbolicPrimePairIntegral_le`, `chiCubicHyperbolicPrimePairIntegral_bulk_eq`, `exists_chiCubicHyperbolicPrimePairIntegral_bulk_bound` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeKernel` | `card_chiCubicHyperbolicIntegerPairs`, `norm_chiCubicHyperbolicPrimeAmplitude_le`, `chiCubicHyperbolicPrimeSupport_measurable`, `chiCubicHyperbolicPrimeAmplitude_continuousOn`, `integrableOn_chiCubicHyperbolicPrimeKernel`, `chiCubicHyperbolicPrimeKernel_nat`, `norm_chiCubicHyperbolicPrimeKernel_le`, `chiCubicHyperbolicPrimeDensityError_tendsto` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeMoments` | `exists_chiCubicPrimeGapCount_moment_bounds` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimePairs` | `exists_chiCubicPrimeGapCount_prefix_bound`, `exists_chiCubicPrimeGapCount_harmonic_bound` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimePeriods` | `chiCubicHyperbolicPrimeAmplitude_frozen_period` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeSampling` | `chiCubicHyperbolicPrimeKernel_sampling`, `chiCubicHyperbolicPrimeKernel_weighted_sampling`, `chiCubicHyperbolicPrimeKernel_shortWindow_sampling`, `chiCubicHyperbolicPrimeKernel_shortWindow_sampling_tendsto` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeTies` | `primeGaussianCubicMainEntry_norm_le_real`, `chiCubicHyperbolicPrimeTiePacket_tendsto` |
| `GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeVariation` | `exists_chiCubicHyperbolicPrimeAmplitude_lipschitz`, `exists_chiCubicHyperbolicPrimeKernel_variation`, `chiCubicHyperbolicPrimeKernel_variation`, `exists_chiCubicHyperbolicPrimeAmplitude_freeze` |
| `GaloisForLFunctions.RHTower.ChiCubicPrimeWindowLogRate` | `tendsto_logPow_volume_psi_short_shrinking`, `chiCubicPrimeWindowError_logRate` |
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain` | `exists_primeGaussianCubic_entry_error`, `primeProfileBand_card_log_le`, `exists_primeGaussianCubic_full_error`, `tendsto_primeGaussianCubic_normalized_error`, `primeGaussianCubicMain_eq_contractions`, `primeGaussianCubic_phase_recenter` |
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianHyperbolicCore` | `tendsto_primeGaussianHyperbolicConductor`, `exists_primeGaussianHyperbolicCore_card`, `exists_primeGaussianHyperbolicCore_physical_mass`, `primeGaussianHyperbolicCore_mem`, `primeGaussianNearWidth_pos`, `primeGaussianNearWidth_pow_four`, `tendsto_primeGaussianNearWidth`, `exists_primeGaussianNearPairs_mass`, `primeGaussianNearPairs_mem`, `exists_primeGaussianPolylogPairs_mass`, `primeGaussianPolylogPairs_mem` |
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianProgressionProfile` | `exists_primeGaussianScaledLogProfile_lipschitz`, `exists_primeGaussianProgressionProfile_power_log`, `exists_primeGaussianProgressionProfile_fourier_bound` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
