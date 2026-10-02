# Route PM: growing cofactor packets retain a coherent prime head

- **ID:** pm-growing-cofactor-prime-head
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); follow-up conjectures remain open
- **Source:** `PMPowerDampedMobiusRamanujanAbsolute`, `PMPairedRamanujanGram`, actual Ramanujan weights.
- **Goal:** identify the cancellation that a small-damping natural-cutoff energy proof must supply. This does not assert RH or an upper energy bound.

## Paper argument

Write a(q) for the actual damped Ramanujan weight, P_q(N) for its cumulative primitive, alpha for the positive divisor density, and b_p=p^(1+epsilon)-1. Include the cofactor r=1. Define

    A(R,N) = sum_(1 <= r <= R) a(r) P_r(N),
    B(p,R,N) = sum_(1 <= r <= R) a(pr) P_pr(N).

For epsilon>0 choose max(0,1-epsilon)<a<1. The audited uniform prefix estimate gives

    |A(R,N)-alpha N| <= C_epsilon N^a

for every R>=1. Hence there is N0 independent of R such that Re A(R,N)>=alpha N/2 for N>=N0.

If p is prime, R<p and N<p, every cofactor is coprime to p. The exact primitive recursion gives P_pr(N)=-P_r(N), and the actual weight recursion gives a(pr)=-a(r)/b_p. Therefore

    B(p,R,N) = A(R,N)/b_p.

This proves a uniform coherent head even when all allowed cofactors grow with p. It strengthens fixed-cofactor resonance: grouping every cofactor of a large prime does not cancel this head.

For integer P>=2, use the actual denominator cutoff P^2 and primes P<p<=2P, with R_p=floor(P^2/p). Then 1<=R_p<p. Every represented denominator lies below P^2, and distinct primes in this band cannot represent the same denominator. The resulting literal sector L(P,N) satisfies

    Re L(P,N) >= alpha N H(P)/2  (N0<=N<P),
    H(P) = sum_(P<p<=2P) 1/b_p.

Choose K=max(N0,1) and P>=2K. For each K<=N<P, the original energy weight gives

    |L(P,N)|^2/[N(N+1)] >= alpha^2 H(P)^2/8.

There are P-K>=P/2 such integers. Hence the sector energy over 1<=N<P is at least alpha^2 P H(P)^2/16.

The existing unconditional theorem `DeletionPrimePacket.upperPrime_card_eventually_lower` gives at least X/(32768 log X) primes in (X/2,X]. At X=2P and since b_p<=(2P)^(1+epsilon),

    H(P) >= (2P)^(-epsilon)/(32768 log(2P))

eventually. Thus the sector energy is bounded below by

    [alpha^2/(32*32768^2)] * (2P)^(1-2epsilon)/log^2(2P),

which tends to infinity for 0<epsilon<1/2. The paper dependencies and the complete Lean proof are closed. The constants only witness divergence and are not optimization targets.

## Frontier consequence and next conjecture

The full natural-cutoff energy includes the complementary denominator sector and every mixed term. No lower bound for an extracted sector transfers to the full energy. The proposed cancellation must act between large-prime sectors and their complement, rather than inside each growing cofactor packet. Next attack: identify an exact complementary-sector subtraction that removes the coherent head while preserving the natural cutoff.

### Closed follow-up: actual relative cancellation on the moving head

For fixed 0<epsilon<1/2, the complete natural prefix at cutoff P^2 has energy on 1<=N<P that is little-o of the sector energy. The literal complementary sector has energy ratio tending to one and normalized mixed energy tending to minus one. This is now proved and audited in `PMRamanujanComplementaryCancellation.lean`; see `pm-complementary-prime-sector-cancellation.md` for its exact source estimates, paper argument and audit. The proof retains a positive-power upper bound for the total source, so global small-damping admission remains open.

### Further source profile to audit

The general prime recursion, without N<p, gives

    b_p B(p,R,N) = A(R,N) - p A(R,floor(N/p)).

At N=pK the density terms cancel exactly. With R=p-1,

    (b_p/p) B(p,p-1,pK) = Z_(p-2)(pK)/p - Z_(p-2)(K).

The first term tends to zero by the cutoff-uniform sublinear bound; the second tends to the actual centered divisor prefix by `tendsto_pmPowerDampedRamanujanCumulativePrefix`. Thus the expected rescaled packet profile is minus the original PM source, not a new decaying cofactor error. This is a further paper candidate to audit and formalize. It suggests that a cofactor-group norm argument risks reproducing the original admission problem; no energy conclusion follows from pointwise convergence alone.

## Log

- 2026-10-02: Corpus searches 119--121 checked candidates and source arguments; search 120 complete at generation 1186897, search 121 complete at 1186923. Source/compiler freshness remains mixed; applicability will be checked in Lean. No numerical experiment or new axiom. Exact packet identity and uniform head selected for formalization; energy divergence remains pending its prime-band dependency.
- 2026-10-02: Prime-band dependency located in `EulerDeletionWeightedPrimeCancellation.lean:120`; proof uses the corpus's unconditional theta-window lower bound. Full packet, literal cutoff membership, no-duplicate property, anchored-energy lower bound, and divergence proof drafted in scratch. First Lean pass identified local sign/name errors, now repaired; no new theorem is claimed audited yet.

## No-go scope and positive survivor

- **Rejected claim:** a uniform anchored-energy budget for the selected large-prime sector, including all its allowed cofactors, at 0<epsilon<1/2.
- **Positive survivor:** exact actual packet identity, a head lower bound uniform over growing cofactor cutoffs, literal natural-cutoff membership and uniqueness, and divergence of the original anchored sector energy.
- **New insight:** cofactor aggregation preserves this coherent contribution. The full source requires signed interaction with the complementary denominator sector. Sector divergence alone says nothing about the full source's admission or RH.
- **Status:** paper proof and eleven public Lean declarations audited. No route-PM retirement. Relative cancellation is now formalized; the source-reproduction follow-up remains a separate open formalization task.

## Lean audit — 2026-10-02

Module: `formal/GaloisForLFunctions/RHTower/PMRamanujanGrowingCofactorHead.lean`.
Main theorem: `RHTower.tendsto_pmRamanujanLargePrimeSectorEnergy_atTop`.

- `lake --old build GaloisForLFunctions.RHTower.PMRamanujanGrowingCofactorHead`: exit 0; only the new leaf reported built, existing dependency diagnostics replayed.
- All ten public declarations: `/tmp` `#print axioms` audit exit 0; only `propext`, `Classical.choice`, `Quot.sound`.
- Follow-up: exported the existing quantitative mass lower bound as `pmRamanujanLargePrimeMass_eventually_lower`, with unchanged proof, for the actual complementary energy comparison. Targeted old-mode rebuild and final actual-file audit passed. The new name's `/tmp` axiom audit also passed with only the same standard axioms, bringing the public declaration count to eleven.
- `lake env lean GaloisForLFunctions/RHTower/PMRamanujanGrowingCofactorHead.lean`: exit 0, empty output.
- Exactly one import added to `GaloisForLFunctions/RHTower.lean`; no umbrella build.
- `scripts/formal_tools.py lint`: exit 1 on eleven unrelated missing umbrella imports: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ThetaRadialSourceCurvature, ZetaZeroDensityPowerSaving. No finding for the new module and no forbidden proof construct reported.
- No new axiom, conjectural RH premise, heartbeat override, numerical experiment, full build, or subagent. Owned scratch files removed after recording these results.
