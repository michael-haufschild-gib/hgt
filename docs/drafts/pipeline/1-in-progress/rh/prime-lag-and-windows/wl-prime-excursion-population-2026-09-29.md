# WL prime excursion population

- **ID:** WL-PEP-20260929
- **Stage:** 1-in-progress
- **Type:** CONJECTURE candidate; source producer obstruction
- **Source:** C13 upper-excursion block candidate, actual 71/100 every-base prime supply, corpus integer-lag dichotomy and prime-lag growth law.
- **Statement candidate:** Under failure of RH, each fixed upper ceiling is exceeded by all prime lags in arbitrarily far one-sided intervals on the k^(3/4) scale. Such intervals contain a number of primes growing at least on the k^(1/25) scale, from 3/4-71/100=1/25. Therefore exceptional high prime lags cannot be confined to locally fewer primes than this scale.

## Plan
1. [ ] Audit current corpus/public literature for positive prime-excursion population laws.
2. [ ] Finish exact quantitative statement and dependency-closed paper proof, including floor/boundary constants and tail recurrence.
3. [ ] Prove any missing finite prime-window cardinality lemma from existing supply; no prime tables or numerical jobs.
4. [ ] Formalize exact survivor only after C13 and source/cardinality audits.

## Paper mechanism under audit
Failure of RH gives unbounded actual upper integer lags, hence arbitrarily far central values above M+1 after accounting for the finite prefix. C13 would force a full high-lag side of radius h with h^2<=k*sqrt(k) and 2h<=k. Take h proportional to k^(3/4). Cover this side by disjoint real intervals of length a fixed multiple of k^(71/100). Existing every-base supply gives one distinct prime per interval. All those actual prime lags exceed M. The number of disjoint intervals is proportional to k^(1/25).

No uniform low-lag density is known or assumed. That opposite arithmetic statement would be a producer; this candidate instead classifies how any RH failure must populate local prime data. Exact constants, endpoint allocation and universal novelty remain unverified.

An exact schedule for the paper audit is `h=floor(k^(3/4)/4)` and `N=floor(k^(1/25)/16)`. Once `k^(3/4)>=8`, `h>=k^(3/4)/8`; always for k>=1, `2h<=k` and `h^2<=k*sqrt(k)`. The common prime-supply tile width `D=(2k)^(71/100)` is at most `2*k^(71/100)`. Hence `N*D<=k^(3/4)/8<=h`. Tile either high-lag side by N disjoint intervals of width D; all bases lie between k/2 and 2k. Actual supply gives a distinct prime in each tile. Thus the proposed exact lower population is N in one of the two Ioc side windows. Non-RH upper unboundedness beyond any finite prefix supplies arbitrarily far central spikes, completing the paper mechanism. The finite cardinality proof and asymptotic floor conditions still need formal/source audits before claiming the exact capstone.

The intended closed capstone is an unconditional dichotomy: RH, or for every M>=0 and every cutoff K, some k>=K has one of the two specified side windows entirely above M in actual lag values, with at least `floor(k^(1/25)/16)` actual primes. Source prerequisites are already unconditional; no new lag-density premise enters this dichotomy. An opposite eventual upper bound on high-prime populations in both windows would then be an explicit RH producer target. That opposite bound is not proved.

## Log
- 2026-09-29: Recorded next candidate before code. Research searches `/tmp/wl-prime-excursion-count-search-20260929.json` and `/tmp/wl-hoheisel-cardinality-search-20260929.json` running. Corpus `PrimeLagGrowthExponent` already proves arbitrarily far prime values exceeding M+p^a; that existing individual-prime statement must not be recounted as novel. The proposed novelty is an entire positive block and its local population, contingent on exact audit.
- 2026-09-29: Both hybrid searches completed with full indexed-inventory snapshot and substantial pending compiler coverage. Inspected `Sieve/ShortIntervalPrimeCount`: its quantitative count requires relative width above a classical PNT error, so it does not supply k^(3/4) window counts. `RetainedPrimeWindowSupply` gives fixed-ratio windows, also different. Inspected `CCMSharpPrimeWindowExcessEnergyGate` sparse-exception definitions: these control the distinct dyadic sum `sum_(n/2<j<=n) Lambda(j)/sqrt(j)` via Dirichlet excess energy, not a block of all actual integer/prime lag values. A guessed adjacent source filename was wrong; use actual `rg` definition hits rather than invented filenames. No new source premise inferred from these neighboring results.
- 2026-09-29: Complete finite tile-count paper proof: choose one prime in each interval `(a+jD,a+(j+1)D]`; every chosen point is below 2k, so every-base supply fits within width D. Distinct tiles force distinct primes. Inject `Fin N` into the actual finite prime window to prove its cardinality bound. Scratch `/tmp/wl-prime-supply-count.lean` contains this proof and explicit API checks, pending its first Lean run. C13 both propagation laws passed scratch, production artifact audit running; C11 finite signed means fully source/axiom audited. The prime mesh survivor `/tmp/wl-prime-quadratic-mesh.lean` also remains pending, rather than abandoned as a failed novelty endpoint.
