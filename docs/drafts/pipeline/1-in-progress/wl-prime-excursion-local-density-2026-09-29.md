# WL prime excursion local density

- **ID:** WL-PELD-20260929
- **Stage:** 1-in-progress
- **Type:** THEOREM candidate; stronger survivor of C14 population audit
- **Source:** Audited `WeilLagExcursionBlocks`; existing `Sieve/InghamUniformDetectorMellinEveryBaseThetaMass.eventually_routeT_detectorPacking_theta_mass_every_base`.
- **Statement candidate:** Unconditionally, RH holds, or for every M>=0 and cutoff K an integer k>=K has an entire high-lag side of radius `h=floor(k^(3/4))` whose number of actual primes exceeds `k^(3/4)/(32768*log(2k))`. Consequently an eventual upper bound at this rate on high-prime lag populations in both side windows, for one ceiling M, is an exact RH criterion.

## Plan
1. [ ] Current corpus/public novelty and all source axiom/API audits.
2. [x] Derive dependency-closed paper mechanism and explicit constants.
3. [ ] Prove eventual radius geometry and transfer actual theta mass to high-lag prime counts.
4. [ ] Prove closed population dichotomy and sparse-exception RH characterization.
5. [ ] Targeted artifacts, all-public axioms, final direct source, umbrella wiring and frontier/index/lint updates.

## Paper proof
The discovered existing source theorem supplies, for every alpha strictly between 701299/1000000 and 1, at every sufficiently large real z,
`theta(z+z^alpha/2)-theta(z)>z^alpha/16384`.
Apply it at alpha=3/4. This is already corpus knowledge, not a new contribution or an assumed short-interval PNT.

For sufficiently large integer k, let `x=k` and `h=floor(x^(3/4))`. Then `2h<=k`, `h>=x^(3/4)/2`, and `h^2<=k*sqrt(k)`. The first property follows from `x^(3/4)/x -> 0`; the latter two follow from the floor bounds and `x^(3/2)=x*sqrt(x)`.

If `a_k>M+1`, the newly audited excursion law gives either `[k-h,k]` or `[k,k+h]` entirely above M. Write that side as `[a,b]`. Its left endpoint satisfies `k/2<=a<=k`, its length is h, and b<=2k. Therefore `a^(3/4)/2<=k^(3/4)/2<=h`, so the existing source window based at a lies inside the high-lag side. Also `a^(3/4)>=k^(3/4)/2` since k<=2a and 2^(3/4)<=2. Monotonicity of theta gives
`theta(b)-theta(a)>k^(3/4)/32768`.

The actual theta difference equals the sum of log p over primes in the integer Ioc side. Each prime p<=b<=2k contributes at most log(2k). Hence the number of primes in that side is strictly larger than `k^(3/4)/(32768*log(2k))`; every such actual prime lag exceeds M.

Under failure of RH, the existing integer-lag upper dichotomy gives arbitrarily far central values above M+1: a finite prefix is bounded by its finite maximum, and the global unboundedness supplies a later witness. This proves the stated closed alternative. Conversely RH bounds every actual prime lag by the existing sharp ceiling, so with M=max(a_1,0) all high-prime counts vanish. Thus an eventual upper bound on both side populations at the stated rate is equivalent to RH. No such actual population upper estimate is proved here.

## Audit and log
- 2026-09-29: C14 first used only existence of one prime per short-gap tile, giving the weaker k^(1/25) population. New research found quantitative theta mass already proved first on detector grids, then at every real base by explicit packing. Exact source statements were read; this forces a new stronger conjecture, sent through this separate paper/novelty audit before Lean code. The theta source's transitive axioms and actual compiled API remain pending. C12 actual-prime mesh survivor is currently the sole owned foreground Lean check.
- 2026-09-29: Existing `CCMSharpPrimeWindowExcessEnergyGate` treats sparse exceptions of a different dyadic Lambda/sqrt window via global Dirichlet excess energy. Existing `PrimeLagGrowthExponent` gives individual large primes. Neither statement is this literal local cardinality law for entire high actual-lag sides. Universal public/training novelty remains unverified.
