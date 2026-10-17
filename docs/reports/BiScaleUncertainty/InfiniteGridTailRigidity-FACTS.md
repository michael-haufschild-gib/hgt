# Infinite-grid tail rigidity: facts and failures

## Scope and counting

Dedicated ledger for infinite-grid tail rigidity beyond Trap 5. Independent field research.
Target: 100 significant mathematical packages. Certified packages in this ledger: **3**.
Existing finite-grid results, standard parent inequalities, and helper lemmas do not count anew.

## Established inputs

- `DistantCopyPolarEnforcement.lean`: for `g(u)=f(u)-a f(u-T)`,
  `h_g(x)=(1+a²)h_f(x)-a(h_f(x-T)+h_f(x+T))`.
- For `a=exp(-T/2)`, the positive half-exponential source moment vanishes exactly.
- On bounded windows, distant copies preserve normalized correlations exactly; their normalized
  Levy energy cost tends to zero. These statements concern finite grids and unrestricted support.
- Compact continuous sources have compact continuous autocorrelations, positive at zero unless
  their origin energy vanishes.

## Certified package 1: single-copy detection and linear energy cost

At `n=ceil(exp T)`, the displacement `delta=log n-T` satisfies
`0<=delta<=exp(-T)`. Once `T` exceeds the autocorrelation support radius,
`h_g(log n)=-a h_f(delta)`. Hence a fixed source produces a negative sample for all large `T`.
If a varying source preserves that grid sample instead, `h_f(delta)=0` and its translation
square distance at `delta` equals twice its origin energy. Moreover
`exp(T/2) h_polarCopy(log n(T)) -> -h_f(0)` for every fixed compact continuous source.

For compact C² sources, the chord inequality and decreasing Levy weight give
`(R-h(delta)) integral_delta^b w <= 4 J(f)` for `0<delta<=b`.
Since `w(x)>=exp(-1/2)/x` on `(0,1]`, this yields
`exp(-1/2)(R-h(delta)) log(1/delta)<=4 J(f)`.
If `T>D+1` and a nonzero-copy coefficient preserves the detecting grid zero, then both
`J(f)/h_f(0)` and `J(copy)/h_copy(0)` are at least `exp(-1/2) T/4`.
The latter follows because local copy preservation also forces `h_copy(delta)=0`.
The stronger bound with `4 integral_0^b Delta(x)w(x) dx` also holds and is formalized.
For `a>=0`, the error-sensitive law is
`exp(-1/2) T (a R + h_copy(log n(T))) <= 4 a J(f)` for `T>D`.
See `InfiniteGridTailRigidity.md`, Theorems 1–5 and the final error-sensitive inequality.

Certificates: `InfiniteGridTailRigidity.lean` and `LogarithmicIncrementEnergy.lean`.
The endpoint `exists_subtractCopy_infinite_grid_energy_barrier` takes only a compact C² source
and derives its support radius; grid-sample preservation forces the stated energy cost.
Both leaves passed direct `lake --old env lean` audits; all 22 new theorems have only
`propext`, `Classical.choice`, `Quot.sound`. Both are in the umbrella and generated API.
Audit logs: `/tmp/infinite-grid-{energy-build,final-axioms,index}.log`.
Global lint failed only on three concurrent unwired modules (listed in the paper); do not
claim global green. No full builds, numerical experiments, new axioms, heartbeat overrides,
commits, or pushes were performed.

## Certified package 2: smooth infinite-grid polar recovery with linear cost

For `N>=ceil(exp 2)`, put `T_N=(log N+log(N+1))/2`. There is a single constant `C` and
an actual nonzero smooth compact source `k_N` for every such `N` whose canonical polar copy
`g_N=k_N-exp(-T_N/2)k_N(.-T_N)` has exact polar balance and satisfies
`h_gN(log n)=0` for every integer `n>=2`. Its normalized energy obeys
`exp(-1/2)T_N/4 <= E(g_N) <= C+T_N`. The centers reach arbitrarily large separations.
Thus the separated-copy obstruction has the correct growth order and an explicit positive
survivor. No optimal leading coefficient or general polar/nonpolar infimum comparison follows.

Construction: choose a concrete smooth compact seed, correlation radius `D>0`, and scale
`L_N=8(D+1)(N+1)`. Its compressed correlation support fits inside radius `1/(8(N+1))`.
Every grid node stays at least `1/(2(N+1))` from the midpoint. All three correlation packets
therefore miss the entire grid. Positive origin mass and the exact polar moment are derived.

Analytic input proved here: for a compact C² seed with correlation radius `D>0`,
`E(f(L .))<=A+log L` for `L>=D`, where `A=3MD/R+log(6/D)+pi` and the linear increment
constant `M` is derived from regularity. Beyond the compressed support, the normalized
integrand equals the Levy weight exactly. The radius-free estimate `A'+2log L` also holds.
The polar error constant scales exactly as `P(f(L .),D')=P(f,D')/L`.

Certificates: `LogarithmicCompressionEnergy.lean` and `InfiniteGridPolarRecovery.lean`.
Endpoint: `exists_smooth_infinite_grid_polar_recovery`; unbounded-center certificate:
`exists_arbitrarily_large_logarithmicMidpoint`. Both leaves passed direct Lean checks without
diagnostics. All 17 new theorems have only `propext`, `Classical.choice`, and `Quot.sound`.
Both modules are wired; all 17 declarations appear in the refreshed API index.
Paper: `InfiniteGridPolarRecovery.md`. Audit logs: `/tmp/infinite-grid-{compression-build,
recovery-build,recovery-axioms,recovery-index,recovery-lint}.log`.
Count this connected construction and estimate as one package, not 17 separate contributions.
Logarithmic scaling itself is classical; the novelty boundary remains the connected corpus result.
The final global lint run failed on six concurrent foreign modules missing umbrella reachability;
the paper records their names. Neither new module has a lint error. Repository-wide green is
not claimed.

## Certified package 3: exact center classification and nearest-grid energy law

For every `T>=2`, the explicit invariant
`d(T)=min(T-log(floor(exp T)), log(floor(exp T)+1)-T)` is the actual attained distance to
`{log n:n>=2}`. It satisfies `0<=d(T)<=exp(-T)<=1`, and is positive exactly off-grid.

Among nonzero smooth compact seeds with correlation radius at most `1/2`, a canonical polar
copy centered at `T` satisfies every logarithmic-grid zero for some seed if and only if `T`
is off-grid. At each off-grid center there is an actual such source with exact polar balance,
positive mass, and `exp(-1/2)log(1/d(T))/4 <= E(copy) <= C+log(1/d(T))`, using one constant
`C` for every center. Thus resonance with a grid node is a genuine singular boundary, not
merely a large-separation effect. At the exact node the class is empty; off-grid the positive
survivor is completely constructed.

The lower theorem is stronger: for any compact C² seed, any nonzero real coefficient `a`,
correlation radius `D>=0`, and `T>D+1`, `T>=2`, all-grid pinning of `f-a f(.-T)` forces
`d(T)>0` and the same logarithmic lower bound for both base and copy. The nearest sample
forces `h_f(d(T))=0`; local preservation transfers this zero to the copy. At zero distance
this would force origin mass zero, yielding the exact-node obstruction.

Upper construction: fix the certified smooth bump and radius `D`; use scale
`L=4(D+1)/d(T)` and correlation radius `d(T)/4`. All three correlation packets miss every
grid node. The support-aware compression law and polar-error scaling supply the uniform
constant. No seed existence, modulus, or grid admissibility is left as an analytic assumption
of the construction endpoint.

Certificates: `LogarithmicGridDistance.lean` (8 theorems) and
`InfiniteGridDistanceClassification.lean` (7 theorems). Main endpoints:
`exists_smooth_polar_source_at_off_grid_center`,
`exists_smooth_separated_polar_grid_source_iff`, and
`subtractCopy_infinite_grid_distance_energy`.
Both leaves passed without diagnostics; all 15 theorems passed the scratch axiom audit with
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella and generated API cover all 15.
Paper: `InfiniteGridDistanceClassification.md`; formalized card:
`infinite-grid-distance-classification-2026-10-17.md`.
Logs: `/tmp/infinite-grid-distance-{geometry,classification,axioms,index,lint}.log`.
Global lint failed on four concurrent foreign modules; neither new module has an error.
This complete classification is counted once. It does not classify arbitrary polar sources.

## Boundaries and next conjectures

- A shrinking mesh alone gives no uniform modulus for a varying family of sources.
- Fixed-source failure does not prove a positive infinite-grid polar energy premium.
- The general polar class is larger than the two-copy construction.
- Lean-certified: bounded normalized Levy energy rules out separated-copy escape
  uniformly for arbitrary changing sources once `T>D+1`.
- Open: multiple interfering translated packets, general polar tails, optimal linear coefficient,
  and whether infinite-grid polar/nonpolar infima differ.
- External parent audit includes Krein inequalities; no claim of exhaustive literature novelty.
- Adjacent concurrent module `AsymptoticTailCoercivityAndNyquistTrap5Closure.lean` has polar-mass
  bounds with a quadratic-collar constant `K`; its derivative-free inequality retains an `N`
  factor. Do not conflate those estimates with the present uniform logarithmic Levy modulus.

## Next exact conjecture

For a finite train of separated translates of one common seed, the extremal pair may detect
the entire support span even when interior pairs interfere. For equally spaced copies with
nonzero endpoint coefficients, the maximal difference has a unique contributing endpoint
pair. Its nearest grid sample should force the same short seed zero, giving energy cost at
least a constant times the full span and ruling out exact grid resonance. Local copy
preservation would transfer the zero to the complete train. This is unproved and uncounted.
Do not extrapolate to independently varying packet shapes: their extremal cross-correlation
need not equal the seed origin mass.

Next corpus search: `/tmp/infinite-grid-multicopy-search.txt`. Useful source-only hits include
`integral_finset_sum_shift_sq_eq`, `autocorr_sourceTranslate`, and the two-copy expansion.
The adjacent `OddMultiplierLeakageFamily` has a private six-packet expansion; inspect its
status before depending on it. Semantic coverage is unmeasured; verify exact APIs in Lean.
