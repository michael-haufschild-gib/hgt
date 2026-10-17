# Infinite-grid tail rigidity: facts and failures

## Scope and counting

Dedicated ledger for infinite-grid tail rigidity beyond Trap 5. Independent field research.
Target: 100 significant mathematical packages. Certified packages in this ledger: **6**.
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

## Certified package 4: full-span rigidity despite finite-copy interference

For `G(u)=sum_{j=0}^m c_j f(u-jS)`, compact C² common seed `f`, nonzero endpoint coefficients,
and separation `S>D+1` beyond its correlation radius, the extremal correlation packet has
exactly one contributing pair. Near `L=mS`,
`h_G(x)=c_0 c_m h_f(x-L)`; on `|x|<=1`, `h_G(x)=Q h_f(x)` with `Q=sum c_j²>0`.
These identities hold regardless of interior coefficient signs, zeros, and cancellations.

If `L>=2`, `h_f(0)>0`, and every logarithmic-grid sample of `G` vanishes, then `d(L)>0` and
`E(f),E(G)>=exp(-1/2)log(1/d(L))/4>=exp(-1/2)L/4`. In particular the full span cannot be
a grid node. The relevant scale is the total span, not adjacent separation. Common-seed
finite-train interference therefore cannot provide bounded-energy escape at diverging span.
This quantitative law is the positive survivor of the exact-span obstruction.

The final division-free endpoint `exists_copyTrain_infinite_grid_energy_barrier` takes a
compact C² source, derives its own support threshold, and proves
`exp(-1/2)L h_f(0)<=4J(f)` and `exp(-1/2)L h_G(0)<=4J(G)`, including zero-mass seeds.
Only the ceiling-node sample is needed by the stronger intermediate theorem. No analytic
interface or regularity constant is assumed. Unrelated packet shapes remain outside scope.

Certificates: `FiniteTranslationTrains.lean` (9 theorems) and
`FiniteCopyTailRigidity.lean` (6 theorems). Both passed direct leaf checks without diagnostics;
all 15 theorem dependency audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Both imports and all API entries are present. **Formal lint passed** on this package's final run.
Paper: `FiniteCopyTailRigidity.md`. Card:
`infinite-grid-finite-copy-trains-2026-10-17.md` in `3-formalized`.
Logs: `/tmp/infinite-grid-train-{algebra,rigidity,axioms,index,lint}.log`.
Finite aperiodic endpoint algebra is classical; count the connected full-span energy law once.

## Certified package 5: complete active-lag cancellation criterion

For a nonzero finite real coefficient vector and spacing `S>=2`, let
`A_k=sum_{j-i=k} c_i c_j`. There exists a smooth compact positive-mass common seed with
correlation radius at most `1/2` whose train has every logarithmic-grid zero if and only if
every active positive center `kS` (`1<=k<=m`, `A_k!=0`) is off-grid. Coefficients may have
arbitrary signs and zeros. Inactive interior lag packets cancel exactly and impose no grid
restriction. The constructed train is smooth, compact, and has positive origin mass.

The grouped exact identity is `h_G(x)=sum_{k=-m}^m A_k h_f(x-kS)`. Separation isolates the
entire packet: `h_G(x)=A_k h_f(x-kS)` for `|x-kS|<=1`. For any positive-mass compact C²
seed, correlation radius `D>=0`, and `S>D+1`, all-grid pinning forces, at each active center
`kS>=2`, `d(kS)>0` and `E(f),E(G)>=exp(-1/2)log(1/d(kS))/4`. Interior near-resonance can
therefore be more expensive than the extremal span. This strengthens the full-span law.

Sufficiency is constructive: choose a positive radius below every active nearest-grid distance
and at most `1/4`, then dilate the certified smooth bump until its correlation fits inside.
Nonpositive lag packets miss all positive grid nodes, inactive packets cancel, and active
packets miss the grid by the chosen radius. No seed-existence interface remains.
The finite symbol `B(c,S,beta)=sum c_j exp(beta*jS)` multiplies the actual source exponential
moment exactly. If `B(c,S,1/2)=0`, the same constructed train has exact polar balance.

Certificates: `FiniteTrainActiveLags.lean` (7 public theorems) and
`FiniteTrainGridClassification.lean` (5 public theorems, one private finite-radius helper).
Both leaves passed without diagnostics. All 12 public theorem dependency audits contain
only `propext`, `Classical.choice`, and `Quot.sound`; these audits include the private helper
transitively. Umbrella and generated API contain both modules and all public names.
Paper: `FiniteTrainActiveLagClassification.md`. Formalized card:
`infinite-grid-active-lag-classification-2026-10-17.md`.
Logs: `/tmp/infinite-grid-active-{algebra,classification,axioms,index,lint}.log`.
Global lint failed on eight concurrent foreign unwired modules, listed in the paper; neither
new module has a lint error. This classification and its quantitative survivor count once.

## Certified package 6: uniform matching cost in the minimum active distance

For nonzero coefficients and spacing `S>=2`, define
`delta(c,S)=min({1} union {d(kS):1<=k<=m,A_k!=0})`. This finite minimum is attained,
lies in `[0,1]`, and is positive exactly for compatible patterns. Empty active sets give one.
Every admissible compact C² seed with correlation radius `D>=0` and `S>D+1` satisfies
`E(seed),E(train)>=exp(-1/2)log(1/delta)/4`.

There is ONE constant `C` for every packet count, coefficient vector, and spacing `S>=2`
such that each compatible pattern has an actual smooth compact positive-mass radius-half
seed producing a smooth compact positive-mass all-grid train with
`exp(-1/2)log(1/delta)/4 <= E(train) <= C+log(1/delta)`.
If the finite half-exponential symbol vanishes, that same train has exact polar balance.
Thus the worst active grid resonance controls the growth order uniformly, without an extra
cost scale depending on packet count or coefficient magnitudes. No optimal leading constant
or assertion for independently shaped packets follows.

Key tool: if two compact C² positive-mass sources have equal normalized correlations on
`[0,a]`, `a>0`, their energies differ by at most `2 integral_a^infinity w`. Their singular
integrals agree locally, and each remaining normalized integral lies in that fixed interval.
Separated trains inherit the bound with `a=1`. A fixed smooth bump compressed to any radius
`0<rho<=1` has `E<=C0-log rho`; choosing `rho=delta/4` completes the uniform construction.

Certificates: `LocalCorrelationEnergyStability.lean` (4 theorems) and
`FiniteTrainUniformEnergy.lean` (10 theorems). Both passed direct leaf checks without
diagnostics; all 14 dependency audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Both imports and all 14 generated API entries are present.
Paper: `FiniteTrainUniformEnergy.md`; formalized card:
`infinite-grid-uniform-train-cost-2026-10-17.md`.
Logs: `/tmp/infinite-grid-uniform-{local,train,axioms,index,lint}.log`.
Global lint failed only on concurrent foreign `ProjectedHyperbolicGramControl` missing
umbrella reachability. Neither new module has a lint error. Count the connected uniform law once.

## Boundaries and next conjectures

- A shrinking mesh alone gives no uniform modulus for a varying family of sources.
- Fixed-source failure does not prove a positive infinite-grid polar energy premium.
- The general polar class is larger than the two-copy construction.
- Lean-certified: bounded normalized Levy energy rules out separated-copy escape
  uniformly for arbitrary changing sources once `T>D+1`.
- Open: tail rigidity for arbitrary source shapes, general polar tails, optimal linear coefficient,
  and whether infinite-grid polar/nonpolar infima differ.
- External parent audit includes Krein inequalities; no claim of exhaustive literature novelty.
- Adjacent concurrent module `AsymptoticTailCoercivityAndNyquistTrap5Closure.lean` has polar-mass
  bounds with a quadratic-collar constant `K`; its derivative-free inequality retains an `N`
  factor. Do not conflate those estimates with the present uniform logarithmic Levy modulus.

## Next exact conjecture

For arbitrary compact C² sources with every logarithmic-grid zero, conjecture the raw bound
`exp(-1/2) T h_f(T)^2 <= 8 h_f(0) J(f)` for `T>=2`, without any packet decomposition or
support-separation hypothesis. This would give uniform normalized tail decay of order
`sqrt(E/T)` for bounded-energy families with changing source shapes and supports.

Candidate mechanism: Krein's inequality compares `h_f(T)` with the zero at `ceil(exp T)`;
the squared difference is at most `2R` times the origin increment at its exponentially short
lag. The certified ceiling-lag energy bound controls that increment. A stronger global
logarithmic continuity modulus and a dyadic-window L² bound decaying as `1/log N` may follow.
These conclusions remain unproved and uncounted. Such slow unweighted decay alone would not
control the exponentially weighted polar moment; do not claim full polar-tail tightness.

Search: `/tmp/infinite-grid-general-tail-search.txt`, useful source-only hits, older-generation
coverage snapshot, semantic coverage unmeasured. Exact APIs:
`autocorr_krein_increment_sq_le`, `autocorr_logarithmicCeilLag_energy_bound`.
The existing `integral_autocorr_sq_dyadic_window_le_biScaleLevyEnergy` gives `2R J` with no
decay in `N`; the quadratic-collar theorem uses an additional regularity constant.
`bounded_levy_width_rigidity` assumes a nonpositive interval and is a different statement.
