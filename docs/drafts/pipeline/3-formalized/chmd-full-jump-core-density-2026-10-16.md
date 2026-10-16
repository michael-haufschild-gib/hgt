# CHMD full jump core density

Status: formalized. RH remains open. Global lint has unrelated umbrella-wiring failures listed below.

## Result

The closed span of actual compact C2 Doob tests equals the maximal theta-cosh /
complete archimedean-plus-prime difference graph: `compactCore_eq_top`.
The literal compact C2 tests themselves form a submodule and are dense:
`dense_compactTests`. Both theorems are unconditional.

The preceding graph construction established completeness, literal endpoint
differences, and constant ground-state classification only on the maximal
domain. The compact-core equality and even constant membership in that core
were unproved before this work. Primitive cusp escape rules out compactness of the source
projection, so compact embedding cannot justify this identification.

## Proof structure

1. Prove normal contractions act on the literal difference graph. Bounded
   truncations converge in graph norm by dominated convergence.
2. Establish finite second jump moment for the actual full edge measure.
   For primes, theta exponential decay and the complete Mangoldt series
   suffice; no finite prime truncation is substituted for the source.
3. Smooth cutoffs tend to one in graph norm. For bounded domain functions,
   multiplying by these cutoffs converges in graph norm. This places the
   genuine constant ground state in the compact-test completion.
4. Approximate bounded compactly supported domain functions by convolution.
   The archimedean singularity is handled locally using positive continuous
   theta weights and Jensen; large jumps have finite measure. Bounded graph
   approximants and strong source convergence suffice via weak closedness
   of the compact core. Every analytic step is now proved in the leaf chain.
5. Deduce maximal/core equality and record exactly what this resolves. This
   does not prove a primitive sign, a spectral gap, or RH.

## Corpus audit

Deep search: `Doob graph compact core maximal domain equality normal contraction
truncation mollification density full prime archimedean jump measure`, 120s,
cached index. Completed without partial results; inventory complete; compiler
metadata largely pending/stale and snapshot one generation behind. Candidate
applicability must be checked in this toolchain. Relevant existing sources:
`CHMDClosedJumpGraph`, `CHMDDoobSourceGraph`, `WeilPhiDoobDivisorEnergy`, and
the weak approximation pattern in `SuzukiLimitingLogClosedMarkov`.

## Verification / work log

- `CHMDFullJumpMoment`: full prime measure finite; full edge displacement L2.
  Leaf build passed. These are tools for localization, not the final contribution.
- `CHMDJumpGraphContractions`: actual normal contractions, bounded scalar
  truncation converging in graph norm. Leaf build passed.
- `CHMDCompactGraphCutoffs`: compact C2 cutoffs converge to the constant ground
  state; every constant belongs to the compact C2 completion; bounded domain
  functions have compact measurable graph approximants. Direct check and leaf
  build passed.
- `CHMDBoundedCompactDomain`: density of bounded compact measurable
  domain functions. Direct check and leaf build passed.
- `CHMDWeakCoreAdmission`: s-finiteness/separability and real weak extraction,
  then compact-core membership from graph-bounded approximants and strong source
  convergence. Leaf build passed. No compact embedding is used.
- `CHMDCompactStationaryJump`: compact-domain transfer to the entire stationary
  Levy norm. Direct check and leaf build passed.
- `CHMDGraphMollification`: normalized convolution, stationary energy contraction,
  uniform full graph bound, almost-everywhere convergence, and compact-core
  membership of bounded compact domain vectors. Leaf build passed.
- `CHMDFullJumpCoreDensity`: maximal/core equality and density of the literal
  compact C2 submodule. Leaf build passed.
- `/tmp/chmd_core_verified_names_20261016.lean`: 51 mathlib `have := @Name`
  probes with explicit universe zeros passed. Initial discovery probes retained
  temporarily for cleanup; never used as repository theorem declarations.
- Smooth-density mechanism: for a compact bounded domain function,
  positivity of theta on its compact support transfers small archimedean jumps
  to the stationary Levy jump norm. Large stationary jumps are controlled by
  ordinary L2 and integrability of the Levy tail. Scalar convolution contracts
  that stationary norm (corpus `HTGeometry/YoungConvolutionL2.lean`), giving
  uniformly graph-bounded smooth compact approximants. Source convergence plus
  weak closedness of the compact C2 core identify the maximal domain.
  This is proved in `CHMDGraphMollification` and `CHMDFullJumpCoreDensity`.
- One owned Lean process at a time; leaf builds only; final plain direct
  audits, axioms audit, umbrella wiring, index and authoritative lint required.
- Owned search scratch: `/tmp/chmd_graph_core_search_20261016.json`.
- Additional search: `/tmp/chmd_graph_smoothing_search_20261016.json`, completed,
  not partial; cached coverage snapshot. No existing applicable smooth jump-domain
  density theorem found. Existing Sobolev results require stronger derivatives.

## Paper closure of the smoothing step

Let v be bounded, compactly supported, measurable, and in the maximal graph.
It belongs to ordinary L2. For 0 < t < 1, a nonzero difference v(x)-v(x+t)
forces both endpoints into one fixed compact interval. Theta has a positive
minimum m there, so the stationary small-jump energy is at most m^-2 times
the actual archimedean energy. For t >= 1, the stationary difference square
is bounded by 2(v(x)^2+v(x+t)^2); the Levy tail is integrable. Thus the entire
stationary Levy difference energy of v is finite.

Convolve v with normalized smooth compact bumps of shrinking radius.
These functions are smooth and compactly supported, stay bounded by the
same M, and converge almost everywhere and in the finite theta-cosh L2
source space. Convolution commutes with each fixed displacement. Young's
L1-L2 theorem makes every stationary difference norm decrease. Fubini and
the positive Levy weight therefore bound stationary energy uniformly.
Global boundedness of theta transfers that bound to actual archimedean
energy; finite full-prime mass controls every prime edge together by 4M^2.
The smooth lifts have uniformly bounded graph norm.

The full graph is a separable real Hilbert space: both underlying measures
are s-finite on countably generated Borel spaces. Extract a weakly convergent
subsequence of the smooth lifts. The compact C2 core is weakly closed, and
strong source convergence identifies the weak limit with the original
literal graph vector by source injectivity. Hence every bounded compact
domain vector lies in the C2 core. Their already proved graph density yields
compactCore = top. The paper dependency chain and all eight leaf builds are complete.

## Final validation

- All eight `lake --old build <leaf>` builds passed; no umbrella build.
- All eight final plain `lake env lean <leaf>` audits passed, with empty logs.
- All 96 new declarations audited in a `/tmp` file: only `propext`,
  `Classical.choice`, and `Quot.sound`; no additional axioms.
- 51 mathlib name probes passed. All eight imports appear exactly once in the
  RHTower umbrella. Whitespace checks passed; audited source hashes unchanged.
- `scripts/formal_tools.py index` passed (13 changed, 0 removed).
- Authoritative `scripts/formal_tools.py lint` exited 1 solely for these 12
  other unwired modules; none is one of the eight new leaves:
  - RHTower/CHMDArchimedeanLevyTranslateForm
  - RHTower/CHMDDAlembertSechKernel
  - RHTower/CHMDLightConePrimeKernelDecomposition
  - RHTower/CHMDMasslessContinuationPieces
  - RHTower/CHMDMasslessZeroWaveExplicitFormula
  - RHTower/PaperThetaBranchAbsoluteContinuity
  - RHTower/PaperThetaConfluentCut
  - RHTower/PaperThetaConfluentQuantile
  - RHTower/PaperThetaParameterAnalytic
  - RHTower/PaperThetaParameterTraces
  - RHTower/PaperThetaParameterVariation
  - HTGeometry/KleinGordonLightConeBesselKernel
  Concurrent work was preserved. The earlier six Deninger wiring failures did
  not appear in this final lint run. No global lint pass is claimed.
- All 36 owned scratch files removed; absence verified. All owned Lean, search,
  indexing, and lint processes reached terminal status. No heartbeat increases,
  numerical experiments, web searches, old research Markdown reads, or commits.

## Exact frontier change

There is no maximal-domain versus compact-C2-core gap for the literal complete
CHMD jump measure. The constant zero-jump ground state belongs to that core;
bounded scalar truncation and spatial localization retain the full graph norm;
normal contractions retain actual edge differences. The positive jump norm and
source norm contract separately, not an asserted signed primitive energy.

Primitive nonnegativity, a selfadjoint generator theorem, and RH are not proved
here. Prior primitive cusp escape and noncompactness remain in force. The next
obstacle is the sign at the critical primitive boundary, now on an identified
domain rather than an assumed completion.
