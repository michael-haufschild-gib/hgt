# Sharp asymptotic constant for the physical selected Fermi trace

- **ID:** thim-sharp-physical-fermi-asymptotic
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `thim-full-trace-valuation-depth-stability.md`
- **Statement:** For the original pronic energies, the optimal inverse constant
  is asymptotic to `4/pi^2 * (log_2 N)^2`, both for arbitrary real coefficients
  and for nonnegative coefficients.

## Exact target and status

Write `P_N(c)=sieveTotalPronicEnergy N c` and
`Q_N(c)=fermiSelectedTotalPronicEnergy N c`. For `N>=2`, define

`K_N = sup {P_N(c)/Q_N(c) : Q_N(c)>0}`,

and define `K_N^+` by additionally requiring every coefficient nonnegative.
The established depth upper bound makes both suprema finite. The precise first
target is

`lim_(r->infinity) K_(2^r)/r^2 = lim_(r->infinity) K_(2^r)^+/r^2 = 4/pi^2`.

Monotonicity in the horizon also gives the general-horizon version. All four
limits are now unconditional Lean theorems in `FermiPhysicalOptimalConstants.lean`.
The source/olean check, six-public-declaration import axiom audit, umbrella
wiring, index regeneration, and generated-file lint gate passed. Every audited
declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
The connected native package is programme contribution C1; its classical path
ingredients and supporting leaves are not counted separately. Earlier progress
entries below are historical and superseded by this checkpoint.

## Corpus audit before implementation

- Deep query `finite interval sharp discrete Poincare Neumann Dirichlet sine
  constant sum consecutive differences operator norm`: completed, with 20
  candidate statements, 20 source arguments and its proposed ingredient set
  inspected. Its suggested sine-sum/spectral-norm ingredients did not prove the
  target. `Hardy matrix norm` returned four irrelevant hits; `pronic optimal
  constant` and `Fermi pronic sharp` returned none. These negatives were not
  treated as exhaustive absence.
- Follow-up `Poincare discrete` found the existing THIM path variance identity;
  source inspection also found `sq_sub_le_length_mul_sum_range_addDiff_sq` in
  `ArithmeticUncertaintyAndSpikeCancellation.lean`. This is the ordinary
  telescoping/Cauchy bound, not the sharp mixed-boundary constant.
- A second deep query about bounded runs of dyadic admissions found
  `BiScaleUncertainty.SobolevShear.finiteGrid_run_le`. Exact follow-up
  `finiteGridRunLength` returned 26 hits, all inspected across both pages.
  Source/reference inspection then found the previously missed existing
  `finiteGridExtension_stability`, `finiteGridExtension_sharp`,
  `pathSineValue_adjacent`, and
  `RHTower.norm_inner_nilpotent_contraction_le_sine`.
- Sources and compiled artifacts for `FiniteGridTraceStability`,
  `FiniteGridTraceSharpness`, and `FinitePathSinePackets` were inspected.
  The `/tmp` interface probe passed, as did axiom inspection of the stability,
  sharpness, and generic nilpotent sine theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`. An initial `have := @...` probe
  needed an explicit universe on the generic nilpotent theorem; this was a
  probe elaboration error, not a failure of the existing theorem.
- The second deep search inventoried 74,258/74,258 files, but compiler coverage
  still had 57,023 pending, 2,658 stale and 2,654 unavailable files. It returned
  `partial=false` for its retrieval stages, not complete compiler verification.
- The generic longest-run/Poincare mechanism also has external prior art:
  Lenz--Stollmann--Stolz, *An uncertainty principle and lower bounds for the
  Dirichlet Laplacian on graphs*, Theorem 3.12,
  https://arxiv.org/pdf/1606.07476. Its relatively dense Dirichlet-set estimate
  is related background, not a theorem about the selected Fermi/pronic operator.

## Native work still needed

The existing sine theorem must be applied with the correct free left boundary,
then transported through the actual pronic weights and the arithmetic terminal
tail. An explicit nonnegative divisor family must attain the leading constant.
Replacing this work with an abstract path theorem or the coefficient-space 3/2
theorem would prove a different statement.

## Proof mechanism

Every positive even integer is uniquely `2^k*u`, with `k>=1` and `u` odd.
For fixed `u`, put

`x_k=s_N(2^k*u)/2^k`,
`y_k=J_N(2^(k+1)*u)/2^(k+1)=x_k-x_(k+1)`.

The exact physical weights are
`w_(k,u)=1/(u*(u+2^(-k)))`. Thus even sieve energy uses `x_k^2*w_(k,u)`
and selected even energy uses `y_k^2*w_(k+1,u)`. Odd energy is already observed
exactly. Horizon saturation gives `x_(R+j)=2^(-j)*x_R` after
`R=log_2(N)+1`.

1. Reflect a length-`n` sequence across its free endpoint into a length-`2n`
   Dirichlet path. The existing sine bound gives the tail-summation matrix norm
   `U_n=1/(2*sin(pi/(4*n+2)))`, hence `U_n/n -> 2/pi`.
2. On levels `K..R`, center at the actual terminal value `x_(R+1)=y_R`.
   The mixed-boundary inequality and the identity
   `(f-M*t)^2=(M+1)*f^2+M*(M+1)*t^2-M*(f+t)^2` give a bound with leading
   factor `(1+1/M)/lambda_n`, where `n=R-K+1` and `M>=1` is an auxiliary
   integer. The remaining cost is linear in `n` for fixed `M`.
3. For fixed `K`, pronic weights on those levels differ from `1/u^2` by a
   relative factor at most `1+2^(-(K+1))`. The discarded first `K-1` levels cost
   only `O(K*R+K^2)` by the exact recurrence and Cauchy. First let `R` grow,
   then let `K` and `M` grow. This gives the upper leading constant `4/pi^2`.
4. For the lower bound at horizon `2^r`, take
   `theta=pi/(2*r+1)`, `x_k=cos((k-1/2)*theta)` for `1<=k<=r`, and set
   `c(2)=2*x_1`,
   `c(2^k)=2^k*x_k-2^(k-1)*x_(k-1)` for `2<=k<=r`, zero elsewhere.
   The sine recurrence gives nonnegative coefficients, including the last one.
   After level `r`, extend `x` geometrically by horizon saturation.
5. Set `H=sum_(u odd positive) 1/u^2`. It is finite and positive and need not
   be evaluated. For `S_r=sum_(k=1)^r x_k^2`, weight comparison gives
   `P>=H*(S_r-1)` and `Q<=H*(2-2*cos(theta))*S_r`, with `S_r -> infinity`.
   Since `r^2*(2-2*cos(theta))->pi^2/4`, the same lower constant follows on the
   nonnegative coefficient cone.

## Dependency-closed paper proof [PROVED HERE]

All sums in the following energy decompositions have nonnegative summands.
The established finite-horizon summability and the comparisons below justify
their rearrangement into odd rays. The homogeneous odd mass `H` is finite by
comparison with the inverse-square series and positive because its first term
is one. No evaluation of that series is used.

### 1. The finite mixed-boundary inequality

For a real vector `z_1,...,z_n`, put `z_(n+1)=0`. Reflect it into the Dirichlet
path vector

`v=(z_n,...,z_1,z_1,...,z_n)`.

Its mass is `2*sum z_k^2` and its Dirichlet difference energy, including both
zero endpoint values, is `2*sum (z_k-z_(k+1))^2`. The nilpotent contraction
sine bound applied to the length-`2n` shift gives

`lambda_n * sum z_k^2 <= sum (z_k-z_(k+1))^2`,
`lambda_n=2-2*cos(pi/(2n+1))=4*sin(pi/(4n+2))^2`.

Indeed the shift has norm at most one and its `2n`-th power is zero; expand the
Dirichlet energy as twice the mass minus twice adjacent correlation. This is
exactly the checked generic sine theorem. The symmetric sine vector attains
the bound. Therefore the tail-summation matrix has norm
`U_n=lambda_n^(-1/2)`, and `U_n/n -> 2/pi` by `sin(t)/t -> 1`.

### 2. Uniform upper estimate in the actual weights

Fix an integer `K>=1` and take `R>=K`. On one odd ray, terminal saturation gives
`x_R=2*y_R` and, for `K<=k<=R`,

`x_k=sum_(j=k)^(R-1) y_j + 2*y_R`.

Set `t=x_(R+1)=y_R` and `n=R-K+1`. The mixed-boundary inequality applied to
`x_K-t,...,x_R-t`, whose next value is zero, gives

`lambda_n * sum_(k=K)^R (x_k-t)^2 <= sum_(j=K)^R y_j^2`.

For any integer `M>=1`, the nonnegative square `(f-M*t)^2` proves
`M*(f+t)^2 <= (M+1)*f^2+M*(M+1)*t^2`. Sum this identity with `f=x_k-t`
and use `t^2=y_R^2<=sum_(j=K)^R y_j^2`. Beyond `R`, the geometric tail has
mass `x_R^2/3=4*y_R^2/3`. Since `lambda_n>0` for `n>=1`, the result is

`sum_(k>=K) x_k^2 <= B_(n,M) * sum_(j=K)^R y_j^2`,
`B_(n,M)=(M+1)/(M*lambda_n)+(M+1)*n+4/3`.

For all odd `u>=1`,

`w_(k,u)<=1/u^2`,
`w_(j+1,u)>=1/((1+2^(-(K+1)))*u^2)` for `j>=K`,
`w_(j+1,u)>=4/(5*u^2)` for every `j>=1`.

For the head, the recurrence and Cauchy give

`sum_(k<K) x_k^2 <= 2*(K-1)*x_K^2
  +2*(K-1)^2*sum_(j<K) y_j^2`,
`x_K^2 <= (R-K+4)*sum_(j=K)^R y_j^2`.

Multiply these inequalities by `1/u^2`, sum over all odd rays, and use the
three weight bounds. If `P_even,Q_even` denote the even parts, the result is

`P_even <= A_(R,K,M)*Q_even`,

`A_(R,K,M)=(1+2^(-(K+1)))*B_(R-K+1,M)
  +(5/2)*((K-1)*(R+4)+(K-1)^2)`.

The coefficient is greater than one, so `P_odd=Q_odd` yields the same bound
for the complete energies. This estimate is uniform in all coefficients and
odd rays. At `N=2^r`, take `R=r+1`. For each fixed `K,M>=1`,

`A_(r+1,K,M)/r^2 -> (1+2^(-(K+1)))*(1+1/M)*4/pi^2`.

Hence the limsup of `K_(2^r)/r^2` is at most this number for every `K,M`.
Letting `K` and `M` grow proves the upper bound `4/pi^2` without interchanging a
coefficient supremum with a limit.

### 3. Nonnegative arithmetic extremizing family

Use the cosine profile and coefficients stated above. Write `x_(r+1)=0`.
For `2<=k<=r`, the sine recurrence gives

`2*x_k-x_(k-1)=2*(1-cos(theta))*x_k+x_(k+1)>=0`.

Together with `x_1>0`, this proves every coefficient nonnegative. Direct
telescoping of the power-of-two divisor coefficients gives the stated profile
on every odd ray through level `r`, followed by its geometric continuation.
The odd sieve and selected odd trace vanish identically.

The reflected sine eigenvector gives the exact finite energy identity

`sum_(k=1)^r (x_k-x_(k+1))^2=lambda_r*S_r`.

Replacing the zero terminal value by geometric continuation replaces its last
energy term `x_r^2` by `x_r^2/3`. Therefore the complete homogeneous selected
energy is exactly `lambda_r*S_r-(2/3)*x_r^2`, and is positive. Since

`(1-2^(-k))*H <= sum_(u odd) w_(k,u) <= H`,

and `0<=x_k<=1`, the actual energies satisfy

`P>=H*(S_r-1)`, `0<Q<=H*lambda_r*S_r`.

For all sufficiently large `r`, at least `floor(r/2)` profile entries are at
least `cos(pi/4)`, so `S_r>=r/4-1/2` and `S_r` tends to infinity. Thus

`K_(2^r)^+ >= (1-1/S_r)/lambda_r`.

An exact replacement for that crude mass estimate follows from the existing
`HTGeometry.sum_cos_odd`. For `r>0`, `sin(theta)>0` and
`2*r*theta=pi-theta`, so
`sum_(j<r) cos((2*j+1)*theta)=1/2`. Applying
`cos(t)^2=(1+cos(2*t))/2` gives `S_r=(2*r+1)/4`.
This classical identity is reused as an auxiliary fact, not counted as a
contribution.

The same comparison can be summed ray by ray, avoiding a separate evaluation
or summation lemma for `H`. On each positive odd ray `b`,
`P_b >= (S_r-1)/b^2` and `Q_b <= lambda_r*S_r/b^2`. For `r>=2`, both
coefficients are nonnegative, hence
`(S_r-1)*Q_b <= lambda_r*S_r*P_b`. Summability and the exact physical ray
decompositions give the global inequality. Positive total sieve energy follows
from its first even sample; the existing complete-trace inverse bound then
forces positive selected energy.

The elementary sine limit gives `r^2*lambda_r -> pi^2/4`. This proves the
matching lower bound on the nonnegative cone. The inclusions
`K_(2^r)^+<=K_(2^r)` and the general upper estimate prove both claimed limits.

### 4. All horizons and supremum well-posedness

For every `N>=2`, a single nonzero coefficient at `d=2` gives positive selected
energy. The previously verified depth upper bound bounds all ratios, so both
suprema exist as finite real numbers. If `N<=M`, extend any coefficient vector
through `N` by zero on `N<d<=M`; its two energies are unchanged and
nonnegativity is preserved. Both optimal constants are therefore nondecreasing.
For `2^r<=N<2^(r+1)`, bracket them by their values at those two powers.
Dividing by `(log_2 N)^2` and using `(r+1)/r -> 1` proves the general-horizon
asymptotic, with the same constant.

## Gates

- [x] Precise conjecture and prior-work audit.
- [x] Complete paper audit of series rearrangements, boundary factors, uniform
  upper bound, nonnegative construction, and both limiting passages.
- [ ] Exact unconditional Lean statements, source and public-axiom checks.
- [ ] Umbrella wiring, generated index and formal lint.
- [ ] Significance and external novelty qualification for the connected package.

## Log

- 2026-10-19 — Recorded after corpus follow-ups recovered existing sharp sine
  machinery that the initial broad deep query missed. No new Lean file yet.
- 2026-10-19 — Completed the paper proof, including the exact geometric-tail
  correction, a uniform upper estimate before taking the supremum, and a
  nonnegative extremizing family. Moved to fully proven; Lean and novelty gates
  remain open. This is a refinement of the same connected observability package.
- 2026-10-19 — The private mixed-boundary reflection helper passed a `/tmp`
  source and axiom check. New leaf `FermiMixedBoundaryRayStability.lean` passed
  its second source audit; its normalized jump identity, terminal-centered
  sine inequality, half-decay step and terminal observation identity are
  ingredients, not the asymptotic capstone. The first audit found a missing
  natural multiplication reassociation and a missing section terminator; both
  were corrected. Two sequencing warnings were then removed; the final source
  audit passed without diagnostics and produced the compiled artifact. The leaf
  is wired; its six-public-declaration axiom audit and index regeneration passed.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur. Global generated
  lint passed. A second `/tmp` scratch passed source verification of the odd-ray
  bijection; its infinite-sum API probes also passed.
  Additional corpus checks found the existing finite odd-fibre grouping in
  `BiScaleUncertainty/SignedDyadicCollarPartition.lean`; it groups logarithmic
  nodes and does not directly provide this infinite pronic reindexing.
- 2026-10-19 — The odd-ray bijection and its complete-series reindexing passed
  `/tmp` source and standard-axiom checks. Ninth leaf
  `FermiPronicRayDecomposition.lean` now states exact decompositions of both
  complete physical energies using their actual next-level pronic weights.
  The first source check caught two missing parentheses in additive `tsum`
  bodies; corrected. The second source check passed without diagnostics and
  produced its compiled artifact. The leaf is wired; all three public axiom
  audits, index regeneration, and global lint passed. No asymptotic theorem
  or additional contribution is claimed from these ingredients.
- 2026-10-19 — Follow-up deep searches for geometric terminal chains and finite
  Cauchy–Schwarz were inspected across all returned candidates, source arguments,
  and proposed ingredient sets. The geometric-tail proposals did not supply a
  Fermi estimate; the underlying mathlib geometric-series API is applicable.
  The finite-sum search recovered both mathlib's
  `sq_sum_le_card_mul_sum_sq` and the existing BiScale theorem of the same short
  name, after a filtered lexical query had returned no hits. Source inspection
  also confirmed `Finset.sum_mul_sq_le_sq_mul_sq` and the generated telescoping
  and series-splitting APIs. Empty filtered results are not absence evidence.
  Retrieval finished (`partial=false`), but compiler coverage still included
  57,026 pending, 2,658 stale, and 2,654 unavailable files.
- 2026-10-19 — Scratch proofs of exact physical ray weight comparisons,
  monotonicity, the terminal square penalty, geometric tail mass, and the
  complete-ray sine bound passed with standard axioms. New leaf
  `FermiPronicRayWeightAndTailControl.lean` contains these ingredients; its
  source check, all nine public axiom audits, and index regeneration passed.
  The leaf is wired; global generated lint passed. The global physical bound, matching nonnegative
  packet, and asymptotic limit remain unformalized.
- 2026-10-19 — The unfiltered square-sum lexical search returned 36 declarations;
  both pages were inspected. The finite-head estimate can directly reuse the
  existing THIM `sq_sub_le_length_mul_sum_range_addDiff_sq`. For each admitted
  ray level `1 ≤ a ≤ R`, telescoping to the observed terminal value and that
  path inequality give `x_a² ≤ 2(R+1) Σ_{j=1}^R y_j²`. Consequently the physical
  head before level `K` costs at most `(5/2)(K-1)(R+1)` times the complete
  selected ray energy. This improves the lower-order head term in the paper
  upper bound without changing its leading asymptotic constant; Lean checking
  of its pointwise ray estimate passed with standard axioms; physical weight
  transfer remains in progress. The existing second-octave theorem
  `two_mul_oddSquarefreeWindow_card_le_sum_second_octave_fermi_and_gradient_sq`
  was checked in source: its observable combines Möbius Fermi curvature and
  BVI gradient energy and does not imply this complete selected-jump estimate.
- 2026-10-19 — The complete weighted ray estimate now passed scratch Lean,
  including summability, physical-weight transfer, and the sharper finite-head
  term. With `n=R+1-K`, `λ=2-2cos(π/(2n+1))`, and `M≥0`, its numerator is
  `(1+2^(-(K+1)))((M+1)+M(M+1)λn+(4/3)Mλ)
  +(5/2)(K-1)(R+1)Mλ`, multiplying the complete selected ray energy; the left
  side is `Mλ` times complete sieve ray energy. No assumed source estimate
  enters this result. Full-ray summation is next.
- 2026-10-19 — `FermiPronicRayDecomposition.lean` additionally exposes joint
  summability of both physical ray arrays, reusing its existing odd-ray
  bijection and normalized term identities. Updated source passed; the new
  declaration's axiom audit passed. This supports legal interchange of
  dyadic-level and odd-part sums.
- 2026-10-19 — A broad spectral-gap-limit deep search was inspected in all
  returned candidate/source/ingredient sections but supplied no exact limit.
  The broad `cos tendsto` lexical query was too broad (354 hits) and was
  narrowed to `cos pi tendsto` (six nonapplicable Fourier/phase hits); no
  absence claim is based on the broad query. A focused hybrid `tendsto_sin_div`
  query recovered existing `HTGeometry.tendsto_sin_div_nhdsNE` and its nearby
  `HTGeometry.cos_sub_one_eq`. Both source proofs were read; Lean interface
  and axiom checks passed. Following the trigonometric dependency also found
  mathlib's `Real.continuous_sinc`, a smaller dependency for the limit step.
- 2026-10-19 — Full physical trace summation passed scratch Lean and standard
  axiom checks. Supplying the explicit summand to `Summable.tsum_comm` resolved
  an elaboration heartbeat limit; no heartbeat setting changed. The exact
  global estimate is the displayed ray numerator times total selected energy,
  bounding `Mλ` times total sieve energy. New leaf
  `FermiPhysicalTraceSineUpperBound.lean` contains two ray-energy definitions,
  the ray estimate, and the global theorem; source and all four public axiom
  audits passed. It is wired and index regeneration passed. Initial global
  generated lint failed on the concurrent unwired module
  `BiScaleUncertainty.SieveAffineTranslationAnchoring`; no error concerns
  this leaf. Its umbrella import subsequently appeared; refreshed index and
  global generated lint passed. Exact corpus search retrieves the new global
  theorem. No foreign source file was edited for this gate.
  Matching nonnegative sharpness and the asymptotic limit remain open in Lean.
- 2026-10-19 — The profile-synthesis deep query was inspected across all
  candidates, source arguments, and its proposed ingredient set. It recovered
  finite divisor-sum and octave identities, but no ready-made dyadic cosine
  synthesis. The existing ramp's source proof directly interchanges its finite
  coefficient sum with `sieveSeq`; this is a reusable pattern for the required
  finite power-of-two packet. Existing `pathSineValue_adjacent` was also checked
  in source: it derives exact sine-packet energy from
  `autocorrelationSineWeight_recurrence`. Both are prior work, not new results
  to count. A scratch proof of the classical scaled sine-gap limit passed with
  standard axioms using mathlib `Real.continuous_sinc` and reciprocal
  natural-number limits. The clean gap proof and scalar coefficient limits
  passed. The fixed-parameter native eventual bound also passed with standard
  axioms. Parameter elimination had only two redundant trailing tactics;
  corrected source passed in the twelfth leaf,
  `FermiPhysicalSineAsymptotics.lean`. Its public theorem
  `sieveTotalPronicEnergy_asymptotic_upper` proves the unconditional upper half
  for every positive epsilon, uniformly over coefficients. The public axiom
  audit passed with only standard axioms; the leaf is wired and index
  regeneration passed. Global generated lint failed on concurrent unwired
  `BiScaleUncertainty.CoprimeOverlapQuarticReadout`; no error concerns this leaf.
- 2026-10-19 — The broad packet-mass deep query recovered the existing adjacent
  sine pairing but supplied no exact mass formula; all twenty candidates,
  twenty source arguments, and the proposed ingredient set were inspected.
  The focused `sum_range_cos` hybrid query recovered `HTGeometry.sum_cos_odd`
  in `HTGeometry/OddDirichletKernel.lean`. Source inspection gives the exact
  profile mass above without a new trigonometric summation proof. Exact-name
  lexical retrieval also completed. Search coverage is fully inventoried but
  compiler coverage remains incomplete; no absence or novelty claim follows
  from the broad query's misses.
  Exact-name retrieval also found `QuantumAlg.Util.DirichletKernel`'s
  unconditional sine-multiplied version; its statement and proof were checked.
  The smaller `HTGeometry.OddDirichletKernel` dependency suffices here. Its
  `sum_cos_odd` interface and standard axioms passed in the actual Lean toolchain.
- 2026-10-19 — Scratch cosine-profile mass, finite energy, and nonnegative
  coefficient differences passed with standard axioms. The exact mass reuses
  `sum_cos_odd`; the energy is finite summation by parts with its Neumann
  first recurrence and zero terminal value. The native finite-horizon synthesis
  is now being checked. No lower-bound theorem or sharp limit is claimed yet.
- 2026-10-19 — The complete scratch lower construction passed with standard
  axioms: finite divisor synthesis, nonnegative coefficients, every odd ray,
  post-horizon tails, exact homogeneous selected energy, physical ray bounds,
  global physical ratio, and positive selected energy. The global estimate is
  `(S_r-1)*Q <= lambda_r*S_r*P`, at `r=L+1>=2`, for the explicit nonnegative
  packet. It is being moved into
  `FermiNonnegativeCosinePhysicalTraceLowerBound.lean`; its named source and
  olean check passed, and the leaf is wired. A combined scratch check now audits
  its four public declarations and proves the matching asymptotic lower
  coefficient. The planned sharp characterization is: a uniform asymptotic
  inverse estimate with leading coefficient `C` (allowing every positive
  epsilon slack) holds exactly when `4/pi^2<=C`, both over all coefficients
  and over nonnegative coefficients. Its paper proof uses the cosine family
  for necessity and the established upper bound for sufficiency. The scratch
  capstone subsequently passed in scratch with standard axioms. The former
  upper-only module was renamed `FermiPhysicalSineAsymptotics.lean`, expanded
  with the explicit-family lower and both sharp-constant iff theorems. Its
  named source/olean check and index regeneration passed. No qualified count changes; the literal
  supremum limits, general-horizon extension, and final novelty/significance
  audit remain open.
- 2026-10-19 — Horizon-extension search recovered the existing
  `sieveSeq_horizon_band_sub` in
  `BuchstabHorizonFiltrationAndSawtoothEvolution.lean:81`; its source was checked
  for zero-extension transfer. Supremum searches recovered the generic
  `rayleighQuotientSet`/floor infrastructure and a finite-dimensional graph
  supremum argument. All candidates and source-argument summaries in both
  searches were inspected. The graph-specific proposed ingredient does not
  prove the physical optimal-constant limit; no absence or novelty inference
  is based on these searches.
- 2026-10-19 — Both literal dyadic optimal-constant limits passed in
  `/tmp/thim-physical-optimal-constants.lean`, with standard axioms only. The
  full-horizon extension is now written there, using horizon-band zero extension,
  monotonicity of the ratio supremum, and a squeeze between consecutive powers
  of two. The existing horizon-band module has no olean in this checkout; its
  named prerequisite check is running before the extension can be checked.
  `scripts/formal_tools.py lint --check-generated` passed after regeneration.
- 2026-10-19 — The full supremum-limit scratch now passes, including both
  all-horizon limits with the real logarithm `Real.logb 2 N`. All four limit
  theorems, all four imported sine-asymptotic theorems, and the existing
  horizon-band theorem have only `propext`, `Classical.choice`, and `Quot.sound`.
  The proof is promoted to `FermiPhysicalOptimalConstants.lean` (280 lines);
  its named source/olean check is running before wiring and the final import audit.

## Final prior-work and significance audit (2026-10-19)

The exact mixed-boundary sine spectrum, cosine sums, and scalar asymptotic
machinery are prior mathematics. In particular, this package does not claim
the constant `4/pi^2` or the finite-path inequality as a new theorem in
isolation. The corpus chain inequality and `HTGeometry.sum_cos_odd` are reused.
General discrete Hardy constants and Jacobi spectral methods remain classical
background; see [Liao](https://arxiv.org/abs/1406.1984) and
[Webb–Olver](https://link.springer.com/article/10.1007/s00220-021-03939-w).

The native result is the optimal conditioning law for the actual complete
selected Fermi boundary trace in its pronic measure, including equality of
signed and nonnegative leading constants. A generic path inequality alone
does not establish the divisor-compatible ray decomposition, uniform pronic
weight control across all odd cores, the finite-horizon terminal relation,
or realizability of the sharp cosine profile by nonnegative sieve coefficients.
Those are proved here before the classical sine estimate is applied. The
result gives the exact replacement for the failed horizon-uniform inverse
bound; the finite-window estimates, counterexamples, and asymptotic refinements
form one contribution, not separate counts.

The final deep package search returned 20 candidate declarations, 20 source
arguments, and one proposed two-step ingredient set; all were reviewed. The
ingredient set uses this task's own ramp and ray lemmas. The lexical
`fermi inverse` query had 36 hits over 14 modules; both pages were exhausted.
Relevant older sources were checked: the PM rough-factor inverse is a finite
Möbius dilation identity; the PM positive-Haar profile concerns a cutoff's
linear energy growth; the Fermi Gram-cell bridge identifies head/tail cell
integrals. None of those statements is the present optimal selected-jump
conditioning theorem. Unrelated spectral and fermionic-algebra hits were also
triaged. This is a bounded prior-work audit, not a proof of global priority:
the deep search reported 74,277 inventoried files but only 43 compiled snapshots,
with substantial pending/stale compiler coverage. Every dependency actually
used here was checked against this Lean toolchain.

## Final formal certificate

Module: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiPhysicalOptimalConstants.lean`.

| Result | Public theorem |
|---|---|
| Signed dyadic supremum limit | `fermiPhysicalInverseConstant_dyadic_limit` |
| Nonnegative dyadic supremum limit | `fermiNonnegativePhysicalInverseConstant_dyadic_limit` |
| Signed all-horizon real-logarithm limit | `fermiPhysicalInverseConstant_logb_limit` |
| Nonnegative all-horizon real-logarithm limit | `fermiNonnegativePhysicalInverseConstant_logb_limit` |

The two public constants are the literal ratio suprema. The underlying physical
energies retain their original pronic weights. All fourteen supporting leaves
have passed named source checks and their public axiom audits; the final leaf
is wired into `GaloisForLFunctions.TransHorizonIncidenceMechanics`. Final
`scripts/formal_tools.py index` and `scripts/formal_tools.py lint --check-generated`
both exited zero. No umbrella/full build, numerical experiment, new axiom,
proof hole, heartbeat increase, or field-README edit was used.
