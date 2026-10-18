# TG: native first-jet shell scale law

Status: formalized component; paper proof, all three Lean leaves and axiom audit
complete. TG and RH remain open. Global lint reports eight unrelated unreachable
modules; none belongs to this component.

## Scope and rotation

Previous completed family: EGC (four source hashes revalidated at session start).
This investigation moves to TG, after comparing its current source obligation with
BAG's common-height signed cubic obligation. Read-only frontier and both framework
READMEs remain unchanged.

## Exact target

TG requires an arithmetic estimate on the same integer charge counted by
`FormationRectangle.opTrace_formationCubicDefect`, or an unconditional exponent-zero
bound for the complete central Gaussian prime-minus-continuum gap. The criterion
`riemannHypothesis_iff_gaussianCentralGap_le_explicit` does not prove its premise.
No replacement positive Gram form, fixed regularization, or source-admission theorem
will be reported as closing this sign obligation.

## Completed scope

1. Locate actual source and previous obstruction theorems in Lean; search full corpus.
2. Conjecture a source estimate retaining the arithmetic weights, continuum, all
   scales, and mixed terms. Attack the estimate on paper before implementation.
3. Prove any surviving exact statement, connect it to BSU/BVI and TG, then formalize
   and run individual leaf audits, axiom checks, lint and source-hash checks.

## Evidence and rejected shortcuts

- `GaussianCentralGapExplicitCriterion`: RH iff the literal central gap is at most
  `-1/10 + 32*sqrt(y)` for all `0 < y <= 1`.
- `BurnolBaseFirstJetAdmission`: native first-jet synthesis is already bounded;
  prime slice has energy `1/(4*p)`, positive depths are square summable.
- `RoutePPrimitiveBurnolBaseNuclearSynthesis`: base covariance already has its
  literal sub-unit trace. Transferring that trace to Xi remains unpaid.
- `FormationAnchoredCubicSpecialization`: Gaussian anchors have zero winding;
  completed-minus-anchor trace is the exact Xi zero count. Finite anchors alone
  do not bound the completed charge.
- Proposed divisor averaging of the Gaussian gap reduces Lambda to log by
  `1 * Lambda = log`. Existing BSU divisor-average Chebyshev laws already supply
  a negative linear channel. This average erases the unsolved signed inversion;
  it is not a proof of the unaveraged central gap.

## Search and verification state

`/tmp/hgt-tg-central-gap-search.json`: deep search completed, partial=false;
74,039 files inventoried, source coverage complete, compiler freshness mixed.
Generated cubic/valuation ingredient suggestions did not address the source gap.
Exact lexical Gaussian source search completed separately. Source declarations
remain authority. The API probe, all leaf compilations and the final axiom audit
passed. Detailed verification and the global lint limitation are recorded below.

## Formalized theorem and dependency-closed paper proof

Let `S` be the original bounded Burnol first-jet synthesis, `F_(p,k-1)` its
columns, and `lambda_(p,k-1)=k log p`, for every prime `p` and integer `k>=1`.
The already proved column identity is

`||F_(p,k-1)||^2 = 1/(4*k*p^k)`.

For `t>0`, `c>=1`, define diagonal weights
`a_(t,c)(p,k-1)=exp(-2*t*lambda)-exp(-2*c*t*lambda)` and the FULL covariance
`Q_(t,c)=S diag(a_(t,c)) S*`. No prime depth or mixed physical matrix entry is
discarded. The square-root synthesis is `S diag(sqrt(a_(t,c)))`.

1. `0<=a<=1`; hence this is a positive covariance of the literal source.
   Its squared column norms sum to
   `E(t,c)=(log zeta(1+2t)-log zeta(1+2ct))/4`.
   Indeed each damped column energy is
   `p^(-k*(1+2t))/(4*k)`, exactly the existing full Euler-log prime-power
   weight divided by four. Both Euler sums converge absolutely for `t>0`.
   Hilbert-basis invariance makes the square-root synthesis Hilbert--Schmidt;
   its covariance is trace class and `Re Tr Q=E(t,c)`.
2. This is also EXACTLY the difference of the two full damped covariances,
   by distributivity of `S diag(.) S*`; it is not the covariance of a
   difference vector (which would have different cross terms).
   The original weighted translation satisfies
   `T_t F_(p,k-1)=exp(-t*lambda_(p,k-1)) F_(p,k-1)`.
   Hence `S diag(sqrt(exp(-2t*lambda)))=T_t S` on each source basis vector,
   and then on the whole source Hilbert space by continuity and its basis
   expansion. The damped covariance is exactly `(T_t S)(T_t S)*`.
3. Existing `EulerFisherPoincareBoundary.eulerLogRegular_eq` gives
   `log zeta(beta)=-log(beta-1)+R(beta)` with `R` analytic at `1`. Therefore
   `E(t,c)=log(c)/4+(R(1+2t)-R(1+2ct))/4`, and
   `Re Tr Q_(t,c) -> log(c)/4` as `t->0+`.
4. Each diagonal weight tends to zero and is at most one. For every source
   vector `v`, dominated convergence of `sum |a_i v_i|^2` yields
   `diag(a_(t,c))v ->0`; bounded left/right synthesis gives `Q_(t,c)f ->0`
   for EVERY physical vector `f`. For `c>1`, trace norm cannot tend to zero:
   `|Re Tr Q| <= ||Q||_1`, whereas the trace limit is strictly positive.
5. At `c=2`, the literal shell trace tends to `log(2)/4<1` and is eventually
   strictly between zero and one, without a normalization chosen to force it.

This proves a positive source-scale law and the precise nonzero boundary mass
which a naive strong-limit trace argument loses. It removes an unquantified
damping-shell trace from the native first-jet calculation. It does NOT identify
`Q` with `formationCubicDefect`, supply the Gamma/co-Poisson residual, or prove
the central Gaussian sign. TG and RH remain open. No route is retired.

## Implementation and verification

- `formal/GaloisForLFunctions/BiScaleUncertainty/PositiveDiagonalCovariance.lean`:
  full weighted covariance, physical mixed entries, positivity, Schatten-1
  membership, exact column-energy trace, covariance subtraction and strong
  convergence from bounded pointwise source weights.
- `formal/GaloisForLFunctions/RHTower/BurnolFirstJetDampingShell.lean`:
  original weighted-translation identification, full prime-power trace formula,
  positive trace-class shells and strong convergence to zero.
- `formal/GaloisForLFunctions/RHTower/BurnolFirstJetShellScaleLaw.lean`:
  exact analytic remainder, trace limit `log(c)/4`, eventual dyadic sub-unit
  trace, and failure of trace-norm convergence to zero for `c>1`.

All three leaves compiled individually with `lake --old env lean ... -j1`
and emitted their `.olean` and `.ilean` files. Final compilation logs are empty;
all exit codes are zero. Each leaf has exactly one direct import in its theorem
area umbrella. No umbrella or whole-project build was run.

The `/tmp` API probe passed. The separate `/tmp` axiom audit imported the final
scale-law leaf and checked all 42 public declarations. Its exit code is zero;
the only axioms are `propext`, `Classical.choice` and `Quot.sound`. No added
`sorry`, `admit`, `axiom`, `opaque` or `unsafe` declaration exists.

`scripts/formal_tools.py lint` ran and exited 1, solely for these eight modules
outside this task that were unreachable from their respective umbrellas:

- BSU: `ExpDecayFourierMass`, `FactorialMuntzTailArchimedeanGrowth`,
  `FactorialMuntzTailWeilGrowth`.
- BVI: `ActiveDeletedMartingaleAndShiftedEulerConvergence`,
  `ArithmeticLagSchedulesAndSharpRecoveryHorizon`,
  `RamanujanLagCoefficientAndTotientQuotient`,
  `TrueTranslationPredictionAndExactCompression`,
  `ValuationVisibilityClockAndRamanujanSupport`.

Scoped `git diff --check` passed. The global whitespace check separately found
an unrelated trailing blank line in `BezoutValuationIncidence/README.md`.
Existing research leaves, framework READMEs and the frontier ledger were not
edited. No external novelty audit or publication-priority claim is made.

Evidence is retained in `/tmp/hgt-tg-shell-audit-manifest.json`,
`/tmp/hgt-tg-shell-source-sha256.txt`, `/tmp/hgt-tg-shell-axioms.lean`,
`/tmp/hgt-tg-shell-axioms.log`, `/tmp/hgt-tg-shell-api.lean`,
`/tmp/hgt-tg-shell-api.log` and `/tmp/hgt-tg-formal-lint.log`. Source hashes were
rechecked after all Lean audits. No owned build or search process remains.

## Session boundary

The user cleared the broader research goal and requested completion of work
already started. These three leaves, their imports and audits are finished.
The task stops here. No additional route investigation or theorem family was
started. Future research should respect the requested rotation across 27 live
routes and 18 candidates; the latest completed families were EGC, then TG.
