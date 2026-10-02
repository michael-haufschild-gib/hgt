# PM divisor coefficients: second-moment density

Type: THEOREM (Lean) / arithmetic covariance calibration
Stage: 3 — formalized
Parent: [PM31](../1-in-progress/pm-power-damped-mobius-haar.md)
Producer: [anchored centered energy](../1-in-progress/pm-centered-divisor-dyadic-energy-budget.md)

## Exact theorem

For epsilon>0, use the actual multiplicative coefficients
c_epsilon(n)=product_(p|n)(1-p^(-epsilon)), n>=1, and
alpha_epsilon=1/zeta(1+epsilon). The exact second moment is

    (1/X) sum_(1<=n<=X) c_epsilon(n)^2 -> gamma_epsilon,
    gamma_epsilon = product_p (1-2*p^(-1-epsilon)+p^(-1-2epsilon)).

This is an unconditional arithmetic mean-value identity. It does
not bound the anchored cumulative remainder R_epsilon(X). It is useful
only as a verified calibration for any proposed pair-correlation estimate.

## Paper mechanism

The square coefficient is again a divisor sum. Its squarefree Euler
coefficient at a prime p is -2*p^(-epsilon)+p^(-2epsilon). Its absolute
Dirichlet series at exponent one converges, since the prime term is at
most 2*p^(-1-epsilon) and this is dominated by the convergent integer
p-series. Finite divisor-floor summation and dominated convergence give
the displayed density, with the absolutely convergent Euler product.
Equivalently, bounded finite-prime products approximate c_epsilon from
above and their mean-square tails are controlled by their mean tails.

The centered coefficient variance therefore has mean
v_epsilon=gamma_epsilon-alpha_epsilon^2. The local identity below gives
an exact comparison and a small-damping asymptotic.

Put u=p^(-1-epsilon), v=p^(-1-2epsilon). Then

    (1-2u+v)*(1-v)/(1-u)^2 = 1-((u-v)/(1-u))^2.

Consequently

    gamma_epsilon = alpha_epsilon^2*zeta(1+2epsilon)
      * product_p [1-((p^(-1-epsilon)-p^(-1-2epsilon))
                        /(1-p^(-1-epsilon)))^2].

Each correction factor lies in (0,1]. Its deficit tends to zero as
epsilon->0+ and is bounded by a constant times 1/p^2, uniformly for
positive epsilon (p>=2). Dominated summation of the deficits gives that
the product tends to one. The already audited reciprocal zeta pole law
alpha_epsilon/epsilon->1 then gives

    gamma_epsilon/epsilon -> 1/2,
    v_epsilon/epsilon -> 1/2.

These are symbolic limits, with no numerical experiments. The proof must
use positive damping throughout; no substitution of the assigned zeta
pole value at epsilon=0 is valid.

## Required audit / limits

- Search1091 and lexical1092 found no exact mean-square c_epsilon result;
  all returned statements/ingredient chains were reviewed on the producer
  card. Search1093 now checks the exact second-moment mechanism.
- The absolute Euler-product construction, summatory interchange and
  positive-damping limit were checked against the current Lean corpus.
  The paper argument is certified by the three audited leaves below.
- A translation-averaged variance or a coefficient second moment does not
  supply a bound for sum_(n<=N)(c_epsilon(n)-alpha_epsilon) at the fixed
  arithmetic origin. Any such transfer is a separate producer requiring
  an actual proof. No stationarity/independence assumption about the
  anchored integer sequence may be introduced.
- The canonical small-positive energy estimate and RH remain open.

## Consequence for the actual signed covariance

For every prime p, the ratio of the local second-moment factor to the
squared local mean is

    1 + (p^(-1-2epsilon)-p^(-2-2epsilon))
          /(1-p^(-1-epsilon))^2 > 1.

The convergent product therefore gives gamma_epsilon>alpha_epsilon^2.
In particular the exact centered coefficients b(n)=c_epsilon(n)-alpha
have strictly positive mean square v_epsilon. Abel summation then gives

    sum_(n<=N) b(n)^2/n divided by log N -> v_epsilon.

The diagonal of the already formalized finite maximum-index covariance
is sum_(n<=N)b(n)^2*(1/n-1/(N+1)); it has the same logarithmic leading
coefficient. Thus this centered-coordinate diagonal diverges at EVERY
positive damping, even in the independently admitted epsilon>=1/2 range.
This differs from the original damped-Mobius generator diagonal, which
is summable. Any finite centered covariance budget must retain negative
cross cancellation of this full logarithmic diagonal.

For an admitted source, finite cumulative energies are bounded, so the
off-diagonal covariance divided by log N tends to -v_epsilon. In the
unconditional epsilon>=1/2 range this becomes an unconditional sharp
cancellation law. For smaller positive damping the same conclusion must
not be inferred without proving the energy control. No claim is made
that subtracting only v_epsilon*log N leaves a bounded remainder: the
second-moment mean theorem alone gives only its leading coefficient.

- Search1093 (`power damped divisor coefficient second moment density`,
  deep, excluding PMPowerDampedMobius): all20 candidate statements, all20
  source arguments and both generated ingredient steps reviewed. No exact
  arithmetic mean-square density returned. Divisor-polynomial fourth
  moments retain the full off-diagonal; the proposed chain does not bound
  it. The finite-gcd divisor-moment result uses an lcm pair kernel and may
  inform finite-prime means, but is not the requested signed density.
  Other hits concern different damping carriers. Partial=false;63941files;
  index1175738, coverage/current1175759; semantic coverage unmeasured,
  background refresh incomplete. No exhaustive novelty claim.

- Search1094 (`divisor sum summable mean density multiplicative square`,
  deep, excluding PMPowerDampedMobius): all20 candidate/all20 source
  statements and both proposed chain steps reviewed. Squarefree-density
  results concern mu(n)^2, not c_epsilon(n)^2. The generic damped-Mobius
  convolution identity is applicable to the square's local weight
  2*p^(-epsilon)-p^(-2epsilon). Its zero-free receiver retains a summatory
  hypothesis. Averaged deletion divisor covariance has another cutoff
  family. Partial=false;63943files;index1175862,coverage1175890/current1175891;
  semantic coverage unmeasured, background refresh incomplete.
- Exact implementation plan: reuse `DampedMobius` at the displayed local
  weight. For squarefree n, its absolute coefficient is at most
  2^omega(n)*n^(-epsilon)=d(n)*n^(-epsilon). The corpus's unconditional
  divisor-square p-series majorant proves absolute summability after
  division by n. Finite divisor-floor summation plus dominated convergence
  then proves the second-moment density. Multiplicativity and the generic
  absolutely convergent Euler product give its exact prime factors.
  No anchored remainder estimate is inferred from this coefficient mean.

- Scratch1095: exact square-divisor identity, unconditional weighted
  absolute summability, generic divisor-floor mean limit and the actual
  coefficient second-moment limit have passed local proof checking.
  The Euler-product proof exposed a structure-instance conversion issue;
  replaced broad conversion by `HasProd.congr_fun`. Centered second-moment
  limit and nonnegativity now checking. No promotion or final audit yet.
- Search1096 (`summatory density harmonic weighted sum logarithm limit`,
  deep): all20 candidate/all20 source statements and both ingredient steps
  reviewed. Finite harmonic bounds and Abel identities are reusable, but
  the generated weighted-sum chain does not prove the needed logarithmic
  mean transfer. Other results require different source bounds or concern
  unrelated carriers. Partial=false;63944files;index1175923,
  coverage/current1175928; semantic coverage unmeasured and background
  refresh incomplete. A precise harmonic-mean transfer still needs proof.

- Full scratch1095 passed, including exact prime-factor Euler product,
  second-moment mean, centered-variance mean, nonnegative variance and
  gamma<=alpha. A redundant tactic emitted a suggestion; replaced it by
  explicit exponent identities for a clean recheck. No heartbeat limits
  were raised: the one inference timeout was fixed by explicit real types.
  The generic divisor-mean theorem also needs no zero-value hypothesis.
  Strict variance positivity, small-damping asymptotic and logarithmic
  covariance calibration remain beyond this initial density leaf.

- Clean scratch1095 passed with empty diagnostics. Promoted/wired
  `PMPowerDampedMobiusSecondMoment` (268 lines /18 declarations); targeted
  build and exhaustive final audits running. This initial leaf certifies
  the exact density/Euler product and centered mean-square, not yet their
  strict positivity or small-damping/logarithmic refinements.
- Strict-variance proof can avoid any unproved infinite ratio product.
  With t=p^(-epsilon), the local second factor minus the squared mean
  factor is exactly t^2*(p-1)/p^2>0. Both Euler products converge, and the
  squared mean limit is strictly positive by reciprocal-zeta nonvanishing.
  Fix one prime. On every finite aperture containing it, compare the
  remaining factors monotonically, retaining this prime's strict ratio.
  Passing to the product limits preserves that fixed strict improvement.
  Thus gamma>alpha^2 follows without assuming a summatory energy bound.

- Leaf32 targeted old build36s passed. Exact-body, exhaustive names/API,
  unique import and no-proof-debt checks passed. Final actual-leaf audit
  now running; all18 axiom reports follow. Global lint has eleven unrelated
  unwired leaves (including WeilFullConePolarizedRepresentation) and three
  generated-file freshness findings from concurrent work; no owned leaf
  or proof-debt finding. No global lint-pass claim.
- Strict-variance paper argument now drafted as scratch1097: a generic
  real finite-product strict comparison, the actual real mean Euler
  product, exact local factor gap and unconditional variance positivity.
  It has not yet been compiled; leaf32 final audits take precedence.

- Leaf32 final actual `lake env lean` check passed with empty diagnostics;
  all18 declaration axiom reports are now running.
- Search1098 (`tendsto weighted average nonnegative divergent weights
  mean`, deep): all20 candidate/all20 source statements and both proposed
  ingredient steps reviewed. Exact reusable machinery found:
  `RHTower.weightedCesaro_smul` transfers a convergent sequence with
  nonnegative divergent total weights; Etemadi's antitone-weight theorem
  transfers a Cesaro mean directly, with an explicit endpoint-weight
  bound. These can supply the harmonic calibration once instantiated.
  The generated second step instead invokes unrelated asymptotic carriers
  and is not a proof. Partial=false;63952files;index1176114,
  coverage1176120/current1176121;semantic coverage unmeasured, refresh
  incomplete. Verify exact applicable definitions before new code.

- Second-moment density fully audited: `PMPowerDampedMobiusSecondMoment`
  (268 lines /18 declarations), targeted old build36s, final actual-leaf
  check with empty diagnostics, all18 standard-axiom reports, exact body,
  exhaustive names/API, unique import and no-proof-debt checks passed.
  It proves the literal coefficient square's summatory mean and Euler
  product, the centered mean-square gamma-alpha^2>=0, and gamma<=alpha.
  Combined: thirty-two leaves /7720 lines /570 audited declarations.
  Strict positivity, small-damping variance and the logarithmic signed
  covariance calibration remain on the second-moment card. The actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  has eleven unrelated unwired leaves and three generated freshness
  findings; no owned or proof-debt finding, no global pass claimed.

- Strict-variance scratch1097 passed with empty diagnostics after an
  explicit real-to-complex cast and a tactic sequencing cleanup. It proves
  the actual real mean Euler product, exact local gap and gamma>alpha^2.
  Added the logarithmic-mean step using the existing Etemadi antitone-weight
  theorem at w(n)=1/(n+1), with its endpoint bound verified by finite
  monotonicity; this extension is now checking. Source search also found
  `SummableDivisorHarmonicMean` and its exact reciprocal-divisor identity,
  but no duplicate dominated-convergence theorem is needed here.

- Harmonic extension passed its mathematical obligations; removed an extra
  tactic after a goal already closed. Scratch1097 now includes the exact
  finite diagonal/off-diagonal covariance split, logarithmic diagonal
  limit v_epsilon>0 and its no-common-budget corollary. Under admission,
  total energy/log N tends to zero, so off-diagonal/log N tends to
  -v_epsilon; epsilon>=1/2 supplies this admission unconditionally. The
  full extension is checking, not yet promoted/audited.
- Small-damping refinement will compare the actual product
  C_epsilon=gamma_epsilon*alpha_(2epsilon)/alpha_epsilon^2 with one.
  Its exact local factors are 1-delta_p with delta_p=((u-v)/(1-u))^2.
  Finite products give 0<=1-C_epsilon<=sum_p delta_p after limits, and
  dominated convergence of the p^-2 majorant makes C_epsilon->1. Combining
  with the already established alpha_epsilon/epsilon->1 yields
  gamma_epsilon/epsilon->1/2 and v_epsilon/epsilon->1/2. This avoids assigning
  the limiting value to the defined reciprocal zeta at its pole. Search1099
  now checks the exact product-perturbation mechanism before new code.

- Search1099 (`Euler product summable deficits parameter limit one`,
  deep): all20 candidate/all20 source statements and both proposed
  ingredient steps reviewed. The generic absolutely convergent Euler
  products and real zeta Euler product are applicable infrastructure;
  unrelated Weil/constitutive deficits do not prove this parameter limit.
  The generated chain pairs different carriers and is not applicable.
  Partial=false;63957files;index1176285,coverage1176293/current1176294;
  semantic coverage unmeasured and background refresh incomplete.
- Quantitative implementation of the correction: write t=p^(-epsilon)
  and delta_p=((t-t^2)/(p-t))^2. For epsilon>=0, p>=2 gives 0<t<=1,
  p-t>=p/2 and 0<=t-t^2<=1. Hence 0<=delta_p<=4/p^2 and delta_p<=1.
  At epsilon=0 its numerator is zero and denominator p-1 is nonzero, so
  each deficit tends to zero. This supplies the required summable
  domination and avoids an unsupported interchange of infinite products.

- Full scratch1097 passed with empty diagnostics. Promoted and wired
  `PMPowerDampedMobiusCovarianceCancellation` (269 lines /17 declarations).
  It proves strict positive variance, exact signed-covariance split,
  diagonal/log N->v_epsilon, failure of every common diagonal budget,
  and off-diagonal/log N->-v_epsilon under admission, unconditionally for
  epsilon>=1/2. Targeted build and final audits are running. The remaining
  card refinement is v_epsilon/epsilon->1/2; the actual small-positive
  energy estimate remains a separate open producer.

- Covariance leaf targeted old build7.8s and exact-body/exhaustive
  names/API/unique-import/no-proof-debt audits passed. Final actual leaf
  now running; seventeen axiom reports follow. Global lint has twelve
  unrelated unwired leaves (including LiClockThetaScoreMeasure and
  LiEvenCrossActualClockSourceCorrelationEnvelope) and two generated
  freshness findings (API/overview), no owned/proof-debt finding.
- Scratch1100 drafted the finite product-deficit lower bound, the limiting
  product squeeze, exact prime deficits, uniform 4/p^2 domination,
  summability and dominated small-damping convergence. It is not compiled;
  leaf33 final audits take precedence. Actual correction-product identity
  and scalar variance asymptotic are still to add.

- Covariance leaf final actual `lake env lean` passed with empty diagnostics;
  seventeen declaration axiom reports now running.
- Scratch1100 now also contains the exact correction-product identity,
  squeeze-to-one limit, real reciprocal-zeta slope and the proposed exact
  gamma/epsilon and variance/epsilon limits 1/2. All of scratch1100 remains
  uncompiled. Its scalar proof uses the analytic residue unit at zeta's
  pole, with positive-damping eventual equalities throughout.

- Signed covariance calibration fully audited:
  `PMPowerDampedMobiusCovarianceCancellation` (269 lines /17 declarations),
  targeted old build7.8s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The variance is strictly positive
  at every positive damping. The actual centered diagonal/log N tends to
  this variance and has no common finite budget, including the admitted
  safe range. The exact off-diagonal/log N tends to its negative under
  actual admission, unconditionally at epsilon>=1/2. Combined: thirty-three
  leaves /7989 lines /587 audited declarations. Small-damping variance
  asymptotic is drafted; the canonical small-positive energy bound and RH
  remain open. Global lint has twelve unrelated unwired leaves and stale
  API/overview, no owned/proof-debt finding; no global pass claimed.

- First scratch1100 check found explicit finite-set inference, function
  composition/pointwise division unfolding, and one-sided positivity
  elaboration issues; its scalar field simplifications also closed two
  goals before redundant tactics. Added exact sets/types and Pi.div_apply,
  removed redundant tactics. No mathematical obstruction or raised
  heartbeat limit; corrected full recheck now running.

- The second check reduced scratch1100 to three structure-instance and
  pointwise-division conversion errors. Replaced simplifier-only
  conversions by explicit function extensionality; the full recheck is
  running. No statement or mathematical argument changed.

- Scratch1100 now passes with empty diagnostics. The conversions also
  discharged their function equalities, so redundant extensionality
  tactics were removed. Promoted/wired
  `PMPowerDampedMobiusSmallDampingVariance` (251 lines /17 declarations).
  Exact correction product and both positive-damping slopes equal to 1/2
  are proved. Targeted build, actual-leaf audit and axiom audit remain.

- Leaf34 targeted old build and exact-body, exhaustive names/API,
  unique-import and no-proof-debt audits passed. Final actual-leaf
  `lake env lean` is now running; seventeen axiom reports follow.

- Small-damping variance refinement fully audited:
  `PMPowerDampedMobiusSmallDampingVariance` (251 lines /17 declarations),
  targeted old build76s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The exact Euler correction
  tends to one; gamma_epsilon/epsilon and v_epsilon/epsilon both tend to
  1/2 as epsilon->0+. All pole identities use positive damping.
  Combined: thirty-four leaves /8240 lines /604 audited declarations.
  The coefficient second-moment card is now formalized; the actual
  small-positive cumulative-energy bound and RH remain open. Global lint
  reports ten unrelated unwired leaves, no generated freshness error and
  no owned/proof-debt finding; no global pass claimed. Next candidate:
  natural-denominator Ramanujan expansion and its anchored energy budget.
