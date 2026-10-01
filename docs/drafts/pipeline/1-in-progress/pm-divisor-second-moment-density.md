# PM divisor coefficients: second-moment density

Type: CONJECTURE / arithmetic covariance calibration
Stage: 1 — in progress
Parent: [PM31](pm-power-damped-mobius-haar.md)
Producer: [anchored centered energy](pm-centered-divisor-dyadic-energy-budget.md)

## Exact candidate

For epsilon>0, use the actual multiplicative coefficients
c_epsilon(n)=product_(p|n)(1-p^(-epsilon)), n>=1, and
alpha_epsilon=1/zeta(1+epsilon). Conjecture the exact second moment

    (1/X) sum_(1<=n<=X) c_epsilon(n)^2 -> gamma_epsilon,
    gamma_epsilon = product_p (1-2*p^(-1-epsilon)+p^(-1-2epsilon)).

The candidate is an unconditional arithmetic mean-value identity. It does
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
an exact comparison and a small-damping candidate.

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
alpha_epsilon/epsilon->1 then predicts

    gamma_epsilon/epsilon -> 1/2,
    v_epsilon/epsilon -> 1/2.

These are symbolic limits, with no numerical experiments. The proof must
use positive damping throughout; no substitution of the assigned zeta
pole value at epsilon=0 is valid.

## Required audit / limits

- Search1091 and lexical1092 found no exact mean-square c_epsilon result;
  all returned statements/ingredient chains were reviewed on the producer
  card. Search1093 now checks the exact second-moment mechanism.
- Verify the absolute Euler-product construction and summatory interchange
  against the current Lean corpus before adding code. The paper argument
  above is not yet a Lean-certified theorem.
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
