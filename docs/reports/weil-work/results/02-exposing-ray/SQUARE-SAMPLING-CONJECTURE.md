# Critical-density diagnostic: square samples

Status: DEFERRED after cycle20 parent audit; not a substitute for the universal
WP02 producer. No proof of C-minus, Lean result or scientific-novelty claim.
The original claim that square density is the first unexcluded density is
withdrawn: the polar primitive-set mean-square law strengthens the old sparse
argument. See CYCLE20-AUDIT.md for the precise paper consequence and limits.

## Competing exact assertions

C-minus: there exist m, a>=0, alpha:Fin m->R with alpha_i>=0 and actual complex
C2 functions f_i such that every f_i is IsPolarTest a f_i, and

    sum_i alpha_i integral |paperFT(f_i)|^2 = 1,
    sum_i alpha_i atomCoeff(f_i,n^2) = 0   for every integer n>=2,
    sum_i alpha_i archEnergy(f_i) < 0.

C-plus is its negation: every such square-null polar mixture has nonnegative
archimedean energy. The zero family causes no normalization issue in C-minus;
positivity for all masses is equivalent to positivity at mass one by scaling
nonzero families. Neither assertion assumes RH or an existing cone point.

The original proposed attack was C-minus. Its structural question was whether
the first integer sampling density outside the displayed sparse-support
theorem already admits negative polar null mixtures. That motivation omitted
the stronger primitive-set mean-square parent and is superseded below.
Falsity would identify a substantially stronger archimedean constraint than
the subcritical counting argument. Truth would exclude a concrete critical
sampling relaxation, not prove the all-integer lower estimate.

[OPEN CORE] Construct the actual finite polar mixture with all square samples
zero and strictly negative energy, or prove that no such mixture exists.
Far-polar Fejer leakage plus independent atom repair does not close this:
at square-root density its current absolute repair budget need not vanish.
A new coherent estimate, or a genuine exclusion, is required.

## Hostile and parent audit

- `WeilPositivitySparseWeightsObstruction.not_weilPositive_of_sparse_support`
  requires a strict exponent theta<1/2. Squares have exponent1/2.
- `WeilPositivityHalfPoleRigidity` excludes perturbations
  Lambda+c*1_squares for nonzero c. It does NOT classify every weight supported
  on squares or prove either assertion above.
- Power-of-one-prime periodization is not the square-sample condition:
  n^2 ranges over all integers n, not just one multiplicative orbit.
- A scaled low-degree L-function classification is not available for free.
  Booker's L-data require discrete, almost-integral spectral multiplicities
  and specific coefficient bounds (Definition1.3 in
  https://arxiv.org/pdf/1308.3067). Those hypotheses have not been produced.
- Do not assume that an arbitrary polar-positive weight is full-positive.
  Do not replace its sqrt(n)(log n+C) box by a logarithmic box.

Original verdict: SURVIVES PRELIMINARY ATTACK as an open diagnostic.
Cycle20 verdict: REDISCOVERED sparse mechanism / insufficient endpoint utility.
The named sparse theorem's exponent1/2 is not a sharp boundary of current
corpus machinery. Mean-square plus its local-mass obstruction excludes every
support count O(N^theta), theta<1, at the level of existence of a polar-positive
weight. This includes squares. Passing from this exclusion to the exact finite
negative square-null mixture still requires the restricted-coordinate duality
argument; it is not claimed as a compiled theorem here. Do not spend another
cycle constructing an annulus witness merely because the older theorem's
signature stops at1/2. The universal lower producer remains the objective.
