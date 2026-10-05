# BAG actual divisor-square axis and uniform pole coalescence

- **ID:** C28.56af.1.
- **Route:** BAG arithmetic axis -> joint damping-height transfer -> physical
  contractions, with complete signed near-resonances retained.
- **Status:** Formalized; production and all 12 public axiom audits passed.

## Exact actual-source result

For 0<=epsilon<1/16 and Re s>1, the complete divisor-square Dirichlet series is

    sum_n pmPowerDampedDivisorCoeff(epsilon,n)^2 n^(-s)
      = axisEulerCorrection(s+epsilon,-epsilon)
          *zeta(s)*zeta(s+2epsilon)/zeta(s+epsilon)^2.

All integers, all prime powers and the full unordered prime product occur.
Bounded actual coefficients prove summability. Their multiplicativity and the
full prime-power geometric series prove the Euler identity. The correction is
the EXISTING literal BAG axis product, not an assumed correction function.

Let F denote zetaResidueFactor and define

    Q(sigma,alpha)=regularAxisSource(sigma,alpha)/F(sigma)^2.

The exact continuation is

    S_e(s)=[1+e^2/((s-1)(s+2e-1))]*Q(s+e,-e).

Both moving poles remain. Where F(sigma) is nonzero, Q(sigma,0)=1; its first
alpha derivative at zero is zero throughout Re sigma>7/8. The two F derivatives
cancel and the full axis product has zero derivative. No finite-prime derivative
is substituted for the complete product derivative.

There are source-constructed d>0 and C>0 such that, for T=1+|t|,
dist(sigma,1+it)<=d/T^9 and |alpha|<=d/T^9 imply

    |Q(sigma,alpha)-1| <= C T^54 |alpha|^2.

Consequently the ACTUAL continuation satisfies

    |S_e(s)-1| <= C |e|^2 T^54
                  *[1+|((s-1)(s+2e-1))^(-1)|]

whenever s+e and e lie in the corresponding source disks. This is uniform
complex damping-squared cancellation, including arbitrarily small damping.
The displayed polynomial exponents are proof envelopes, not optimization goals.
As usual, totalized expressions at the two poles are irrelevant to punctured
contour identities.

## Why the uniform cancellation holds

The actual F and 1/F have polynomial bounds on proved zero-free disks about
1+it. The full K product has a uniform bound on its analytic tube. On a smaller
sigma disk and twice the required alpha disk, these give a polynomial bound
for Q. Holomorphy of the literal regularAxisSource supplies each alpha slice.
Second-order Schwarz, using Q(0)=1 and Q'(0)=0 on that slice, yields the
quadratic alpha factor without a Cauchy estimate that loses damping. Expanding
the exact two-pole expression then proves the continued-source remainder bound.

This resolves the uniform source cancellation needed before contour shifting.
It does not exchange a fixed-damping limit with a moving-height limit.

## Lean and evidence

Production leaf: ChiRamanujanDampedSquareAxis.lean, 12 public declarations.
Principal producers:

- dampedSquareDirichlet_eq_axis
- dampedSquareDirichlet_eq_twoPole
- exists_dampedSquareRegularSource_quadratic_bound
- exists_dampedSquareContinuation_remainder_bound

Foreground production80197 passed with a clean log:
`lake --old env lean GaloisForLFunctions/RHTower/ChiRamanujanDampedSquareAxis.lean
-o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ChiRamanujanDampedSquareAxis.olean`.
Axiom26840 passed for all 12 public declarations; only propext,
Classical.choice and Quot.sound occur. Index41850 passed and all 12 names
appear in LEAN_API.md. The leaf is imported once by RHTower.lean; no
umbrella/full build was run. Lint38417 reports 40 unrelated unreachable
modules, no proof-debt or new-leaf errors; repository-wide lint does not pass.
Logs remain in `/tmp/bag-square-axis-{production,axioms,index,lint}-01a1.log`.

Search93135 was partial65595/65595 after malformed filter/judge JSON; it found
fixed-epsilon moment laws. Search90093 was nonpartial65596/65596 and supplied
Euler/LSeries machinery. Search12567 was nonpartial65596/65596; its proposed
homological double-zero ingredient was rejected as irrelevant. All ranked
sections were inspected. Actual axis and zero-free source files, and this
toolchain's second-order Schwarz theorem, ground the proof. Compiler metadata
mostly source-only/pending; background refresh incomplete.

Lean failures were elaboration issues: explicit function arguments and real-to-
complex casts removed a dependent timeout; typed geometric sums avoided hidden
function inference; explicit denominator cancellation avoided expanding inverse
polynomials; `using!` resolved inherited complex module-instance diamonds.
No heartbeat/recursion-limit increases, added axioms, or numerical experiments.

## Remaining hard problem

The stronger uniform smooth local square law has a separate paper proof in
../2-fully-proven/bag-uniform-damping-height-square-law.md. Its Mellin inversion,
both residue contributions, original tails, all rectangle edges and uniform
small-damping limit still require Lean formalization. Literal full physical
contraction matching, growing profiles and the signed cubic near-resonant
aggregate are not closed by this source theorem. No generic quadratic-to-cubic
promotion is valid. Growing moments, moving cofactors, positive common-height
self-return and RH remain open.
