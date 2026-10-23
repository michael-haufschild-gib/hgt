# The surviving nonunit cofactor sum

- **ID:** twin-prime-nonunit-cofactor-dispersion
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / BRIDGE
- **Source:** [compensated source](../3-formalized/twin-prime-compensated-damping-coefficients.md).
- **Statement:** Control the actual shifted correlation of the truncated Möbius dilation, with its complementary-divisor weights and all mixed terms retained.

## Exact object

Use the admissible schedule `epsilon_X=(1+log(X+2))^(-6)` and

`w_epsilon(m)=(1-m^(-epsilon))/epsilon`,

`V_(epsilon,Z)(n)
 = sum_(dm=n, 2<=m<=Z) mu(d)d^(-epsilon) w_epsilon(m)`.

The complete sum, with no cutoff, is exactly
`tau_epsilon(n)/epsilon` for `n>=2`. The omitted unit cofactor has
zero weight, not an estimated small weight. This is the finite-difference
counterpart of ACCE's Möbius--logarithm dilation.

The first candidate is the odd-source short-cofactor covariance

`C(X,Z)=sum_(2<=n<=X, n odd)
 V_(epsilon_X,Z)(n) V_(epsilon_X,Z)(n+2)`.

**Candidate:** for every fixed `0<delta<1/2`,

`sup_(2<=Z<=X^(1/2-delta)) |C(X,Z)| / X -> 0`.

This is an actual arithmetic estimate, not an assumed interface for
the twin-prime theorem. It concerns only one part of the complete
pair sum; even its proof would leave the two mixed terms and the
long-cofactor pair to be controlled.

## Attack before proof

1. **Finite geometry.** In the odd sum, every surviving cofactor is
   odd and greater than one. An incidence `ke-md=2` forces
   `gcd(m,k)=1`, hence `m!=k`. There is no equal-cofactor diagonal
   on this carrier. This says nothing about cancellation among
   the remaining incidences.
2. **Small affine face.** At `(m,k)=(3,5)`, the equation becomes
   `d=5t+1`, `e=3t+1`, with the parity restriction inherited from
   odd `n`. The coefficient retains both actual Möbius values.
   Absolute summation cannot provide `o(X)` even on this face.
   A fixed-form cancellation theorem, where available, does not
   give a bound uniform over growing `m,k`.
3. **Do not turn faces into necessary obligations.** An individual
   face can be hard while its sum with the other faces cancels
   exactly. The unit-cofactor identity is an explicit example.
   The candidate estimates the complete truncated row; it does
   not posit separate bounds for every face.
4. **Mixed terms remain.** Writing the full response as `V+R`
   leaves `VV+VR+RV+RR`. A small `VV` term alone yields no lower
   bound for the whole pair sum. Positivity of the complete source
   does not make `V` or `R` nonnegative.
5. **Balanced CRT estimate has limited range.** The existing
   paper bound controls divisors of size `sqrt(X)`. Here short
   cofactors can put both Möbius divisors far above that scale.
   The smooth coefficient is in the cofactor; it does not make
   either Möbius row smooth.
6. **RH criterion is insufficient as currently stated.** The
   receiver controls weighted prefix energy. No checked theorem
   extracts this literal shift-two covariance uniformly in the
   cutoff and shrinking damping. The common-kernel deletion
   certificate already shows why the aggregate RH criterion
   alone is too coarse for this deduction.

**Verdict: BRIDGE / UNPROVED.** This is a more selective analytic
target, not a novel theorem or a completed beyond-SOTA mechanism.
No counterexample or proof has been obtained. No assertion that
RH and twin primes are equivalent follows from these coordinates.

## Damping removed from the arithmetic input

The [uniform deformation estimate](../3-formalized/twin-prime-cofactor-damping-removal.md)
now has a complete elementary paper proof and five unconditional
Lean capstones with standard-axiom audits. Put

`U_Z(n)=sum_(dm=n, 2<=m<=Z) mu(d) log m`.

For every pair of cutoffs `Z,W>=2` with `ZW<=X`, the difference
between their damped and undamped normalized correlations is at
most `6/(1+log(X+2))`, also on the odd carrier. This uses the
literal CRT count `N_X(m,k)<=2X/(mk)+1`, including its endpoint
error, and no Möbius cancellation assumption.

Consequently the candidate can now be attacked with the fixed
arithmetic row `U_Z` alone. The same faster schedule still resolves
the full prime-pair observable by the proved pointwise diagonal
error. This changes an auxiliary clock, not the target conjecture.
The earlier `log^(-4)` candidate has not been refuted; that clock
does not make this particular absolute deformation bound vanish.

**Remaining estimate:** for every fixed `0<delta<1/2`,

`sup_(2<=Z<=X^(1/2-delta))
 |sum_(2<=n<=X,n odd) U_Z(n)U_Z(n+2)| / X -> 0`.

The estimate remains unproved. The deformation bound resolves
parameter uniformity, not the signed arithmetic correlation or
its mixed/long-cofactor companions.

There is now a smaller-range
[paper deduction](../2-fully-proven/twin-prime-polylogarithmic-affine-cancellation.md).
For some absolute `kappa1,c1>0`, the actual odd-source covariance
is `O(X/(log X)^c1)`, uniformly for `2<=Z<=(log X)^kappa1`.
The proof tracks growing-modulus constants in the ordinary
two-point source, pays the Möbius squarefree projection, and
sums the logarithmic cofactor weights with every endpoint cost.
This is not yet Lean-certified; no analytic input is assumed
in Lean. The polynomial cutoff target above, mixed terms,
long-cofactor pair and positive twin-prime mass remain open.

## Dependency and novelty audit

Corpus search `Möbius correlation affine linear forms nonunit
cofactors determinant shift` returned exact truncated-divisor
pair expansions, a window-energy theorem with a correlation
premise, and definitions of binary Möbius correlations. None
supplies the candidate. The correlation-premise theorem is not
used as an unconditional input.

The search also returned `abs_truncAF_conv_le_log` in
`RHTower/Sieve/VaughanTypeIPieces.lean`; its source was checked.
It bounds `Lambda_truncated * mu_truncated`, using positivity
and `Lambda*1=log`. The present row is `mu*(log_truncated)`.
Those are different truncations, so its pointwise logarithmic
bound is not an available estimate for `U_Z`.

Checked ACCE source:
`TheTangentFactorsThroughTheMoebiusDilation.lean`, especially
`sum_divisors_dampedMoebius_mul_dampedLog` and
`prefixDilation_dampedPrime_factor`. These justify the common
language, not the missing shifted estimate.

The current external fixed-affine and determinant interfaces
are recorded in the [signed determinant audit](twin-prime-consumed-mark-determinant.md).
No new external novelty claim is made. A precise parent-theory
comparison must precede any such claim for a surviving estimate.

The newly available SAEI source
`FrustrationIsPaidAlongCanonicalPaths.lean` was also inspected.
Its positivity theorem requires a concrete positive gauge, signed
supersolution, paths, edge shares and their proved packing bounds.
None has been constructed for this source at the required scale.
Passing a `PathCertificate` as an unproved input would merely hide
the missing estimate and is not an allowed proof of the candidate.

The later SAEI source `TheOddWeilLedgerIsFrustratedOnlyByPrimes.lean`
was checked at `oddFold_pos_imp_primeSum` and
`frustrated_walk_has_primeSum`. It locates a necessary prime-power
atom on every frustrated odd-ledger cycle. It does not force two
such atoms to have additive difference two, or estimate the above
Möbius dilation on that correspondence. The sign geometry alone
therefore supplies no missing fixed-shift lower bound here. No
new obstruction theorem or failed route is claimed by this audit.

The [fixed-determinant audit](twin-prime-fixed-determinant-uniformity.md)
isolates a further possible route. Parity restriction gives primitive
affine forms with determinant four, but growing slopes still produce
a growing progression modulus. A fixed determinant alone does not
remove that source of nonuniformity.

The corpus's `UniformCofinalMobiusPrefixDiscrepancy.lean` was
also checked at its exported statement and proof. Its unconditional
`cofinal_moebius_source_prefix_sublinear` controls the signed first
moment of `s_N(k)=sum_(d<=N,d|k) mu(d)`, with `N` and the prefix
horizon growing independently. Its quotient-window argument uses
unweighted Möbius prefixes. In the present covariance, the second
shifted row remains inside those windows; the theorem supplies no
bound for that weighted expression. No first-moment estimate is
being promoted to a two-row correlation estimate.

## First proof obligation

**[OPEN CORE]** Find a signed estimate for the complete truncated
Möbius dilation on the determinant surface, uniform at the stated
cutoff. Preserve both arithmetic rows through any energy or
Fourier step. A bound for arbitrary coefficient envelopes must
be tested against the explicit full-height counterexample.

The elementary Fourier-energy route does not supply the saving.
For the finite row `v(n)=V_(epsilon_X,Z)(n)` and
`F(theta)=sum_n v(n) exp(2 pi i n theta)`, the shifted correlation
is the second Fourier coefficient of `|F|^2`, with the finite
interval boundaries retained. Parseval controls its absolute value
by `sum_n |v(n)|^2`; it does not make that coefficient small.
Likewise a hypothetical bound `sup |F|<=X/log^A X` combined with
an energy bound `sum |v|^2<=X log^B X` yields only
`X^(3/2) log^(B/2-A) X` via `||F||_infinity ||F||_1`.
This calculation is a diagnostic, not an assumed Fourier theorem
or a claimed obstruction to every spectral method. The missing
information is the angular distribution of the actual squared
Fourier transform, beyond its size.

For fixed `Z` and positive damping, absolute Dirichlet convergence
on `Re(s)>1` gives the exact generating function

`sum_n V_(epsilon,Z)(n)n^(-s)
 = (sum_(2<=m<=Z) w_epsilon(m)m^(-s))/zeta(s+epsilon)`.

Indeed the finite outer sum may be interchanged, and the remaining
Möbius series is the reciprocal zeta series in its absolute half-plane.
This identifies the same damped reciprocal and finite dilation
used by the RH research. It does not control a fixed additive
Fourier coefficient or justify continuation at a growing cutoff.

One possible mechanism is to sum the cofactor weights before
dualizing the modulus variable, as in the earlier partial-mark
aggregation. It is not yet a proved inequality. Reindexing alone,
or a claimed contraction with no paid error term, does not close it.

## Gates

- [x] Exact candidate, carrier, normalization and failure tests.
- [x] Internal dependency statements checked.
- [ ] Source-specific arithmetic estimate.
- [ ] Complete paper proof with no open dependency.
- [ ] Unconditional Lean certificate; no analytic premise added.

## Log

- 2026-10-23 — Retained the nonunit source after exact endpoint
  compensation. Infinitude and the candidate estimate remain open.
