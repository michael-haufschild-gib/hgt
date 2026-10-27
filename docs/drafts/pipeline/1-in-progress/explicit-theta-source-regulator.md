# An explicit regulator for the positive theta trace

- **ID:** CDG-EXPLICIT-THETA-REGULATOR
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Common positive theta trace; quantitative xi canonical-factor bounds.
- **Count:** Unaccepted; no contribution claimed.

## Exact gap

The current common schedule chooses an index by testing the actual local
logarithmic error. It proves existence of one arithmetic sequence, but does
not give a closed regulator formula. A substantive successor would remove
that error-dependent choice while retaining the full joint moving window.
This removes the error-dependent choice. A closed regulator expression alone
does not provide a certified convergence rate or a numerical algorithm.

## Conjecture

Let `M_n` be the already defined positive cutoff derivative control and put

```
K_n = exp((n+1)^4) M_n,
eta_n = exp(-K_n).
```

Use `eta_n` directly in the positive theta curvature integral. Conjecture:
these literal readings recover every compact C² collided moment uniformly
for `|tau| <= n/2` and `j|L| <= 2 log(n+1)`, with no local-error test in the
regulator and no zero coordinates in the approximants.

The current error-tested moving theorem has passed its final source check
and transitive axiom audit. The explicit conjecture above remains unproved.

## Proposed analytic bridge

The needed new estimate is an unconditional expanding-disc bound

```
integral_(|s|<=R) |log|xi(s)||^2 <= C (R+1)^6
```

for all sufficiently large R, with one fixed C. The exponent is provisional;
any fixed polynomial suffices. Nothing will assume this estimate at the xi
endpoint. It must be proved, or the explicit-regulator conjecture remains open.

For `x>0`, `K>=4`, and `eta=exp(-K)`, split at `x=exp(-K/4)`:

- Above the split, `0.5 log(1+eta/x^2) <= 0.5 exp(-K/2)`.
- Below the split, `-log x >= K/4`, and the regularization error is at most
  `2(-log x) <= (8/K)(log x)^2`.

Consequently the local L1 error is bounded by the disc area times
`0.5 exp(-K/2)` plus `(8/K)` times the log-square integral. The actual xi
zero set is planar-null, so its totalized logarithm does not affect this
integral estimate. Multiplication by the cutoff Laplacian envelope cancels
`M_n` in the second term. The remaining factor is a polynomial times
`exp(-(n+1)^4+O(n^2))`, which tends to zero in the fixed moving window.
The first term also needs an explicit elementary bound after multiplication
by `M_n`; `M_n>=1` is available.

## Corpus ingredients read and remaining proof

`GaussianXiGrowthConstantDischarges` provides actual, uniformly quantified
bounds for the canonical residual, its normalized logarithm, and the total
canonical divisor mass, with the growth premise discharged by xi growth.
In particular, on a fixed inner fraction of the canonical disc, the
normalized residual logarithm has size `O(R^2)` and the divisor mass is
`O(R^2)`.

Proposed factor argument:

1. The exact canonical decomposition and residual normalization have now
   been read in `GaussianXiLogDerivativeGrowth`: its canonical factor is the
   inverse Blaschke factor, with norm `R/|a|` at zero. The residual has norm
   at least one at zero, and its normalized analytic logarithm vanishes there.
   Thus `log|xi|` is the residual logarithm minus the positive canonical-factor
   logarithms, with the Gaussian spelling equal by its definition to `-2 * RHTower.xi`.
   The elementary normalization identity and pointwise canonical majorant
   passed their scratch Lean check. The importing main leaf now also
   discharges the actual xi growth bound and passed its individual olean
   check and standard-axiom audit.
2. Bound each canonical-factor logarithm by
   `log(2R/|z-a|)` on an inner disc. Prove a uniform `O(R^2)` bound for its
   squared integral using planar integration. The existing
   `PlanarLogNormIntegrability` polar-coordinate proof was read as a method
   reference; it currently supplies L1, not this quantitative log-square bound.
3. The checked `HTGeometry.sq_log_le_four_mul` bounds the polar radial
   weight by `4S`; a scratch proof targets the translated planar kernel
   bound `integral max(0,log(S/|z-a|))^2 <= 8 pi S^2`.
   This bound is now checked in `HTGeometry/PlanarLogSquare.lean`.
   Weighted Cauchy–Schwarz (`HTGeometry.sq_sum_weighted_le`) and the
   `O(R^2)` divisor mass then give an `O(R^6)` bound for the sum of
   factor logarithms. These existing ingredient statements have been read;
   the finite weighted-kernel integral is now checked in
   `HTGeometry/PlanarLogSquareMass.lean`. Its application to actual xi is
   checked in `XiLogSquareIntegral.lean`, including the unconditional
   `exists_xi_log_square_polynomial_bound`. Its transitive axiom list contains
   only `propext`, `Classical.choice`, `Quot.sound`.
4. Add the residual logarithm and the actual normalization term. No zero
   separation or simplicity assumption is permitted.
5. Prove the regularization estimate and discharge it for actual xi.
6. Compose with the checked moving-square envelope and moving-tail theorem.
   Audit exact final transitive axioms.

The integral composition is now checked; the explicit-regulator endpoint
remains a proof obligation. `XiCanonicalLogBound.lean` contains the canonical
majorant and `XiLogSquareIntegral.lean` proves the actual polynomial bound.
The scalar-error and
exponential-control estimates passed their main-module check in
`HTGeometry/LogRegularizationSquareError.lean`. The actual local-error endpoint
`exists_explicitSourceLocalError_bound` now passes in `XiExpRegulatorError.lean`
with only `propext`, `Classical.choice`, `Quot.sound` in its closure. No explicit-regulator endpoint is yet certified.

## Novelty and calibration gates

The basic Poincaré–Lelong density is standard and cannot count. A generic
repackaging of current convergence also cannot count. Acceptance requires a
new arithmetic consequence from the explicit regulator, checked against
existing source contour reconstructions and explicit regularizations.

This construction remains a positive conjugate-diagonal trace and carries
no successor charge. Planted entire quartets retain their positive masses.
The result would not assert a prime-side upper bound, capacity payment,
zero simplicity, or RH.

## Exact polynomial integration draft

For canonical radius `R_n`, put `q_i(z)=max(0,log(2R_n/|z-i|))`,
`m_i=divisor(xi_G)(i)`, and `M=sum m_i`. The checked pointwise majorant is

```
|log|xi_G(z)|| <= 2A(R_n+1)^2 + sum_i m_i q_i(z)
```

on `|z|<=R_n/4`. Normalization `xi_G=-2xi` adds at most `log 2`.
Weighted Cauchy–Schwarz and the planar kernel bound imply

```
integral (sum_i m_i q_i)^2 <= M^2 * 8 pi (2R_n)^2.
```

Jensen already supplies `M<=A(2R_n+1)^2/log 2`. Since
`4(n+3)<R_n<4(n+3)+1`, the disc `|z|<=n+2` lies in that inner quarter.
The inequality `(u+v)^2<=2u^2+2v^2` and disc area then give
`integral_(|z|<=n+2) log|xi(z)|^2 <= C(n+1)^6` with one actual constant.
No zero separation or multiplicity bound is used. The finite-mass integration,
normalization transfer and final polynomial assembly are written in scratch,
and has passed Lean verification. The actual theta growth theorem discharges `A`.

For the regulator error, write `x=(n+1)^4` and `a=exp x`. Eventually `x>=16`
and `a>=4x`. With `M_n>=1`,

```
M_n exp(-a M_n/2) <= exp(-a/4) <= exp(-x),
M_n / (a M_n) = exp(-x).
```

Thus the proposed local error, multiplied by the cutoff control, is at most
`(pi(n+2)^2/2 + 8C(n+1)^6) exp(-(n+1)^4)`. This local rate is now Lean-checked in `XiExpRegulatorError.lean`. The remaining polynomial is absorbed by the existing Gaussian
source envelope in the joint moving window.

The final source-window assembly can use a fixed explicit majorant. For
`t=n+1`, `t^6<=exp(6n)` and `n+2<=2t`; hence

```
(pi(n+2)^2/2+8C t^6) exp(-t^4+50n^2+56)
 <= (2pi+8C) exp(-n^4+56n^2+62).
```

The right side tends to zero by the checked quadratic-exponential limit
composed with `n^2`. Multiplying by the already proved moment coefficient
`(2pi)^-1 4^(j+1) A_f^2` gives a uniform compact-current error. The checked
moving-tail theorem then yields the full collided formula. This assembly is
written through the full moving endpoint in scratch. That endpoint remains
unchecked and unclaimed.

## Arithmetic tail certification

A further strengthening can replace the unquantified omitted reference mass
by an existing arithmetic resolvent bound. The corpus already proves
`lorentzMassW_le_re_logDeriv_xi` and `lorentzMassW_le_log` in
`RHTower/LorentzianZeroMass.lean`; their exact statements have been read.
The public multiplicity bridge `tsum_xiZeroCopy_eq_zetaCarrier` and its
summability companion in
`ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean`
have also been read.

For `n>=1`, a zero omitted by `chi_n` has `|Im rho|>n`. Its reference term is
at most twice the width-n Lorentzian term. Thus the proposed certified tail is

```
sourceReferenceTail n <= 2 lorentzMassW n 0
 <= (16/n) Re (xi'/xi)(1+n)
 <= (16/n) (xiLineTwoLogDerivConstant + log(n+4)).
```

This uses only existing arithmetic estimates, preserves multiplicities and
requires no zero-counting premise. Composing it with the checked moving-tail
comparison would certify the full trace error by a vanishing source envelope
plus an arithmetic `O(log n/n)` bound. The application is not yet formalized
and is not a separate contribution or a constants improvement to count.
It supplies an error certificate needed by the proposed finite-input formula.
