# Global arithmetic minimum classes: source audit

**Stage:** audit closed in Lean; the classwise RH producer remains open. **Frozen objective:** determine the actual infinite minimum classes before treating their labels as an additional constraint on zeros. RH remains unproved. [Complete certificate](../3-formalized/arithmetic-global-minimum-classes.md).

## Frozen conjecture E

Use the literal remainder and profiles defined in [arithmetic zero minimum classes](arithmetic-zero-minimum-classes.md). For every complex parameter with `sigma=Re(s)>0`, `s!=1`, not just zeros:

`p^(2 sigma) W_p -> -conj(s) sum_(n>=1)n^(-2 sigma-1)/12`.

Consequently, the first profile has an attained negative minimum and the second is unbounded below when `sigma>1/2`; the roles reverse when `0<sigma<1/2`. At every critical-line zero both profiles attain the same negative minimum. Thus the coarse finite/infinite label pattern encodes the normalization exponents. It cannot itself distinguish zeros from nearby nonzeros in either open half-strip.

## Source mechanisms and proof obligations

Corpus searches for periodic primitives, Bernoulli asymptotics, and zero-mean averaging suggest extracting the mean `-1/12` of `bernoulliPeriodic`. `PeriodicMeanZeroAveraging` and the elementary bounded-primitive construction in `CCMSawtoothDilationMean` supply the mechanism; their later applications are not part of this proposal. The actual remainder representation is already formalized in `EulerDeletionPowerSumRemainder`.

1. Integrate the centered periodic kernel to a bounded primitive. One integration by parts should prove `R_s(N)=-s N^(-s-1)/12+O_s(N^(-sigma-2))`. This weaker error than the earlier paper expansion is sufficient and must be independently proved.
2. Carry that explicit error through the absolutely convergent multiples sum defining `W_p`. No numerical limit or assumed asymptotic enters Lean.
3. The coefficient of `mu(p)p^(1-2 sigma)` in the first profile is strictly negative, since `Re(1/(conj(s)+1))>0`; the second exponent is `2 sigma-1`. Along `p=2q`, with odd primes `q` tending to infinity, `mu(p)=1`. Prove this supplies negative entries and divergence below on the growing side. Combine negative entries with decay on the other side.
4. At a critical-line zero use the already formalized strict finite undershoot below the limiting lower boundary to force actual global attainment, including ties.

## Falsification and positive residue

Check the sign of the Bernoulli mean, integer endpoint terms, conjugation, exceptional modulus zero, and both exponents. A failure of E must remain a failure of E; any weaker result is labelled `[BRIDGE]`. If E succeeds, the surviving information is the exact tail coefficient and the finite arithmetic structure of the minimizing indices and values. A further RH producer must constrain that information beyond the normalization-driven finite/infinite pattern. This audit supplies no such producer by itself and makes no literature novelty claim.

**Outcome of E:** proved in Lean, including the actual scaled remainder limit, global negative entries without a zero equation, finite minima below the decay exponent, unboundedness below above it, and attained equal minima at critical-line zeros. The `(0,0)` class contains no strip zero. The further exact survivor is `arithmeticMinimumClass_both_positive_iff`: at a strip zero, positivity of both labels is equivalent to critical-line location. This equivalence is an audit of the proposed classification; no independent law forcing both labels positive is proved.

**Closed paper proof and Lean status:** the centered periodic primitive has absolute value at most one and vanishes at integer endpoints. Its tail integral has norm at most `N^(-sigma-2)/(sigma+2)`. Multiplication by `s(s+1)(s+2)` gives the explicit ordinary-remainder error bound. In the multiples coordinate, the scaled weighted remainder has a fixed coefficient and the summable majorant `|s(s+1)| n^(-2 sigma-1)/(sigma+1)`, so dominated convergence supplies the claimed modulus limit. The sign and prime-product argument proves both strict sides. At the boundary the finite arithmetic undershoot lies strictly below every sufficiently late profile value, reducing the global minimum to a finite set. All these dependencies are checked in the three modules named in the certificate; no numerical input is used.
