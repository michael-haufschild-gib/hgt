# Original causal source matching

Status: bridge formalized in Lean. RH and Hawking-clock extinction remain open.

Target: identify the complete canonical temporal/metric/QNM value with a
receiver derived from the original static-time source and its original radial
counterterms. The unit-source receiver is excluded by DN35; that no-go does
not exclude a receiver retaining the forcing.

Write `w = physicalFundamentalFrequency q side`, `s = physicalRate q br`,
`mu = physicalAngularParameter q^2 - 1/4`, `C = physicalSelfSourceCoefficient q`,
and let `M,X,Y` be the original scalar, tortoise and forcing periods from DN31.

[BRIDGE] The full action is the ordinary convergent causal integral

`-mu*C * integral_{u>0} chi(u)*exp((2*s-w)*u)*((mu-2)*(X-u*M)+Y) du`.

The integrand must be attached to the limit of the original spatial source
cutoff, whose factor is `(mu-2)*(tortoise(z)-u)+w/z`. The time coordinate is
the original static time `u-tortoise(z)`. No finite counterterm may be changed.

Proof mechanism: establish `Re(2*s)<Re(w)` for all four physical branch/side
choices; differentiate the genuine onset integral to obtain its first time
moment; take the original three spatial finite-part limits; apply DN31.
This is a derived bridge, not a new primary conjecture.

Whole-route test: this supplies a source-derived causal observable, not an
identification of that observable with the retarded field itself or with a
Hawking-clock extinction functional. Those stronger identifications must not
be inferred from the scalar transform formula.

## Exact argument

For `rho = q.1`, the four values of `w-2*s` are
`3-5*rho/2`, `2-3*rho/2`, `1+3*rho/2`, and `5*rho/2`.
Their real parts are positive because `0<Re(rho)<1`. This statement concerns
the two physical fundamental QNMs, not arbitrary overtones.

Set `F_w(u)=chi(u)*exp((2*s-w)*u)`. On the frequency ball of radius
`d=(Re(w)-Re(2*s))/2`, the differentiated kernel is bounded by
`u*exp(-d*u)`. This is integrable on the positive ray. Consequently the
fixed-source frequency derivative is exactly `integral -u*F_w(u) du`.
The continued onset agrees with this ordinary transform on an open
neighborhood of the actual QNM.

Let `M_e,X_e,Y_e` denote the three original subtracted spatial integrals
from DN31. At each positive cutoff, the static-time source density and its
counterterms factor as

`-mu*C*chi(u)*exp(2*s*u)*((mu-2)*(X_e-u*M_e)+Y_e)`.

In particular the logarithmic counterterm contains
`(log(e)/2-log(2)-u)/(w+1)-1/(2*(w+1)^2)`. The forcing retains both
`F(0)*e^w` and `w*F'(0)*e^(w+1)/(w+1)`.
The original three cutoff limits select the claimed profile at every `u`.
Integrating that profile in time and using the two genuine onset moments
gives exactly DN31's complete action. No interchange of pointwise limits
and integrals is assumed in this argument.

## Lean certificate

[OriginalCausalSourceMatching](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCausalSourceMatching.lean)
proves `physicalFundamentalFrequency_time_chamber`,
`causalOnset_integrable_hasDerivAt`, `physicalOnset_time_moments`,
`canonicalCausalSourceCutoff_tendsto`, and
`canonicalCausalSourceProfile_laplace`.
The last two theorems quantify over every actual Xi copy, both source branches,
both fundamental QNMs and arbitrary source amplitude, without a matching or
RH premise. Scratch verification, isolated exact-module audit (128 seconds,
two jobs), and repository formal lint passed. The module is wired into the
RHTower umbrella; no umbrella build was run.
