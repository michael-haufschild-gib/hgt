# Original causal source matching

Status: analytical bridge under Lean verification. RH remains open.

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
