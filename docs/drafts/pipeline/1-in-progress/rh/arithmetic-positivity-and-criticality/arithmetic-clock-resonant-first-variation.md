# First variation at arithmetic endpoint coincidences

- **Status:** frozen F [BRIDGE] proved; continuing clock problem remains in progress
- **Certificate:** [full paper proof, Lean declarations, and exact scope](../../../3-formalized/arithmetic-clock-first-variation.md)
- **RH dependency:** the logarithmic-clock conjecture C remains open; even C would leave the independent unit-remainder constraint missing.

## Question retained from the source limit

The constant-speed prefix is exactly zero when a complete phase turn ends at an integer. Its source-scaling limit supplies no sign there. The frozen first-variation identity retains both the changing arithmetic quadratic and the transported weight; it does not replace C, D1, or E.

## Frozen statement

Put `b(v)=(fract(v)^2-fract(v))/2`, `q_h(v)=(exp(h*v)-1)/h` for `h>0`, and

`J_h=integral_(0..m)b(q_h(v))*exp(-(sigma+1)*h*v)*sin(lambda*v) dv`.

For fixed `sigma>=-1`, positive integers m and K, `0<lambda<2*pi`, and `lambda*m=2*pi*K`, the frozen conjecture was

`lim_(h->0+) J_h/h = Q(sigma,lambda,m) < 0`.

Let

`c(lambda)=cos(lambda/2)/lambda^2 - 2*sin(lambda/2)/lambda^3`.

The proposed exact coefficient is

`Q = m/[2*sin(lambda/2)] * [(sigma+2)*c(lambda) + lambda*c'(lambda) - (lambda/2)*c(lambda)*cot(lambda/2)]`.

This claims a first-order limit, not a uniform error bound in m or lambda, and not a sign theorem for every positive h. At reciprocal-integer h it settles the large-cutoff sign of precisely the zero-margin prefixes omitted by the present scaling theorem.

## Resolution and next mathematical obstruction

F is now proved in Lean, including the interchange of the right clock derivative and the integral at all integer slope jumps. Exact parameter differentiation of the finite cosine prefix evaluates the two required moments. Their combination is strictly negative for every permitted sigma and frequency, including the undamped boundary. The simplified coefficient is

`Q=m*[(1-sigma)/lambda^3 + sigma*cos(lambda/2)/(2*lambda^2*sin(lambda/2)) - 1/(4*lambda*sin(lambda/2)^2)]`.

At reciprocal-integer acceleration, the theorem applies to the literal anchored source integral. Combining the integer case with the prior noninteger case gives eventual strict negativity for every fixed positive complete prefix. All endpoint cases are covered, but the cutoff can depend on the number of turns. An all-prefix law at a single finite cutoff would need new uniform information; the present theorem does not provide it. C, B2, D1, E, and R remain unproved, and none of them alone supplies the unit-remainder constraint at every zero.

No new computation was needed. The trigonometric sign ingredient occurs in literature; the certificate records that audit. No radical new RH architecture or global literature novelty is claimed.
