# The exact image of polynomial Stepanov syzygies

- **ID:** alst-stepanov-image-fixed-ideal
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For `q≥2`, the integer auxiliaries `Σ_i f_i ψ_q(g_i)` obtained from global mixed first-factor syzygies of every order below `r` are exactly the ordinary ideal power `(X_j^q−X_j : j∈σ)^r`.

## Mathematical purpose
The fixed torus omits coordinates equal to zero. A polynomial construction
may therefore obey a stronger algebraic constraint than torsion vanishing.
Classifying its image would identify precisely which auxiliaries the
syzygy method can construct, including its forced vanishing off the torus.
The expected least arithmetic length is `p_min^(qr)`, attained by
`(X_p^q−X_p)^r`, rather than the torsion-only threshold `p_min^((q−1)r)`.

## Proof route to audit
Represent the paired family by a polynomial in two copies of the variables.
Global derivative syzygies should mean membership in the `r`th power of the
diagonal ideal. Integral Taylor coefficients must justify this without
dividing by factorials. Substitute the second copy by `X^q` to obtain the
fixed-point ideal power. Conversely, diagonal differences give its generators;
products supply every order. Euler and ordinary polynomial syzygies must be
proved equivalent, including coordinate hyperplanes.

## Evidence and open obligations
The corpus supplies torsion-grid ideal descent and mixed Euler transfer,
but the searches for Adams fixed-point polynomial ideals and diagonal Taylor
syzygies have not found this image classification. This is a lead, not a
completed novelty audit. The integral diagonal statement, converse image,
sharp length, and boundary cases remain unproved. Nothing is counted.

The origin-ideal support criterion is already available as
`MvPolynomial.mem_pow_idealOfVars_iff'`. A denominator-free route is to
induct on the order: the constant coefficient is evaluation at zero; each
positive exponent is detected by `coeff_pderiv`, whose positive integer
factor is cancellable over the polynomial coefficient ring. Translating
the first variables by the second then identifies the diagonal filtration.
