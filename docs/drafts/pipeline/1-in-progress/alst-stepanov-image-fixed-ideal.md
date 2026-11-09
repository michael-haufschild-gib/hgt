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

## Formalized input
`IntegralDiagonalJets.polynomialVanishesToOrder_iff_mem_pointIdeal_pow`
identifies ordinary jets with the point-ideal power over any characteristic-zero
domain, including integer polynomial coefficient rings. Its plain Lean check
and axiom audit passed; the image classification and sharp length remain open.
`EulerJetsDetectTheDiagonal.polynomialEulerVanishesToOrder_iff_mem_pointIdeal_pow`
also passes: nonzero point coordinates suffice, even if they are not units
of the coefficient ring. Thus the tuple of coefficient indeterminates
detects the diagonal ideal integrally through Euler jets.

## Image mechanism
For `Q(U,V)=Σ_i f_i(U)g_i(V)`, the diagonal Euler jets equal the original
moment polynomials. The substitution `U↦X`, `V↦X^q` is surjective because
every integer polynomial lifts through the `U` variables. It sends each
diagonal generator `U_j−V_j` to `X_j−X_j^q`; ideal images commute with
powers. Conversely, every bivariate polynomial is a finite paired sum,
by expansion in the outer monomials. These facts give the proposed image
classification for every `q`, including `0` and `1`; the sharp length
statement still requires `q≥2` and a separate filtration argument.

## Filtration route
For generators `G_p` with arithmetic leading monomial `X_p^q` and coefficient
one, use `B_a=∏_p X_p^(a_p mod q) G_p^(a_p div q)`. Arithmetic triangularity
gives an integral basis preserving length. Multiplication by `G_p` shifts
the index by `q e_p`, so the `r`th ideal power should retain exactly the
indices with `Σ floor(a_p/q)≥r`. For `G_p=X_p^q−X_p`, this would yield the
sharp cost and its least-prime minimizer. This filtration claim still
requires a proof; it is not inferred from the generator degrees alone.
