# The smooth population at an interior quotient cut

- **Stage** 1-in-progress
- **Question** How much signed mass has already crossed the quotient cut before the full prime reading cancels?

Freeze the prime wall at \(y\). For integers \(1\le Z\le X\), take \(K=\lfloor X/Z\rfloor\ge y\) and read the upper quotient indices
\[
 B=\sum_{K<q\le X} a(q)M_y(\lfloor X/q\rfloor).
\]
Keep the ordinary primes above \(y\) with their logarithmic weights and allow arbitrary signed choices bounded by \(\Lambda\) on the proper powers. Writing \(A(t)=\sum_{q\le t}a(q)\), the exact transposition is
\[
 B=\sum_{m\le Z}\mu_y(m)\,[A(\lfloor X/m\rfloor)-A(K)].
\]
Every cofactor beyond \(Z\) has quotient at most \(K\); every cofactor through \(Z\) has quotient at least \(K\). Both endpoints of the prime reading occur.

Write \(R_y(Z)\) for the number of rough integers through \(Z\). For every \(\Theta<s<1\), where \(\Theta\) is the zeta zero abscissa, both ordinary prime errors in each interval have size \(O_s((X/m)^s)\). The total possible change on proper powers has size \(O(\sqrt{X/m})\) per cofactor. Thus, for \(y\le Z\) and \(yZ\le X\), divisor inversion gives
\[
 \left|B-\frac XZ\Psi(Z,y)\right|
 \ll_s X^s Z^{1-s}+\frac XZ R_y(Z).
\]
Indeed \(\Psi(Z,y)=\sum_{m\le Z}\mu_y(m)\lfloor Z/m\rfloor\). Replacing \(X/m\) by \((X/Z)\lfloor Z/m\rfloor\) costs less than \(X/Z\) in each row, and the common lower endpoint costs at most another \(X/Z\). Dividing by \(X\), the first term is at most \(y^{s-1}\). The second tends uniformly to zero as \(y\to\infty\) by comparison with a fixed primorial. Lean proves the finite estimate and uniform decay in `quantitative_smooth_profile_at_every_interior_cut` and `raw_prime_profile_at_every_interior_cut`. [All interior cuts](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSmoothProportionAtEveryInteriorQuotientCut.lean)

This identifies the positive smooth proportion throughout the whole upper quotient range, including \(X/Z=X^{o(1)}\).

The first band is [formalized](../3-formalized/qfsb-signed-profile-through-the-first-prime-band.md). The original exact floor center on the same sector is
\[
 y\sum_{m\le Z}\mu_y(m)
 \left(\left\lfloor\frac{X}{ym}\right\rfloor-\left\lfloor\frac K y\right\rfloor\right).
\]
Its difference from \(\sum_{m\le Z}\mu_y(m)(X/m-K)\) has size at most \(yR_y(Z)\). The two discarded remainders each lie in \([0,y)\). For \(y\le Z\le y^2\), \(yZ\le X\), this rounding cost is \(o(X)\) uniformly by zero prime density. On this range, the prime number theorem replaces every prime interval by its length with total absolute error \(o(X)\). Thus the same estimate survives independent signed multipliers of modulus at most one on all rough cofactors. At the log-square wall and \(Z=y^2\), the upper floor sector carries \((1-\log 2)X+o(X)\) even though the entire floor center is \(o(X)\).

For general moving \(Z\), the positive smooth fraction persists when \(\log Z/\log y\) stays bounded and disappears when this ratio tends to infinity. The precise question at smaller errors is how the signed fractional parts and the prime error in the displayed transposition cancel together. The square-root estimate for their sum remains open.
