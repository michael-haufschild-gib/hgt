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

For \(K\ge X^\delta\) with fixed \(\delta>0\), the prime number theorem with a logarithmic remainder replaces each bracket by \(X/m-K\). The total error is \(O_\delta(X/\log X)\), uniformly in the signed choices, since \(\sum_{m\le Z}1/m\le1+\log X\) and the proper-power population is sublinear by a fixed power. Divisor inversion gives \(\Psi(Z,y)=\sum_{m\le Z}\mu_y(m)\lfloor Z/m\rfloor\). If \(R_y(Z)\) counts the rough integers through \(Z\), the endpoint and rounding together give
\[
 \left|B-\frac XZ\Psi(Z,y)\right|
 \le 2\frac XZ R_y(Z)+O_\delta(X/\log X).
\]
As \(Z,y\to\infty\), \(R_y(Z)/Z\to0\) by comparison with any fixed primorial. The upper quotient contribution therefore measures the **positive** smooth proportion at the interior cofactor cutoff. A bound on the recombined reading forces the complementary signed charge with the opposite sign.

The first band is [formalized](../3-formalized/qfsb-signed-profile-through-the-first-prime-band.md). The remaining issue is the original exact floor center on the same sector. It is
\[
 y\sum_{m\le Z}\mu_y(m)
 \left(\left\lfloor\frac{X}{ym}\right\rfloor-\left\lfloor\frac K y\right\rfloor\right).
\]
Its difference from \(\sum_{m\le Z}\mu_y(m)(X/m-K)\) has size at most \(yR_y(Z)\). The two discarded remainders each lie in \([0,y)\). For \(y\le Z\le y^2\), \(yZ\le X\), this rounding cost is \(o(X)\) uniformly by zero prime density. On this range, the prime number theorem replaces every prime interval by its length with total absolute error \(o(X)\). Thus the same estimate survives independent signed multipliers of modulus at most one on all rough cofactors. At the log-square wall and \(Z=y^2\), the upper floor sector carries \((1-\log 2)X+o(X)\) even though the entire floor center is \(o(X)\).

For general moving \(Z\), the positive smooth fraction persists when \(\log Z/\log y\) stays bounded and disappears when this ratio tends to infinity. The precise question at smaller errors is how the signed fractional parts and the prime error in the displayed transposition cancel together. The square-root estimate for their sum remains open.
