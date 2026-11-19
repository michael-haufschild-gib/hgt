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

At \(y=\lfloor\log(X+1)\rfloor^2\), take \(Z=y^2\). An integer through \(y^2\) has at most one prime factor greater than \(y\), counted with multiplicity. Its nonsmooth population is exactly \(\sum_{y<p\le y^2}\lfloor y^2/p\rfloor\). Rounding costs \(\pi(y^2)\), and Mertens' reciprocal prime sum on this interval tends to \(\log 2\). Hence the normalized upper quotient contribution tends to \(1-\log 2\), and the lower quotient contribution tends to its negative whenever the full signed reading is \(o(X)\). These are the sectors of the raw prime reading. In the original floor center, the upper sector equals
\[
 y\sum_{m\le Z}\mu_y(m)
 \left(\left\lfloor\frac{X}{ym}\right\rfloor-\left\lfloor\frac K y\right\rfloor\right).
\]
Its difference from \(\sum_{m\le Z}\mu_y(m)(X/m-K)\) has size at most \(yR_y(Z)\), since the two discarded remainders each lie in \([0,y)\). At the log-square wall and \(Z=y^2\), this is \(o(X)\). Thus the upper floor sector also carries \((1-\log 2)X+o(X)\), although the entire floor center is \(o(X)\). Subtracting the center cancels the linear term within the upper sector.

The entire first interval has an explicit profile. Uniformly for \(y\le Z\le y^2\) and \(X\ge yZ\), the normalized reading differs from \(1-\log(\log Z/\log y)\) by \(o(1)\) as \(y\to\infty\). The only rough cofactors through \(Z\) are the positive unit and the negative primes in \((y,Z]\). The prime number theorem approximates their interval readings uniformly above \(X/Z\). The reciprocal prime mass stays bounded, and the common endpoint costs at most \((1+\pi(Z))/Z\) after normalization. This proof also covers polynomial prime walls throughout the stated range.

For \(y^2\le X\le y^3\), take \(Z=\lfloor X/y\rfloor\). Then \(\lfloor X/Z\rfloor=y\) exactly, since \(X=yZ+r\) with \(r<y\le Z\). The upper sector now contains the entire rough Mangoldt reading. Its Dirichlet convolution with \(\mu_y\) gives the **negative** logarithmically weighted rough Möbius prefix. Thus one profile gives the positive upper charge at the log-square cutoff and the negative full bias in the polynomial range. For \(y\sim X^\theta\) with \(1/3<\theta<1/2\), that normalized bias tends to \(-1+\log((1-\theta)/\theta)\).

For general moving \(Z\), the positive smooth fraction persists when \(\log Z/\log y\) stays bounded and disappears when this ratio tends to infinity. The precise question at smaller errors is how the signed fractional parts and the prime error in the displayed transposition cancel together. The square-root estimate for their sum remains open.
