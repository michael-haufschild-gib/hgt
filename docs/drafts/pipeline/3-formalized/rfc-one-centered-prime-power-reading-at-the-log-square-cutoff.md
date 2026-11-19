# One centered prime-power reading at the log-square cutoff

- **Stage** 3-formalized
- **Question** Does the full square-root criterion reduce to one explicit sequence of centered prime-power readings?

Put \(b(X)=\lfloor\log(X+1)\rfloor^2\), \(\mu_y(n)=\mu(n)1_{(n,P(y))=1}\), and \(L_y(X)=\sum_{n\le X}\mu_y(n)\log n\). There is an equivalence of the full Mertens power bounds above one half with the same family of bounds on
\[
 \sum_{m\le X/b(X)}\mu_{b(X)}(m)
 \left(\psi_{b(X)}(X/m)-b(X)\left\lfloor\frac{X}{b(X)m}\right\rfloor\right).
\]
Here \(\psi_y\) counts prime powers with base greater than \(y\), with Mangoldt weights. The readings occur at actual integer quotient endpoints.

**Weight inversion.** For every nondecreasing cutoff \(b\) and nondecreasing weight \(v\) with \(v(1)>0\), suppose the single frozen diagonal satisfies \(|\sum_{k\le n}\mu_{b(n)}(k)v(k)|\le C v(1)n^s\), \(s>0\). Then every row with \(y\ge b(n)\) satisfies \(|M_y(n)|\le C E_s(y)n^s\), where \(E_s(y)=\prod_{p\le y}(1-p^{-s})^{-1}\). At the base \(y=b(n)\), partial summation prices the smaller endpoints by \(C E_s(y)n^s(v(n)-v(1))\). Adding the diagonal reading fits exactly inside \(C E_s(y)n^s v(n)\). Above the base, adding a prime costs a smaller row at \(\lfloor n/p\rfloor\), covered by the new Euler factor. Induct first on \(n\), then on \(y\). Undoing the prime cutoff costs one further \(E_s(b(n))\). For the logarithmic weight use \(v(k)=\log(\max(2,k))\); its extra term is exactly \(\log 2\) at the unit. Conversely a full power bound controls every frozen row by Euler deletion and its log-weighted sum by partial summation.

**Exact centering.** The reading plus \(L_y(X)\) equals \(-y\Psi(\lfloor X/y\rfloor,y)\). Rankin's inequality bounds \(\Psi(T,y)\le T^s E_s(y)\), including prime powers. At every \(y\le b(X)\), the entire smooth term costs \(O_\varepsilon(X^{1/2+\varepsilon})\). Thus bounding the single signed reading suffices. Its square-root estimate remains open.

**Lean.** `exact_centered_prime_power_remainder` and `smooth_main_term_paid_at_the_log_square_cutoff` establish the decomposition and the uniform square-root price of its smooth term. `full_prefix_from_one_weighted_reading` proves the weighted inversion. `square_root_iff_one_centered_prime_power_reading` gives the equivalence at every exponent one half plus epsilon. [Exact centering](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/CenteringThePrimePowerReadingsAtTheirQuotientFloors.lean) · [Weighted inversion](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/InvertingAWeightedReadingAtAMovingPrimeCutoff.lean) · [Single reading criterion](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/OneCenteredPrimePowerReadingAtTheLogSquareCutoff.lean)
