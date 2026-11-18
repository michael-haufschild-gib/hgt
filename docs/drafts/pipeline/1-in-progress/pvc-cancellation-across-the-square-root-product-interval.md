# Cancellation across the square-root product interval

**PVC · Conjecture.** For logarithmic cutoffs, remove the entire product interval
$Y<pv\le X^{1/2+c}$ at square-root precision up to logarithms, for some fixed
$c>0$ independent of the target exponent. Here $Y=(D+1)\lfloor\sqrt X\rfloor$
when this is below $X$.

For $v\le X^{1/1000000}$ the sharp reciprocal-prime band contains this interval
when $c\le10^{-9}$ and $X$ is large. For short $p$, expand the inner floor
increment into divisibility tests $e\mid v$ and set $v=et$. On $pet\asymp U$,
each harmonic has phase $hX/(dpet)$ in $t$. Its second derivative has size
$hX(pe)^2/(dU^3)$. The [integer reciprocal phase estimate](../../../../formal/GaloisForLFunctions/RHTower/DivisorTerminalModularMean.lean)
applies to every truncated dyadic interval.

For $P\ge V\ge X^{\eta}$ with $\eta=10^{-6}$, split the shorter dyadic
factor into intervals of length $H=\lfloor X^{\eta/2}\rfloor$. For coefficients
bounded by one, write $S_h$ for the bilinear sum of $e(hX/(dpv))$ with a sharp
product interval. Put $\rho=X/(dP^2V^2)$. Cauchy–Schwarz on each short
interval produces one long-variable exponential sum per pair of shorter
arguments. At gap $j>0$ its curvature is comparable to $|h|\rho j/P$.
The two product restrictions intersect in a single interval. The [reciprocal
second derivative test](../../../../formal/GaloisForLFunctions/RHTower/DivisorTerminalModularMean.lean)
and the trivial bound for curvature above one give
$$
\frac{|S_h|}{PV}\ll H^{-1/2}
 + (|h|\rho H/P)^{1/4} + (|h|\rho P)^{-1/4}\qquad(h\ne0).
$$
There are $O(V/H)$ short intervals. Each contributes at most $PH$ times
the displayed relative bound, including its diagonal $PH$ before the
outer Cauchy factor. Near the square-root product, $P\gg X^{1/4}$ and
$X^{-2c}/(Cd)\le\rho\ll1$. Hence the harmonic bound is
$O(PV\sqrt{|h|}\,X^{-\eta/4})$ up to logarithms. The smoothed sawtooth
estimate at $\Delta=X^{-\eta/8}$ then pays for the slab width $X^c$.
For shared primes above $X^\eta$, absolute counting costs
$O(X^{1/2+c-\eta}(\log X)^{O(1)})$. Formalization requires the masked
short-interval bilinear estimate with arbitrary bounded coefficients.
