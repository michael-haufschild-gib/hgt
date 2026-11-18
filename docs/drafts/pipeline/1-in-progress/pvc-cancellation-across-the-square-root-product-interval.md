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

For both factors above $X^{1/1000000}$, let $P$ be the longer dyadic length
and $V$ the shorter. Partition the shorter interval into pieces of length
$H\le X^{1/4000000}$. Cauchy–Schwarz on each piece gives reciprocal phases in
the longer variable, with curvature of size $hXj/(dP^3 V^2)$ for
$1\le j<H$. Both product restrictions cut the longer sum to an interval.
The needed estimate is uniform over these pieces and the low Fourier harmonics
of the centered fractional part. Shared primes can be separated using
the [prime-multiple slice bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean).
