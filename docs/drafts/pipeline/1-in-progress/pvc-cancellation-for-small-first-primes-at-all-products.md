# Cancellation for small first primes at all products

**PVC · Conjecture.** For logarithmic cutoffs, every first prime $p\le X^c$,
for some fixed $c>0$, can be omitted from the coprime product row at
square-root precision up to logarithms, uniformly in the lower endpoint $Y$.

Write $T=\lfloor X/p\rfloor$. For $v<T^{0.49}$ use the pointwise bounds on
both weights. For $v>T^{0.51}$ group by $\lfloor T/v\rfloor$. There are
$O(T^{0.49})$ such quotients, and the inner jump has bounded interval sums.
Both bounds survive a cut at $Y/p$. In the intervening band, expand the inner
jump into its divisor tests $e\mid v$ and the outer weight into centered
fractional parts. The reciprocal phase for $v=et\asymp V$ is $hT/(det)$.
On each dyadic interval the integer second derivative estimate bounds its
sum by
$O(\sqrt{hT/(dV)}+\sqrt{dV^3/(hT)}/e)$.
For $T^{0.49}\le V\le T^{0.51}$ and polylogarithmic $d,e$, this is
$O(|h|^{1/2}T^{0.27})$ for every nonzero integer $h$. When the lower
curvature exceeds one, the trivial length bound already suffices. In the
[smoothed sawtooth decomposition](../../../../formal/GaloisForLFunctions/HTGeometry/SmoothedSawtoothFourier.lean)
both nonzero Fourier coefficient bounds, multiplied by $|h|^{1/2}$, are
$O(\Delta^{-1}|h|^{-3/2})$. The zero mode costs $O(\Delta V)$. The choice
$\Delta=T^{-0.04}$ bounds the whole dyadic fractional-part sum by
$O(T^{0.47})$. Summing the
first factors up to a sufficiently small fixed power preserves square-root
precision. The [shared-prime slice bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean)
handles the coprimality condition.
