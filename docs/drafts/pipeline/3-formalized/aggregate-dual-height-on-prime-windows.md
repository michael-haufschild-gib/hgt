# Aggregate dual height on prime windows

At center $T$ take the primes with $|\log p-T|\le32\log(T+2)$. Sum the natural dual section heights of $m(e_1+e_p)$ over these primes. RH is equivalent to this sum being at most $m^2\exp((1+\eta)T)$ at cofinally many multiplicities in arbitrarily late windows, for every $\eta>0$.

**Proof.** Under RH each dual height has zero quadratic coefficient. Conversely, finite summation gives the sum of $\max(-Q(e_1+e_p),0)$ as the coefficient. For $0<\sigma<1/2$, primes with deficit exceeding $p^\sigma$ each cost at least $\exp(\sigma T/2)$ at late centers. Taking $\eta=\sigma/4$ bounds their number by $\exp((1-\sigma/4)T)$. The one-sided prime-window theorem tolerates this many exceptions and forces all zero real parts below $1/2+\sigma$. Letting $\sigma$ decrease to zero gives RH.

**Open arithmetic estimate.** Control this nonnegative sum from ordinary prime contacts and the pole and jet radii. The bound permits exceptional conductors and uses a common multiplicity across each finite window. [Section mass criterion](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheTotalDualHeightInPrimeWindows.lean) [Prime windows with exceptions](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/ExceptionalLogarithmicWindows.lean)
