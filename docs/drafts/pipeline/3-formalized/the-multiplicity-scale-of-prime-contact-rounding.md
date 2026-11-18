# A prime product in the denominator at every multiplicity

Write $d_{\rm ord}(mD_n)=U/V$ in lowest terms for $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$. Put $W_n=e^8(2n+1)^2$. For all positive $n,m$,
\[
  \prod_{W_n/3<p\le W_n/2}p\;\mid\; V.
\]
Consequently $\log V\ge n^2/12$ for every sufficiently large $n$ and every $m\ge1$. For some absolute $c>0$ and every $1\le m\le c\sqrt n$, the signed generator satisfies $\log(U/V)\le -n^2/24$.

At a lag $p$ in this window, $\log p>8+\log(n^2)$. Products internal to either sign vanish by disjoint spline supports. At mesh resolution $r$ the lower degree $j=12r$ has spline argument $\log4-5$. The upper argument lies between $3+\log(4/3)$ and $3+\log2$. Both are in $(-4,4)$, where the convolution spline is strictly positive. This row is strictly negative, so its floor is at most $-1$. Distinct primes have distinct valuations in the reduced generator. The prime number theorem gives log mass at least $W_n/12$. The [numerator estimate](prime-contact-products-at-small-multiplicity.md) gives $\log U=O(m^2)$ in the indicated range.

Lean proves `successorSquare_window_product_dvd`, `successorSquare_denominator_lower` and `small_multiplicity_exponential_decay`. [Prime valuations](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ReducedOrdinaryPrimeProducts.lean) · [Window and decay](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ANegativePrimeWindowAtEveryMultiplicity.lean) · [Original-radius section count](acs-original-sections-on-square-conductors.md)
