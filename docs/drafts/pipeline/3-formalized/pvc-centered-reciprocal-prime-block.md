# Centered fractional parts on ordinary-prime blocks

**Route** PVC. **Stage** 3-formalized.

Uniformly for integers $1\le A\le B\le 2A$ and real $A^{999/500}\le Y\le A^{1001/500}$,
$$
\left|\sum_{A\le p<B}(\log p)\bigl(\{Y/p\}-\tfrac12\bigr)\right|\ll A^{999/1000}.
$$
The bound includes integral values of $Y/p$ and is uniform under changes of the sharp upper endpoint $B$.

**Proof.** Let $b(t)=(\{t\}^2-\{t\})/2+1/12$. Its cosine coefficients are $1/(2\pi^2k^2)$ for $k\ge1$, and its constant coefficient is zero. For any shift $h$, multiply the series at $Y/p+h$ by $\log p$ and sum over the block. Put $H=\lfloor A^{1/250}\rfloor$. For large $A$ and $1\le k\le H$, the frequencies $2\pi kY$ lie in $[A^{199/100},A^{201/100}]$. A constant rotation preserves the norm in the [reciprocal prime bound](pvc-reciprocal-ordinary-prime-block.md), so these modes contribute $O(A^{99/100})$ in total. The higher modes cost $O(A/H)$ by the Chebyshev mass bound and $\sum_{k>H} k^{-2}\le 1/H$. Thus the shifted sum of $b$ is $O(A^{249/250})$ uniformly in $h$.

For all real $y$, $(\{y\}^2-\{y\})/2\le(y^2-y)/2$, with equality on $[0,1)$. Applying this at $y=\{t\}+h$ gives $b(t+h)-b(t)\le h(\{t\}-1/2)+h^2/2$. Use both $h=\pm A^{-1/1000}$ and the positivity of the prime weights. The two errors are $O(A^{997/1000})$ from the shifted sums and $O(A^{999/1000})$ from the quadratic remainder. Enlarge the constant on bounded $A$.

**Lean.** [`centered_fractional_reciprocal_prime_block`](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsOfReciprocalPrimes.lean).
