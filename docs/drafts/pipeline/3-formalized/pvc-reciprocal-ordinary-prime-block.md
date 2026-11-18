# Cancellation of reciprocal phases over ordinary primes

**Route** PVC. **Stage** 3-formalized.

Uniformly for integers $1\le A\le B\le2A$ and $A^{199/100}\le S\le A^{201/100}$,
$$
\left|\sum_{A\le p<B}(\log p)e^{iS/p}\right|\ll A^{99/100}.
$$
These are the low Fourier modes of the centered reciprocal fractional parts in the prime band near the square-root horizon.

**Proof.** In the unconditional Vaughan bound `exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power'`, put $T=S/r$ and let $r\downarrow0$. Each $T\log(1+r/n)$ tends to $S/n$. The finite sum passes to the limit, and the bound depends on $T,r$ only through $S$. Choose $U=\lceil A^{11/20}\rceil$, $V=\lceil A^{1/20}\rceil$. For large $A$, $U<A$, $UV\le A$, $10^{27}A\le S$, and $S(UV)^3\le64A^{381/100}\le72\pi A^4$. The five terms in the bound, before its logarithmic factor, have exponents at most $581/600$, $101/200$, $39/40$, $391/400$, and $29/40$ in $A$. Each ceiling is between its argument and twice its argument. All five exponents are below $49/50$. Absorb $(1+\log(2A))^4$ into $O(A^{1/100})$. Proper prime powers contribute $O(\sqrt A)$ in absolute value by the Chebyshev prime-power decomposition. Increase the constant on bounded $A$.

**Lean.** `reciprocal_mangoldt_block` gives the full Mangoldt sum. `reciprocal_ordinary_prime_block` gives the ordinary-prime sum. [Reciprocal phase bounds](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/ReciprocalPhasesNearTheSquareRoot.lean)

**Application.** The [centered fractional-part bound](pvc-centered-reciprocal-prime-block.md) sums the Fourier modes at each original horizon.
