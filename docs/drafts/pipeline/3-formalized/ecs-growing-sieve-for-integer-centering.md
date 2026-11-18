# A growing prime sieve for the integer reference

Let $N_P(t)=\delta_P^{-1}\sum_{(n,\prod_{p\in P}p)=1}n^{-1/2}\Phi(t-\log n)$, $\delta_P=\prod_{p\in P}(1-1/p)$ and $A=\int e^{-u/2}\Phi(u)du$. Uniformly over all subsets $P$ of the primes at most $T^2$,
\[
\int_0^T|N_P(t)-Ae^{t/2}|\,dt\le T\exp(8\sqrt T+64T/\log T)
\]
for sufficiently large $T$. The right side is $e^{o(T)}$. For fixed $P$ the stronger absolute Cesàro limit is zero.

Write $E_P=N_P-Ae^{t/2}$. For $p\notin P$, the surviving multiples of $p$ have the form $pn$ with $n$ surviving $P$. Hence
\[
 E_{P\cup\{p\}}(t)=\frac{E_P(t)-p^{-1/2}E_P(t-\log p)}{1-p^{-1}} .
\]
Each translate has no larger $L^1(-\infty,T]$ mass than the original. The local cost is $(1+p^{-1/2})/(1-p^{-1})=(1-p^{-1/2})^{-1}$. The unsieved error is integrable on the negative ray by exponential confinement and has $o(T)$ mass on $[0,T]$ by integer quadrature. This proves the fixed-sieve limit.

For $a=p^{-1/2}\le3/4$, $(1-a)^{-1}\le1+4a\le e^{4a}$. The Chebyshev half-power bound at $N=\lfloor T^2\rfloor$ gives $\sum_{p\le N}p^{-1/2}\le 2N^{1/4}+16\sqrt N/\log N$. For $T\ge3$, $T\le N\le T^2$. Multiplying the local costs yields the asserted exponent.

For any $\eta>0$, primes $p\le T^2$ have zero state weight on $[\eta T,T]$ for large $T$ since $2\log T<\eta T$. Thus both the ordinary-prime wave and the sieved reference use only integers coprime to the primorial on that interval. Including $2$ removes all odd additive gaps at once. Cancellation among the remaining pairs is open.

**Lean.** `sievedReferenceError_insert` and `sievedReferenceError_integral_le` give the exact recursion and product bound. `riemannHypothesis_or_quadratically_sieved_density_reference` supplies the critical-state reference. `eventually_ordinaryPrimeWave_eq_sieved` and `sifted_odd_gap_product_eq_zero` give the late support and parity conclusions. [Sieve recursion](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/SievingTheIntegerReferenceWave.lean) · [Product estimate](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Analysis/TheCostOfSievingAtTheSquareOfTheLogarithmicHorizon.lean) · [Critical-state bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/RemovingSmallPrimesFromTheDensityReference.lean).
