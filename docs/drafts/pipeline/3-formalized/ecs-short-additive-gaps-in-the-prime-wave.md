# Short additive gaps in the ordinary-prime covariance

Write $a_t(p)=(\log p)\Phi(t-\log p)/\sqrt p$ for the atom of the continuous critical state. For every sufficiently large real $t$ and every integer $K\ge1$,
\[
 \sum_{1\le d\le K}\sum_{p,\ p+d\text{ prime}} |a_t(p)a_t(p+d)| \ll_\Phi K.
\]
In particular all gaps up to $o(t)$ together have lower order than the equal-prime contribution, which is asymptotic to $t$. The implied constant is uniform in both $t$ and $K$.

**Counting.** In the shell $e^{v-1}<p\le e^v$ the total number of pairs over $1\le d\le K$ is $O(Ke^v/v^2)$ uniformly for large $v$. In the averaged Selberg pair sieve take $P_1=2$, $h=\lceil e^{v/256}\rceil$, $z=h^{36}$. Every prime in the shell exceeds $h$. The level inequality is an equality. Mertens' lower bound gives $\exp(S(h)-S(2))\gg\log h\ge v/256$. The summed remainder is at most $2Kz^3\ll Ke^{v/2}$, absorbed since $v^2\ll e^{v/2}$.

**Weights.** The state vanishes on the positive ray, so only $p>e^t$ contribute. For $q\ge p>e^{v-1}$, confinement gives $|a_t(q)|\le C e^{2t}(\log q)q^{-5/2}\le C e^{2t}(v-1)e^{-5(v-1)/2}$ for $v\ge2$. Each shell $v=t+j+1$ contributes at most $C'K e^{-4j}$. Summing this geometric majorant proves absolute convergence and the uniform bound. The remaining covariance involves primes farther apart than the chosen additive cutoff and subtraction of the polar terms.

**Lean.** `eventually_shellPrimePairs_log_square_le` proves the uniform counting estimate. `unique_shell_of_prime_pair` partitions every contributing pair. `riemannHypothesis_or_controlled_short_prime_pairs` gives the absolute covariance bound for the state forced by failure of RH. [Selberg count](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/CountingPrimePairsInLogarithmicShells.lean) · [Covariance bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ShortAdditiveGapsInTheOrdinaryPrimeWave.lean)
