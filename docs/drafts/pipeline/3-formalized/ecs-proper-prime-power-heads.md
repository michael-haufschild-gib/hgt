# Proper prime powers in the ECS prime wave

- **ID:** ecs-proper-prime-power-heads
- **Stage:** 3-formalized
- **Source:** ECS Q8, beyond-the-wall prime continuation.

Let $P_{\ge2}(F,p)$ be the sum of the prime heads at $n=q^k$, $q$ prime and $k\ge2$. For every half-line energy profile this series is holomorphic on $\Re p<0$ and extends across every nonzero point of the imaginary axis. Its residue at zero is $-\mathcal LF(0)/2$, nonzero for a critical state. For the continuous representative $\Phi$ of a critical state and every $\varepsilon>0$,

$$
\sum_{q,\,k\ge2}\frac{\log q}{q^{k/2}}
       |\Phi(x-k\log q)| \le B_{\Phi,\varepsilon} e^{\varepsilon x}
       \qquad(x\ge0).
$$

**Proof.** On $\Re p\le\sigma<0$, the coefficient majorant sums because $(1/2-\sigma)k>1$ for the square row and the subsequent rows form geometric tails. Split each head at $-\log n$ into the full transform minus the lower tail. The confinement moment pays $O(n^{-4})$ for each translated tail, locally uniformly on $\Re p>-4$. The full transform multiplies the scalar Euler series for proper powers at $s=1/2-p$. Its square row is $-\zeta'/\zeta(2s)$ minus the proper powers at $2s$. The remaining rows converge absolutely for $\Re s>1/3$. At $p=0$ the polar term is $-1/(2p)$. Closed-right-half-plane nonvanishing gives $\mathcal LF(0)\ne0$ for the state.

In time, $|\Phi(u)|\le C e^{au}$ on its support for $a=\min(2,\varepsilon)$. Translation contributes $e^{ax}n^{-a}$, so the same summable Euler majorant pays the absolute wave. The signed cancellation between ordinary primes and the polar term remains open.

**Lean.** [TheProperPrimePowersInThePrimeWave.lean](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheProperPrimePowersInThePrimeWave.lean) proves the exact split (`primeHead_eq_prime_add_properPowerHead`), continuation (`differentiableOn_properPowerHead`, `properPowerHeadContinuation_eq`, `differentiableAt_properPowerHeadContinuation_of_re_zero`), pole (`riemannHypothesis_or_criticalState_properPowerHead_pole`) and absolute time bound (`criticalState_properPowerWave_subexponential`). The module passed its individual Lean check. All six axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.
