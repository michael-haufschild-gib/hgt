# Independent prime asymptotics on the physical state

Let $\Phi$ be the continuous representative of a confined critical state. Write $P_k(t)=\sum_p(\log p)p^{-k/2}\Phi(t-k\log p)$.

**Claim.** As $t\to\infty$,
$$
e^{-t/2}P_1(t)\longrightarrow\mathcal L\Phi(-1/2),\qquad
P_2(t)\longrightarrow\tfrac12\mathcal L\Phi(0).
$$
More generally, for every fixed real $k\ge1$,
$$
e^{(1/2-1/k)t}P_k(t)\longrightarrow k^{-1}\mathcal L\Phi(1/2-1/k).
$$
The entire proper-prime-power wave $\sum_{k\ge2}P_k(t)$ tends to $\mathcal L\Phi(0)/2$.

**Proof.** Let $N(v)$ be the least integer $n\ge1$ with $\vartheta(n)>v$ for $v\ge0$. Then $\vartheta(N(v)-1)\le v<\vartheta(N(v))$. The prime number theorem and $N(v)\to\infty$ imply $N(v)/v\to1$. For $x>0$ the reading $N(xy)/x$ is $p/x$ on the interval $[\vartheta(p-1)/x,\vartheta(p)/x)$ of length $(\log p)/x$. Thus every continuous $g$ with $|g(u)|\le C/(1+u^2)$ satisfies
$$
\frac1x\sum_p(\log p)g(p/x)=\int_0^\infty g(N(xy)/x)\,dy\longrightarrow\int_0^\infty g(y)\,dy.
$$
Indeed $N(xy)/x\to y$ for $y>0$, and $\vartheta(n)\le (\log4)n$ gives an integrable majorant $C(1+\log^2 4)/(1+y^2)$.

Take $x=e^{t/k}$ and $g(y)=y^{-k/2}\Phi(-k\log y)$ for $y\ge1$, zero below $1$. This test is continuous since $\Phi(0)=0$. The bound $|\Phi(u)|\le C e^{2u}$ gives $|g(y)|\le C y^{-5k/2}$ for $y\ge1$. The substitution $u=-k\log y$ identifies its integral with $k^{-1}\mathcal L\Phi(1/2-1/k)$.

For $k\ge3$, $\sum_{p,k}(\log p)p^{-k/2}<\infty$. The state is bounded, and every fixed summand vanishes once $t\ge k\log p$. Dominated convergence removes the entire cubic-and-higher tail, leaving the square limit.

This proves signed ordinary-prime cancellation at polar scale directly from $\vartheta(x)/x\to1$. ECS still requires control of the error below every positive exponential rate.

**Lean declarations**

- `tendsto_dilated_ordinary_prime_sum` proves the scaled prime measure limit on the full positive ray. [Dilated ordinary-prime measure](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/DilatingTheOrdinaryPrimeMeasure.lean)
- `criticalState_primePowerLayer_asymptotic`, `criticalState_ordinary_and_square_prime_limits` and `criticalState_tendsto_properPowerWave` give the layer formula, the ordinary-prime and square limits, and the limit over all proper powers. [Prime number theorem on the state](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ThePrimeNumberTheoremOnTheState.lean)
