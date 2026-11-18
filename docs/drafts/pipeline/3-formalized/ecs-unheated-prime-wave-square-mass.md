# Square mass of the unheated prime wave

Let $F$ be the critical state at its positive threshold, $F^+$ its profile beyond the wall and $\Theta=\sup_{\zeta(\rho)=0}\operatorname{Re}\rho$. For every $d>\Theta-1/2$,
$$
\int_0^\infty e^{-2dx}|F^+(x)|^2\,dx<\infty .
$$
The same bound holds for the prime sum after polar subtraction,
$$
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}F(x-\log n)-e^{x/2}\mathcal LF(-1/2).
$$

On $\Theta-1/2<c<1/2$, the [reflected logarithmic moments](ecs-reflected-logarithmic-moments.md) pay for the regular Euler multiplier. The squared truncation weight on $u<-\ell$ satisfies $e^{2s(u+\ell)}\le e^{-8(u+\ell)}$ for $s\ge-4$, giving an $L^2$ prime-tail trace for $s>-4$. The Lévy head and the two charge terms also lie in $L^2$. Their sum gives ordinary square mass for the continued state on $\operatorname{Re}w=-8-c$.

In the reflected half-plane, divide the continuation by $(1+\varepsilon w)^2$ to absorb its quadratic growth. Poisson majorization followed by $\varepsilon\downarrow0$ bounds the Hardy norm by the boundary mass. After damping the Hardy datum to exponent one, its Laplace transform equals that of $e^{-x}F^+$. Laplace injectivity identifies the original datum with $e^{-cx}F^+$. Extra damping covers every $d>\Theta-1/2$. The physical prime-form identity gives the second bound.

Lean declarations: `integrable_norm_sq_stateMeromorphic_reflected_line`, `memLp_damped_beyondWallProfile_of_abscissa`, `memLp_damped_prime_sum_sub_pole_of_abscissa`. [Proof](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/TheLeftTraceUpToTheRateOfTheZeros.lean).
