# Logarithmic moments of the reflected state

For every critical state at its positive threshold, every $0\le c\le1$ and every integer $m\ge0$,
$$
\int_{\mathbb R}\log^m(4+|t|)\,|\mathcal LF(-c+it)|^2\,dt < \infty .
$$
Consequently $N(1/2+c-it)\mathcal LF(-c+it)\in L^2(dt)$ for $\Theta-1/2<c\le1$, where $N$ is the logarithmic derivative of the pole-removed zeta function.

Put $h=k^2$, $G=e^{-cu}F$, $D(u)=F(u)-e^{-ch}F(u+h)$. The wall modulus and $1-e^{-ch}\le h$ give $\int D^2=O(h)$. Confinement gives $\int D^2 e^{-8u}=O(1)$ uniformly for $0<h\le1$. On the negative half-line $k e^{-2cu}\le1+k^2 e^{-8u}$, so $\int|G(u)-G(u+h)|^2\,du=O(k)$. With $h=4^{-(n+1)}$, the Plancherel weight $1-\cos(ht)$ is bounded below on $4^n\le |t|+4<4^{n+1}$ for $n\ge2$. The resulting shell masses are $O(2^{-n})$, which is summable against every fixed polynomial in $n$. The Euler factor grows at most logarithmically on the indicated zero-free lines.

Lean declarations: `criticalState_eventually_tilted_sq_increment_le`, `integrable_log_pow_mul_norm_sq_reflected_laplace`, `integrable_norm_sq_reflected_euler_mul_laplace`. [Proof](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/LogarithmicMomentsOnTheReflectedLines.lean).
