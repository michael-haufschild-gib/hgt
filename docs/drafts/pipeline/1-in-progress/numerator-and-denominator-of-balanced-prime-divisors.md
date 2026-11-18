# Numerator and denominator on the balanced prime ray

For $a_p=p e_1+(p-1)e_{p^2}-e_{p^4}$ write the ordinary-prime generator of $ma_p$ in lowest terms as $U_{p,m}/V_{p,m}$. Determine the separate quadratic limits of $\log U_{p,m}$ and $\log V_{p,m}$. Their difference is the quantity in the [pole-balanced comparison](pole-balanced-integer-spline-divisors.md).

Let $H(t)=\int B(u)B(u+t)\,du$. For $\log p>8$ the three windows of ordinary primes are disjoint. After the mesh limit their weights before $2\log q/\sqrt q$ are
\[
 (p^2+(p-1)^2+1)H(\log q),\qquad
 (p-1)^2 H(\log(q/p^2)),\qquad
 -p H(\log(q/p^4)).
\]
The shared sign of the two terms at distance $2\log p$ holds after integration by translation. In the finite product each ordinary prime occurs once, so passing to positive and negative parts commutes with the fixed-window mesh limit.

**Conjecture.** Both quadratic coefficients divided by $p^3$ tend through primes to $2\int e^{t/2}H(t)\,dt>0$. The prime number theorem gives the proposed leading term in each moving window. RH requires a uniform upper bound for their difference at scale $p^2$. A group homomorphism from $\mathbb Z/U$ to $\mathbb Z/V$ is zero by coprimality. Consequently any additive injection into $\mathbb Z/V$ times an auxiliary group must pay all of $\log U$ in that group.
