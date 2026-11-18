# The canonical factorial remainder and the Mertens function

Let $S_N=\sum_{d\le N}\mu(d)\lfloor N/d\rfloor\log\lfloor N/d\rfloor$ be the Stirling entropy of the factorial presentation of $\operatorname{lcm}(1,\ldots,N)$. Its logarithmic value is $\psi(N)$. Put $S_0=0$, $\epsilon(1)=1$ and $\epsilon(j)=1-(j-1)\log(j/(j-1))$ for $j>1$. Then
$$1+\psi(N)-S_N=\sum_{j\le N}\epsilon(j)M(\lfloor N/j\rfloor)\quad(N\ge1).$$
Indeed the first difference of $j\log j$ is $\log j+1-\epsilon(j)$, and differencing each floor restricts the Möbius sum to divisors. Convolution of $\mu$ with $\log$ gives $\Lambda$, and convolution with $1$ gives the mass at one.

The operation on the right has a bounded inverse already at the square-root scale. For $j\ge2$, the midpoint inequality $\log(j/(j-1))\ge2/(2j-1)$ gives
$$0<\epsilon(j)\le(2j-1)^{-1}<\sqrt{j/(j-1)}-1.$$
Dividing by $\sqrt j$ and telescoping shows $\sum_{j\ge2}\epsilon(j)/\sqrt j\le1-\delta$ with $\delta>0$ from the strict inequality at two. Thus for every $\sigma\ge1/2$ the nonidentity part of the floor sum has norm at most $1-\delta$ on the weighted prefix supremum $\max_{k\le x}|F(k)|/k^\sigma$. The factorial remainder and $M$ have the same power bounds, including the endpoint with its constant. The Dirichlet series $\sum\epsilon(j)j^{-s}$ also has modulus at least $\delta$ throughout $\Re s\ge1/2$.

For each integer sample $m>1$, the sign of its entropy minus $\Lambda(m)$ is exactly $(-1)^{\omega(m)+1}$. Expand $\epsilon(j)=\sum_{k\ge1}j^{-k}/[k(k+1)]$, valid at one by telescoping. The magnitude equals
$$\sum_{k\ge1}\frac{(\mathrm{rad}(m)/m)^k}{k(k+1)}\prod_{p\mid m}(1-p^{-k}).$$
For a scaled compact weight $W$, the signed factorial remainder is therefore an invertible average of $\sum_m\mu(m)W(m/X)$ at the dilated scales $X/j$, up to the explicit sample at one. This removes a possible cancellation at off-line zeros in the entropy remainder and identifies the arithmetic estimate needed for this specific presentation. The uniform bound for the square generator remains open.
