# A prime cutoff separating the two square products

Let $H$ be the eightfold box convolution, $b=\log4$, and $F(t)=2H(t)-H(t-b)$. There is a fixed cutoff $\tau$ with $F\ge0$ to its left and $F\le0$ to its right. For a function with one such sign change at $c$, its moving integral $G(x)=\int_{x-1}^{x+1}f$ is nonnegative for $x\le c-1$ and nonpositive for $x\ge c+1$. On $[c-1,c+1]$ shifting the interval right loses only nonnegative mass and gains only nonpositive mass. Continuity gives a separating zero for $G$. The difference of the two initial box functions has a sign change at $1$; convolution seven times proves the claim.

Write $e_p=v_p(U_n/V_n)$ and $T_n=e^\tau n^2$. Every positive profile valuation is at or below $T_n$ and every negative profile valuation is at or above it. Consequently
$$
0\le \log U_n-\sum_{p\le T_n} e_p\log p
=\sum_{p\le T_n}(-e_p)_+\log p+\sum_{p>T_n}(e_p)_+\log p\ll n^2.
$$
The absolute profile error pays for every misplaced factor. The analogous approximation for $\log V_n$ has exactly the same error. In particular the two products can be separated by prime size at the precision of the RH comparison.

The common cubic leading constant of $\log U_n$ and $\log V_n$ is $4\int_{\tau-b}^{\tau}H(t)e^{t/2}\,dt$. The prime number theorem applies to the continuous compact positive and negative parts of the profile. Each gives twice the positive half moment of $F$; integrating up to $\tau$ and translating by $b$ gives the formula. Controlling the difference between the two prime counts through their common cubic term remains open.

Lean proves the cutoff, exact log errors, quadratic misplaced mass, and both cubic limits in [APrimeCutSeparatesTheSquareProducts](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/APrimeCutSeparatesTheSquareProducts.lean).
