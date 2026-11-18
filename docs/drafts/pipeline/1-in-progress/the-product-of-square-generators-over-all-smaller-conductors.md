# The product of square generators over all smaller conductors

Put $q_n=U_n/V_n$ at multiplicity $n$ and $P_N=\prod_{n\le N}q_n$. Can the entire prefix be compared at once? The proposed arithmetic criterion is
$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\exists B\in\mathbb N_{>0}\ \forall N\ge1,\qquad B^{-N^3}\le P_N\le B^{N^3}.
$$
Inter-conductor cancellation is allowed in the product. More generally the exponent of $|\log P_N|$ is $3+2w$, with $w$ the zero width.

A prefix bound $|\log P_N|\le C N^{3+2s}$ gives $\sum_{x-x^\theta<n\le x}\log q_n\le 2Cx^{3+2s}$ for $0<\theta<1$. The interval contains at least $x^\theta/2$ integers for large $x$. At one of them $\log q_n\ll n^{3+2s-\theta}$. These selected conductors have gaps $O(x^\theta)$. The sparse conductor criterion gives $w\le s+(1-\theta)/2$ whenever that bound is below one half. Taking $\theta$ to one gives $w\le s$. Conversely the pointwise width bound gives the prefix bound by summation. [Sparse conductor criterion](square-section-bounds-on-sparse-conductors.md)

The signed prime profile of the prefix is $V(v)=2\int_0^1 tW(v/t^2)\,dt=v\int_v^\infty W(u)u^{-2}\,du$. The accumulated valuation and quadrature errors cost $O(N^3)$. The sum-integral replacement has the same allowance. For each prime, $tW(p/t^2)$ has bounded derivative on a support interval of length $O(\sqrt p)$, so replacing its sum by its integral costs $O(\sqrt p)$ before the log weight. Thus $\log P_N=N^2\sum_p V(p/N^2)\log p+O(N^3)$. The Mellin multiplier is $M_V(s)=M_W(s)/(s+1)$ for $\Re s>-1$.

A different averaging weight, $n^{-4}$, isolates a positive kernel. For $A(v)=\int_0^v W(u)\,du$, translation gives $A(v)=2\int_{\log v-\log4}^{\log v}H(t)e^{t/2}\,dt\ge0$. Integrating $2t^{-3}W(p/t^2)$ between two conductors $N$ and $M$ gives $(A(p/N^2)-A(p/M^2))/p$. Passing to infinity retains the nonzero limiting prime average at the moving upper endpoint.

**Dirichlet series of the actual rational prices.** Put $D(s)=\sum_{n\ge1}n^{-s}\log q_n$ and $z=s/2-1$. Prime factorization gives the continuation
$$D(s)=-M_W(z)\,\zeta'(z)/\zeta(z)+E(s),\qquad \Re s>3,$$
with $E$ holomorphic there. Initially $\Re s>4$ and both sums converge absolutely. Replacing $v_p(q_n)$ by $2nW(p/n^2)$ costs $O(n^2)$ per conductor in total log mass. For each $p$, integration of $2t^{1-s}W(p/t^2)$ on $(0,\infty)$ gives $p^{-z}M_W(z)$. On compact subsets of $\Re s>3$, the sum–integral difference is $O_K(p^{(1-\Re s)/2})$ by integrating the derivative on the unit cells, with $t\asymp\sqrt p$ on its support. These errors are normally summable even after multiplication by $\log p$. The prime powers of order at least two are absolutely summable for $\Re z>1/2$. The simple zero $M_W(1)=0$ removes the real pole; at every zero $\rho$ with $\Re\rho>1/2$ the residue at $s=2+2\rho$ is $-2\operatorname{ord}_\rho(\zeta) M_W(\rho)\ne0$. A one-sided bound on $\log P_N$ is then a Landau bound for the nonnegative density $C x^b\pm\log P_{\lfloor x\rfloor}$, since $D(s)/s$ is the Mellin integral of the prefix against $x^{-s-1}$. [Prime exponent estimate](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeExponentsOnTheSquareDiagonal.lean) · [Mellin multiplier](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/CriticalZerosSeparateThePrimeProfileFromFactorialKernels.lean)

**One-sided product bound.** Let $a_z$ be the coefficient of $e^{zu}$ in the real spline trace. At $u=2\log N$ the normalized logarithm $N^{-3}\log P_N$ differs by $O(1)$ from
$$
\sum_z a_z\frac{2\,4^z-4}{3+2z}e^{zu}.
$$
Indeed, $\log q_n/n^2=2T(2\log n+\log4)-4T(2\log n)+O(1)$. Replacing $\sum_{n\le N}n^{2+2z}$ by $N^{3+2z}/(3+2z)$ costs $O((1+|z|)N^{2+2w})$ by integrating the derivative on each unit cell. The absolute first spectral moment is finite and $2w<1$. Every off-line coefficient survives, since $|4^z|<2$ in the centered open strip. The spectral series has bounded increments between consecutive logarithms of squares. A bound from either side extends to every real log scale, where the one-sided Laplace argument excludes poles with $\Re z>s$. This would allow either inequality for $P_N$ alone. The missing arithmetic input is a uniform one-sided cubic allowance for the actual cumulative product. [Landau argument at integer degrees](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/OneSidedHasseWeilAtTheIntegerDegrees.lean) · [Square trace and its spectral coefficients](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheThetaMeanOfTheSquareTrace.lean)
