# The product of square generators over all smaller conductors

Put $q_n=U_n/V_n$ at multiplicity $n$ and $P_N=\prod_{n\le N}q_n$. Can the entire prefix be compared at once? The proposed arithmetic criterion is
$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\exists B\in\mathbb N_{>0}\ \forall N\ge1,\qquad B^{-N^3}\le P_N\le B^{N^3}.
$$
Inter-conductor cancellation is allowed in the product. More generally the exponent of $|\log P_N|$ is $3+2w$, with $w$ the zero width.

A prefix bound $|\log P_N|\le C N^{3+2s}$ gives $\sum_{x-x^\theta<n\le x}\log q_n\le 2Cx^{3+2s}$ for $0<\theta<1$. The interval contains at least $x^\theta/2$ integers for large $x$. At one of them $\log q_n\ll n^{3+2s-\theta}$. These selected conductors have gaps $O(x^\theta)$. The sparse conductor criterion gives $w\le s+(1-\theta)/2$ whenever that bound is below one half. Taking $\theta$ to one gives $w\le s$. Conversely the pointwise width bound gives the prefix bound by summation. [Sparse conductor criterion](square-section-bounds-on-sparse-conductors.md)

The signed prime profile of the prefix is $V(v)=2\int_0^1 tW(v/t^2)\,dt=v\int_v^\infty W(u)u^{-2}\,du$. The accumulated valuation and quadrature errors cost $O(N^3)$. The sum-integral replacement has the same allowance: each prime costs $O(\sqrt p)$ before the log weight, since $tW(p/t^2)$ has bounded derivative and is supported on an interval of length $O(\sqrt p)$. Thus $\log P_N=N^2\sum_p V(p/N^2)\log p+O(N^3)$. The Mellin multiplier is $M_V(s)=M_W(s)/(s+1)$ for $\Re s>-1$.

A different averaging weight, $n^{-4}$, isolates a positive kernel. For $A(v)=\int_0^v W(u)\,du$, translation gives $A(v)=2\int_{\log v-\log4}^{\log v}H(t)e^{t/2}\,dt\ge0$. Integrating $2t^{-3}W(p/t^2)$ between two conductors $N$ and $M$ gives $(A(p/N^2)-A(p/M^2))/p$. Passing to infinity retains the nonzero limiting prime average at the moving upper endpoint. The missing estimate is the fluctuation about this mean, not its positivity.

**One-sided product bound.** Let $a_z$ be the coefficient of $e^{zu}$ in the real spline trace. At $u=2\log N$ the normalized logarithm $N^{-3}\log P_N$ differs by $O(1)$ from
$$
\sum_z a_z\frac{2\,4^z-4}{3+2z}e^{zu}.
$$
Indeed, $\log q_n/n^2=2T(2\log n+\log4)-4T(2\log n)+O(1)$. Replacing $\sum_{n\le N}n^{2+2z}$ by $N^{3+2z}/(3+2z)$ costs $O((1+|z|)N^{2+2w})$ by integrating the derivative on each unit cell. The absolute first spectral moment is finite and $2w<1$. Every off-line coefficient survives, since $|4^z|<2$ in the centered open strip. The spectral series has bounded increments between consecutive logarithms of squares. A bound from either side extends to every real log scale, where the one-sided Laplace argument excludes poles with $\Re z>s$. This would allow either inequality for $P_N$ alone. The missing arithmetic input is a uniform one-sided cubic allowance for the actual cumulative product. [Landau argument at integer degrees](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/OneSidedHasseWeilAtTheIntegerDegrees.lean) · [Square trace and its spectral coefficients](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheThetaMeanOfTheSquareTrace.lean)
