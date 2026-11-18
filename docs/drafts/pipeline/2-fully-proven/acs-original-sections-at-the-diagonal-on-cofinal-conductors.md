# Original sections at the diagonal on cofinal square conductors

On $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$ write $S(n,m)$ for the original radius minus the full log generator and $V(n,m)$ for the ordinary floor loss. Then
\[
  (S(n,n)-V(n,n))/n^2-Q(D_n)\longrightarrow 0.
\]
On arbitrarily large conductors $Q(D_n)\ge0$ and $V(n,n)\ge cn^2$. Consequently the original section lattice contains at least $2\lfloor e^{\delta n^2}\rfloor+1$ sections at the exact multiplicity $m=n$ on arbitrarily large conductors, for some fixed $\delta>0$.

Let $q(n,r)$ be the regularized jet form of the unscaled packet at resolution $r$. For any sequence $r_n\to\infty$, $q(n,r_n)$ tends to the same constant. Indeed split the packet into its unit atom and the upper pair. Their supports in degree indices differ by a factor of order $n^2$. Both harmonic masses are bounded independently of resolution, so their mixed jet costs $O(1/n)$. The unit atom has a fixed-window limit. Translating the upper pair by $-\log n^2$ converts its resolution exactly to $n^2r_n$. Its relative displacement $\log((2n+1)^2/n^2)$ tends to $\log4$. The profiles lie in a fixed window, are uniformly Lipschitz and tend uniformly to the pair with relative dilation four. Compact-window stability gives the fixed pair's jet limit. [Separation and dilation](../3-formalized/acs-the-jets-of-moving-integer-translates.md) · [Compact-window stability](../3-formalized/acs-stability-of-jets-on-a-fixed-window.md)

The full prime and pole comparisons give
\[
 S(n,m)=V(n,m)-m^2(q(n,r_{n,m})+P_*(D_n))+O(n+m)
\]
with $r_{n,m}$ the original resolution. For fixed $n$, $V(n,m)$ is bounded by the window's total prime log weight, and $S(n,m)/m^2\to Q(D_n)$. Choose $m_n\ge n$ so that $q(n,r_{n,m_n})$ differs from $-Q(D_n)-P_*(D_n)$ by at most $1/(n+1)$. The resolutions at $m_n$ and at $n$ both tend to infinity, so their jets differ by $o(1)$. Substitution at $m=n$ yields the displayed limit. The prime sum cancels between resolutions without any bound on its sign or growth. [Full ideal comparison](../3-formalized/acs-the-full-prime-ideal-at-diagonal-scale.md) · [Diagonal floor loss](../3-formalized/acs-prime-floor-loss-on-the-diagonal.md)

For every fixed $K\ge1$, the stronger inequality $S(n,m)\ge m^2Q(D_n)+\delta_Kn^2$ holds for every $1\le m\le Kn$ on every sufficiently large conductor. Indeed the discrepancy $q(n,r)+Q(D_n)+P_*(D_n)$ tends jointly to zero as $n,r\to\infty$. It is also bounded above for all positive resolutions, by the finite jet upper bound and the convergence of $Q(D_n)+P_*(D_n)$. Choose the large-resolution error at most $c_K/(4K^2)$, where the ordinary floors save $c_Kn^2$. At resolutions below the resulting fixed threshold, $m$ is bounded since $r_{n,m}\ge m$. Thus the error times $m^2$ costs at most $c_Kn^2/4+O_K(1)$. The remaining $O(n+m)$ error is absorbed for large $n$. On the cofinal set with $Q(D_n)\ge0$, this proves exponential growth of original sections through every prescribed fixed multiple of $n$.
