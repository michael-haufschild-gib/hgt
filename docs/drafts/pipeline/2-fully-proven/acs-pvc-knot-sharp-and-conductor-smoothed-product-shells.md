# Knot-sharp and conductor-smoothed upper product shells on square conductors

- **ID:** acs-pvc-knot-sharp-and-conductor-smoothed-product-shells
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../../../reports/review-1811/obstacles-summary.md · §2.3, §2.4, §2.14, §2.18
- **Statement:** On the detached subquadratic range, eighth-order periodic quotient cancellation bounds each single-conductor shell $T_n(V,M)-T_n(W,M)$ by $O(W^8(1+\log W)/n^{15})$, paying all products through $\lfloor n^{15/8}\rfloor$ on individual conductors; summing $n^2(T_n(u_n,n)-T_n(w_n,n))$ across conductors smooths the B-spline knots to ninth order, giving $\left|\sum_{N<n\le M} n^2 B_n\right|\ll N^{7/4}(1+\log(2N))$ for the §2.4 shell $V_n=\lfloor n^{7/4}\rfloor$ ($N\le M\le 2N$), $O(N^{9\alpha-14}(1+\log(2N)))$ for every shell $V_n=\lfloor n^\alpha\rfloor$ ($3/2\le\alpha<2$), and paying all products through $\lfloor n^{17/9}\rfloor$ in the signed ACS conductor prefix for RH.

## Paper proof (`[PROVED HERE]`)

Let $\Phi=\mathrm{dyadicSpline}$, $s_n(k)=\Phi(k/n^2)/n$, $L_n=\mathrm{splineHorizon}(n)$, $Y(k)=\mathrm{productLower}(1,k)$, and $T_n(U,M)=\mathrm{cappedUpperProductReading}(U,M,n)$.

1. **Arbitrary-order periodic quotient cancellation.** By `centeredPrimeWeight_expansion` and `stencil_recip` at $R=1$, $w(j):=\mathrm{centeredPrimeWeight}(1,j)=\mathrm{correctedStencil}(1,d\mapsto\mathrm{centeredModularRamp}(d,j))$ is a fixed linear combination over $1\le d\le 16512$ of $d$-periodic zero-mean sequences bounded by $1$. Applying `abs_sum_mul_periodic_le_iter` to each modulus $d$ shows that for every $s\in\mathbb{N}$, $b\in\mathbb{N}$, and $x:\mathbb{N}\to\mathbb{R}$ vanishing on $[0,s+1)$ and $[b,\infty)$,
   $$\left|\sum_{j<b} x(j)w(j)\right|\le C_s\sum_{j<b}|\Delta^{s+1}x(j)|.$$
   For $H(n,q):=\sum_{k\le L_n}(s_n(k)-s_n(k+1))w(\lfloor k/q\rfloor)$ with $n,q>0$, padding above $L_n$ to $q b$ ($b=\lfloor L_n/q\rfloor+2$) where $s_n=0$ and grouping modulo $q$ yields $H(n,q)=\sum_{j<b}(s_n(qj)-s_n(q(j+1)))w(j)$.

2. **Piecewise smoothness and Lipschitz knot barrier of $\Phi$, $\widetilde{\Psi}$, and $\Theta_2$.** Recall $\mathrm{splineAutoCorr}=\mathrm{upow}(1,7)=U_1^{\star 8}$.
   - Globally, $\mathrm{upow}(1,1)$ is $1$-Lipschitz and $\partial_x\mathrm{upow}(1,m+1)(x)=\frac{1}{2}(\mathrm{upow}(1,m)(x+1)-\mathrm{upow}(1,m)(x-1))$ for $m\ge 1$, so $\mathrm{upow}(1,7)\in C^{6,1}(\mathbb{R})$ with compact support $[-8,8]$. By composition with $\log$ and multiplication by $2x^{-1/2}$ on $[e^{-8},4e^8]$, $\Phi\in C^{6,1}_c([e^{-8},4e^8])$. Setting $F(u)=\int_0^u\Phi(x)x^{-2}\,dx$ and $\widetilde{\Psi}(u)=\frac{1}{2}u F(u)$, differentiation gives $\widetilde{\Psi}''(u)=\Phi'(u)/(2u)$ on $(0,\infty)$ and $0$ on $(-\infty,0]$, hence $\widetilde{\Psi}''\in C^{5,1}_c([e^{-8},4e^8])$ and $\widetilde{\Psi}\in C^{7,1}(\mathbb{R})$ with $\Delta_h^2\widetilde{\Psi}(u)=0$ outside $[e^{-8}-2h,4e^8]$. Likewise $\Theta_2(x):=2x\Phi'(x)+4x^2\Phi''(x)\in C^{4,1}_c([e^{-8},4e^8])$.
   - Outside the finite knot set $K_{\mathrm{knots}}=\{e^{2i-8},4e^{2i-8}:0\le i\le 8\}$ ($\#K_{\mathrm{knots}}\le 18$), induction on $m$ exhibits a finite family $\mathcal{P}_7$ of $C^\infty(\mathbb{R})$ functions such that on every open interval disjoint from $\mathrm{upowKnots}(7)$, $\mathrm{upow}(1,7)$ agrees with a member of $\mathcal{P}_7$. Hence on every interval $[u,u+kh]$ ($h\in(0,1]$) disjoint from $K_{\mathrm{knots}}$, either the interval lies outside $[e^{-8},4e^8]$ (where $\Delta_h^8\Phi=0$ and $\Delta_h^9\widetilde{\Psi}=0$) or lies inside $(e^{-8},4e^8)$, where the mean value theorem for iterated differences gives $|\Delta_h^8\Phi(u)|\le M_8 h^8$ and $|\Delta_h^9\widetilde{\Psi}(u)|\le M_9 h^9$ by compactness of $[e^{-8},4e^8]$ across the finite family $\mathcal{P}_7\times\mathcal{P}_7$.
   - At most $18(k+1)$ indices $j\in\mathbb{N}$ satisfy $[jh,(j+k)h]\cap K_{\mathrm{knots}}\ne\emptyset$; at these indices $\Phi\in C^{6,1}$ gives $|\Delta_h^8\Phi(jh)|\le 14 L_6 h^7$ and $\widetilde{\Psi}\in C^{7,1}$ gives $|\Delta_h^9\widetilde{\Psi}(jh)|\le 16 L_7 h^8$. Summing smooth ($\le (4e^8+1)/h$) and knot ($\le 180$) indices yields, uniformly for $0<h\le 1$ and $b\in\mathbb{N}$:
     $$\sum_{j<b}|\Delta_h^8\Phi(jh)|\le K_\Phi h^7,\qquad \sum_{j<b}|\Delta_h^9\widetilde{\Psi}(jh)|\le K_{\widetilde{\Psi}} h^8,\qquad \sum_{j<b}|\Delta_h^5\Theta_2(jh)|\le K_\Theta h^4.$$

3. **Single-conductor eighth-order shell and the fifteen-sixteenths window.** Whenever $7q<e^{-8}n^2$, $s_n(qj)=0$ for $0\le j\le 7$; Step 1 ($s=6$) and Step 2 ($h=q/n^2$) yield $|H(n,q)|\le K q^7/n^{15}$. For $Y(L_n)\le V\le W$ and $7W<e^{-8}n^2$, exchanging horizons and prime/cofactor pairs gives uniformly in $M\in\mathbb{N}$:
   $$|T_n(V,M)-T_n(W,M)|\le C\frac{W^8(1+\log W)}{n^{15}}.$$
   Splitting at $U_0=\max(1,Y(L_n))$ and comparing with `dyadicPrimeContact_upper_product_tail` for $U\le U_0$ or $7U\ge e^{-8}n^2$ upgrades the global approximation for all $n\ge 1$, $U\ge 1$, $M\in\mathbb{N}$ to
   $$|D_n-T_n(U,M)|\le A(1+\log L_n)^6+B\frac{(1+\log U)U^8}{n^{15}}+C\frac{n(1+\log L_n)}{M+1}.$$
   Setting $U=\lfloor n^{15/8}\rfloor$, $M=n$ gives $|D_n-T_n(\lfloor n^{15/8}\rfloor,n)|\le C(1+\log(2n))^6$, paying the $(n^2)^{15/16}$ product window on every conductor. On $V_n=\lfloor n^{7/4}\rfloor$, $|B_n|\le C(1+\log(2n))/n$.

4. **Two-variable conductor-mesh smoothing beyond the knot wall.** Let $u,w:\mathbb{N}\to\mathbb{N}$ be monotone with $Y(L_n)\le u(n)\le w(n)$ on $n\in(N,M]$ ($0<N\le M\le 2N$, $1\le w(2N)$) and $8w(2N)<e^{-8}N^2$. For each $(p,v)$ with $q=pv$, $\{n\in(N,M]:v\le n\wedge u(n)<q\le w(n)\}$ is order-convex, hence equals $[a,d)\cap\mathbb{N}$ for some $N<a\le d\le M+1\le 2N+1$. By trapezoidal Euler–Maclaurin on $[a,d)$, for $G(j):=\sum_{n\in[a,d)}n\Phi(jq/n^2)$,
   $$G(j)=I(j)-B(j)-R(j),\quad I(j)=\int_a^d t\Phi(jq/t^2)\,dt=a^2\widetilde{\Psi}(jq/a^2)-d^2\widetilde{\Psi}(jq/d^2),$$
   $$B(j)=\tfrac{1}{2}\big(d\Phi(jq/d^2)-a\Phi(jq/a^2)\big),\quad R(j)=\sum_{n\in[a,d)}\int_0^1\frac{s(s-1)}{2(n+s)}\Theta_2\!\left(\frac{jq}{(n+s)^2}\right)ds.$$
   Since $8q<e^{-8}N^2<e^{-8}a^2$, each piece vanishes for $j\le 8$ and beyond $b_{\max}=\max(\lfloor L_{2N}/q\rfloor+2,\lfloor 4e^8(2N+2)^2/q\rfloor+12)$. Applying Step 1 + Step 2 with $s=7$ to $I$, $s=6$ to $B$, and $s=3$ to $R$ gives
   $$\left|\sum_{n\in[a,d)}n^2 H(n,q)\right|\ll \frac{q^8}{N^{14}}+\frac{q^7}{N^{13}}+\frac{q^4}{N^8}.$$
   Summing over $4<p\le w(2N)$ and $v\le w(2N)/p$ by Mertens' first theorem gives
   $$\left|\sum_{N<n\le M}n^2\big(T_n(u_n,n)-T_n(w_n,n)\big)\right|\ll (1+\log w(2N))\left(\frac{w(2N)^9}{N^{14}}+\frac{w(2N)^8}{N^{13}}+\frac{w(2N)^5}{N^8}\right).$$

5. **Resolution of §2.4 and the seventeen-eighteenths prefix criterion.**
   - Specializing $u_n=\lfloor n^{7/4}\rfloor$, $w_n=2\lfloor n^{7/4}\rfloor$ yields $\left|\sum_{N<n\le M}n^2 B_n\right|\le C N^{7/4}(1+\log(2N))$ for all $N\le M\le 2N$, hence $\ll_\delta N^{7/2-\delta}$ for every $\delta<7/4$.
   - For every $\alpha\in[3/2,2)$, $u_n=\lfloor n^\alpha\rfloor$, $w_n=2\lfloor n^\alpha\rfloor$ yields $O_\alpha(N^{9\alpha-14}(1+\log(2N)))$, saving $N^{2-\alpha}$ beyond the single-conductor eighth-order knot bound $O(N^{8\alpha-12}(1+\log(2N)))$.
   - Taking $u_n=\lfloor n^{15/8}\rfloor$, $w_n=\lfloor n^{17/9}\rfloor$ gives $O(M_0^3(1+\log(2M_0)))$ on every octave $(M_0,M_1]$ ($M_0\le M_1\le 2M_0$). Dyadic halving $M_0=\lfloor(N+1)/2\rfloor$ sums to $O(N^3(1+\log(2N)))$ for all $N\in\mathbb{N}$. Combining with Step 3 proves $\left|\log P_N-\sum_{n=1}^N n^2 T_n(\lfloor n^{17/9}\rfloor,n)\right|\le C N^3(1+\log(2N))^6$, transferring both `zetaZeroWidth ≤ a` ($0<a<1/2$) and `RiemannHypothesis` to `seventeenNinthsConductorPrefix`.
