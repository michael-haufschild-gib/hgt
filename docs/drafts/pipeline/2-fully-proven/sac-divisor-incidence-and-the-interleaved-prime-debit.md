# Divisor incidence, the interleaved prime debit, and the macroscopic cost barrier

For any finite set $S\subseteq\mathbb N_{>0}$, contact weight $w:\mathbb N\to\mathbb R$, and real divisor $c:S\to\mathbb R$, split the Weil self-pairing into its diagonal-plus-real-place budget and its mixed prime-and-boundary debit:

$$
B_{\mathrm{dr}}(S,c)=\sum_{n\in S}c_n^2\log\frac{n}{2\pi}-\sum_{n\in S}\sum_{m\in S\setminus\{n\}}c_m c_n\,\mathrm{jetKernel}(m,n),
$$
$$
D_w(S,c)=\sum_{n\in S}\sum_{m\in S\setminus\{n\}}c_m c_n\,\mathrm{contactW}(w,m,n)-2\left(\sum_{n\in S}\frac{c_n}{n}\right)\left(\sum_{n\in S}c_n\right).
$$

Then $\mathrm{combFormW}(w,S,c)=B_{\mathrm{dr}}(S,c)-D_w(S,c)$. When $S=[1,N]$ and $u=\mathrm{upperDivisor}(N,a)$ is given by signed integer endpoint jumps $a_j$, `interleaved_finite_part` identifies $B_{\mathrm{dr}}([1,N],u)=\sum_{n=1}^N u_n^2\log(n/(2\pi))-\tfrac12\int_0^1 J_{a,a}(x)\,dx$ and $D_\Lambda([1,N],u)=\sum_{k=0}^N c_k^{a,a}(\psi(k)-k)-2F_{u,a}$. Paying the mixed prime debit using the diagonal and real-place budget of $u$ is therefore the exact inequality $D_\Lambda(S,u)\le B_{\mathrm{dr}}(S,u)$, equivalently $\mathrm{combForm}(S,u)\ge0$.

1. **Failure on unshifted prefixes and negativity of the isolated prime-boundary term.** Write $v_{d,r}(n)=\mathbf1_{n\equiv r\pmod d}-1/d$ and $v_d=v_{d,0}$. On $[1,2]$ the integer centered divisor $u_2(n)=2\mathbf1_{2\mid n}-1$ already satisfies $B_{\mathrm{dr}}([1,2],u_2)<D_\Lambda([1,2],u_2)$. Asymptotically, for every prime $p$, every off-diagonal contact on $[1,N]$ of ratio coprime to $p$ preserves $v_p$, so monotonicity of $\psi$ on $p$-periods and $\sum_{j\le M}\psi(M/j)=\log(M!)$ give $D_\Lambda([1,N],v_p)\ge 2(1-1/p)\log(\lfloor N/p\rfloor!)-O_p(N)$, while $B_{\mathrm{dr}}([1,N],v_p)\le (1-1/p)\lfloor N/p\rfloor\log(N/(2\pi))+O_p(N)$ via the $p$-block Schur bound on the jets. Thus $\mathrm{combForm}([1,N],v_p)\to-\infty$ at rate $-\frac1p(1-\frac1p)N\log N$. Even on a late comb $S=(N,N+3KN]$ ($K\ge1$), $D_\Lambda(S,v_p)\ge 2\log 2\sum_{m\in(N,\lfloor(1+3K)N/2\rfloor]}v_p(m)^2-O(1/N)>0$ for every prime $3K<p\le KN$, so the prime-and-boundary contribution is strictly negative before spending $B_{\mathrm{dr}}$.

2. **Three divisibility counts on late combs and complete solution of the two-prime pilot.** Fix $K\ge1$ and put $S=(N,N+3KN]$, $S_r=(N,\lfloor(1+3K)N/r\rfloor]$.
   - *Coprime contact bijection:* For $d_1,d_2$ coprime to $\{2,\dots,3K\}$, multiplication $m\mapsto rm$ preserves divisibility on each $S_r$, giving $\sum_{m\ne n\in S}v_{d_1}(m)v_{d_2}(n)\,\mathrm{contactW}(w,m,n)=2\sum_{r=2}^{3K}w(r)\sum_{m\in S_r}v_{d_1}(m)v_{d_2}(m)$. Replacing $\Lambda$ by the Liouville weight $\lambda\Lambda$ leaves the endpoint, real-jet, and diagonal terms unchanged and reverses only nonsquare ratios $2\le r\le3K$:
     $$
     \mathrm{combFormW}(\lambda\Lambda,S,v_d)-\mathrm{combForm}(S,v_d)=4\sum_{\substack{2\le r\le3K\\\neg\mathrm{IsSquare}(r)}}\Lambda(r)\sum_{m\in S_r}v_d(m)^2>0\qquad(3K<d\le KN).
     $$
   - *Chinese Remainder shifted-incidence cancellation:* For coprime $d_1,d_2\ge2$ and any $h\in\mathbb N$, joint divisibility $d_1\mid m\wedge d_2\mid(m+h)$ defines one residue class modulo $d_1d_2$. On every interval $(a,b]$, the main term $(b-a)/(d_1d_2)$ cancels identically in $\sum_{m\in(a,b]}v_{d_1}(m)v_{d_2}(m+h)$, leaving absolute discrepancy at most $2$. Reversed and direct Abel summation over $S$ yield $|\mathrm{formBilinW}(w,S,v_p,v_q)|\le C_{K,w}(1+\log N)$ uniformly for all distinct primes $p\ne q$.
   - *Complete-period partition:* Partitioning $(a,b]$ into $\lfloor(b-a)/d\rfloor$ periods of length $d$ gives $\sum_{n\in(a,b]}v_d(n)^2\ge\lfloor(b-a)/d\rfloor(1-1/d)$ and $|\sum_{n\in(a,b]}v_{d,r}(n)|\le 1$.

3. **General controlled-cost positivity producer and unrestricted $\sqrt N$ prime spans.** For every $K\ge1$, contact weight $w$, and $\kappa>0$, orthogonal block reduction combined with boundedness of step-packet matrices and the bounded-ratio Schur estimate $|\sum_{m\ne n\in S}c_m c_n\,\mathrm{contactW}(w-\Lambda,m,n)|\le 2(\sum_{r=2}^{3K}|w(r)-\Lambda(r)|)\sum_{n\in S}c_n^2$ yields $C_{K,w,\kappa}>0$ such that eventually in $N$, every finite linear combination $c=\sum_{t\in T}\alpha_t v_{d_t,r_t}$ of residue refinements satisfies
   $$
   \mathrm{combFormW}(w,S,c)\ge \kappa\sum_{n\in S}c(n)^2-\frac{C_{K,w,\kappa}}{N}\left(\sum_{t\in T}|\alpha_t|\right)^2.
   $$
   For any $C_0>0$, Chebyshev's bound $\pi(X)\le\sqrt X+(2\log4)X/\log X$ and $|\langle v_p,v_q\rangle_S|\le2$ give $\sum_{n\in S}(\sum_{p\le C_0\sqrt N}\alpha_p v_p(n))^2\ge\frac{K}{4C_0}\sqrt N\sum_p\alpha_p^2$ eventually, hence $(\sum_{p\le C_0\sqrt N}|\alpha_p|)^2\ll (\log N)^{-1}\sum_{n\in S}c(n)^2$. Consequently:
   - On the two-prime pilot ($2\le p\ne q\le C_0\sqrt N$, covering all primes of order $\sqrt N$), $A_w>0$, $C_w>0$, and $B_w^2\le A_w C_w$ hold uniformly for all sufficiently large $N$, for both $\Lambda$ and $\lambda\Lambda$.
   - Every unrestricted real linear combination $c=\sum_{p\le C_0\sqrt N}\alpha_p v_p$ satisfies $\mathrm{combFormW}(w,S,c)\ge\kappa\sum_{n\in S}c(n)^2\ge0$ eventually.

4. **Macroscopic cost barrier, exact spanning, Liouville refutation, and RH equivalence.** For $N\ge2$ and $Q\ge2$, upper-triangular Möbius inversion on $S=(N,QN]$ expresses every point mass up to the constant $\mathbf1_S$, while $\sum_{t=1}^Q\mu(t)\mathbf1_{tN\mid n}=0$ on $S$ gives $\sum_{t=1}^Q\mu(t)v_{tN}(n)=-N^{-1}(\sum_{t=1}^Q\mu(t)/t)\mathbf1_S(n)$. By Bertrand's postulate there is a prime $p\in(Q/2,Q]$, whose $p$-adic valuation forces $\sum_{t=1}^Q\mu(t)/t\ne0$. Every $c:S\to\mathbb R$ therefore has an explicit representation $c=\sum_{d=2}^{QN}\alpha_d v_d$ on $S$ with $(\sum_{d=2}^{QN}|\alpha_d|)^2\le C_Q^* N\sum_{n\in S}c(n)^2$. At $Q=1+3K$:
   - Embedding the sign-twin first-step window of ratio $<10609/5000<4\le 1+3K$ into $S$ produces, for every $K\ge1$ and all sufficiently large $N$, a centered-divisibility combination $c=\sum_{d=2}^{(1+3K)N}\alpha_d v_d$ of cost $(\sum_d|\alpha_d|)^2\le C_{1+3K}^* N\sum_{n\in S}c(n)^2$ with $\mathrm{combFormW}(\lambda\Lambda,S,c)<-(1/2000)\sum_{n\in S}c(n)^2<0$. The $N^{-1}(\sum|\alpha_t|)^2$ cost barrier is therefore sharp up to a constant factor, and no contact-sign-blind divisibility count can cross it.
   - Paying the mixed prime debit $D_\Lambda(S,c)\le B_{\mathrm{dr}}(S,c)$ across centered-divisibility linear combinations of cost $(\sum_{d=2}^{(1+3K)N}|\alpha_d|)^2\le C_{1+3K}^* N\sum_{n\in S}c(n)^2$ on all late combs at every fixed $K\ge1$ is unconditionally equivalent to the Riemann Hypothesis.
