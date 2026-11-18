# Prime bands at prescribed multiplicity

For $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$ there are absolute $c,c'>0$ such that every sufficiently large $n$ and every integer $1\le m\le c(n+1)^{5/8}$ satisfy $\log d_{\rm ord}(mD_n)\le-c'n^2$ and give at least $2\lfloor\exp(c'n^2)\rfloor+1$ original sections.

## Proof

Put $b=(2n+1)^2$, $t=m^2/(2n+1)$ and $F(x)=2H(-\log x)/\sqrt x$, with $H$ the spline autocorrelation. On $u=e^8/2\le k/b\le v+1$, $v=2e^8$, only the last pair of graphs meets, so the integrated row of $mD_n$ is $-tF(k/b)$. The actual row differs by $O(m/n)$. The function $F$ has Lipschitz constant $L\ge1$ on this interval, with $F(u)>0$ and $F(v)=0$.

Fix $t\ge d>0$. Take $0<e\le\min(1/16,d/4,dF(u)/16)$. For each integer $0\le j\le tF(u)/2$ there exists $z_j\in[u,v]$ with $tF(z_j)=j+4e$. On $(z_j,z_j+e/(Lt)]$ the scaled profile differs from $j+4e$ by at most $e$. If the actual mesh error is at most $e$, every prime in this interval times $b$ has actual floor $-j-1$ and fractional part at least $1/2$. Different $j$ give disjoint prime sets.

For $7/12<\alpha<1$, all sufficiently late intervals $(x,x+h]$ with $x^\alpha\le h\le x/2$ carry at least $h/2$ in prime logarithmic mass. This follows from the uniform short-interval theorem for $\psi$ and the $O(\sqrt{x}\log x)$ proper-power contribution. Apply it at $x=z_j b$, $h=eb/(Lt)$ whenever $Kt\le b^{1-\alpha}$ with sufficiently large fixed $K$. There are at least $tF(u)/2$ distinct levels. Adding their contributions gives ordinary floor loss at least $eF(u)b/(8L)$ for each prescribed multiplicity.

The two bounds $Km\le(n+1)^{3/2-\alpha}$ and $Km\le(n+1)^{1-w}$ suffice for the prime intervals and the signed degree respectively. Taking $\alpha=7/8$ admits $m\le c(n+1)^{5/8}$. The signed integrated prime contact, all remaining prime powers, the archimedean contribution and global quadrature together cost at most $E(m^2(n+1)^{2w}+nm)$, where $w\le3/8$ is the zeta zero width. Choosing $c$ small absorbs this in half the floor loss, for both the logarithmic ordinary generator and the excess of the full generator over its radius. The original square-root theorem handles $t<d$ for a sufficiently small fixed $d$. The resulting logarithmic margin counts every integer coordinate $|z|\le\exp(c'n^2)$.
