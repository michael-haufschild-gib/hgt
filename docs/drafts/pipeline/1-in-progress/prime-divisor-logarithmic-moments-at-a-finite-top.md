# Prime-divisor logarithmic moments at a finite top

For $k\ge1$ let $B_k(X)=\sum_{n\le X}\sum_{p\mid n}(\log p)^k$. Each prime divisor is counted once, so $B_k(X)=\sum_{p\le X}(\log p)^k\lfloor X/p\rfloor$. The Dirichlet series of its jumps in $\Re s>1$ is $\zeta(s)(-1)^kP^{(k)}(s)$ for $P(s)=\sum_p p^{-s}$.

At a right zero $\rho$ of multiplicity $m$, $P'(s)=m/(s-\rho)+H(s)$ with $H$ holomorphic. Higher prime powers are holomorphic there. Hence the continued jump series has order exactly $m-k$. It detects precisely the zeros of multiplicity less than $k$ as poles. With $r$ unrestricted integer factors in the floor count the corresponding order is $rm-k$. Thus the first moment sensitive to a particular quartet on the one-factor row is $k=m+1$.

The first moment has an unconditional positive error of exact order $\sqrt X$. Put $w(d)=\Lambda(d)$ on proper prime powers and zero elsewhere, and $c=\sum_{d\ge1}w(d)/d$. For integer $N$,
$$B_1(N)-\log(N!)+cN=\sum_{d\ge1}w(d)\big(N/d-\lfloor N/d\rfloor\big).$$
The summands are nonnegative. The proper-power mass through $u$ is $O(\sqrt u)$. Summing first through $N$, then over $(2^jN,2^{j+1}N]$ with weight at most $2^{-j}$, costs $O(\sqrt N)$ in all. For $\sqrt N<p\le 2\sqrt N$, the square $p^2$ alone contributes at least $(\log p)/4$. The prime number theorem gives a lower bound $\gg\sqrt N$ at every sufficiently large cutoff. Thus a first-moment error on the square-root scale is compatible with every right-zero multiplicity.

For higher moments the pole at one prescribes a polynomial in $\log X$ multiplying $X$. Can a genuine arithmetic estimate below $X^{\Re\rho}$ be proved for the first detecting order under the quartet hypothesis?

The first moment can still detect a right zero at half its ordinate. Write $M=-\zeta'/\zeta$ and $P_1(s)=\sum_p(\log p)p^{-s}$. On $\Re s>1$, Möbius inversion in the prime exponent gives
$$\zeta(s)P_1(s)=-\zeta'(s)-\zeta(s)\{M(2s)+M(3s)\}+\zeta(s)T(s),$$
where $T$ is holomorphic for $\Re s>1/4$. After the rows at exponents two and three have been removed, every remaining prime-power row has exponent at least four. The positive majorant $\sum_p(\log p)p^{-4\sigma}/(1-p^{-\sigma})$ converges for $\sigma>1/4$.

At $z=\rho/2$ for a right zero, the residue is
$$\zeta(z)\left(\frac{\operatorname{ord}_{2z}\zeta}{2}+\frac{\operatorname{ord}_{3z}\zeta}{3}\right).$$
The two multiplicities are nonnegative, so a coincident zero at $3z$ increases the residue factor. If every such pole were canceled, every right zero $\rho$ would force $\zeta(\rho/2)=0$. Reflection and iteration of $s\mapsto1-s/2$ would give zeros tending to $2/3$, where $\zeta$ is nonzero. Consequently RH is equivalent to absence of nonreal poles of this first ordinary-prime moment in $\Re s>1/4$. The possible real poles there are $1,1/2,1/3$. This recovers a test for arbitrary configurations from a count whose transform is regular at every right zero itself. [Halving theorem](../../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyZeroCascade.lean)
