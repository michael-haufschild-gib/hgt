# Height of the quarter-shifted factorial ratio

Let $U_N/V_N=\prod_{k=1}^N(4k-1)/(4k-3)$ in lowest terms. Can its integer height be controlled by arithmetic of the recurrence $R_{N+1}/R_N=(4N+3)/(4N+1)$? The conjectural comparison at the first binomial intersection is
$$\log\gcd\!\left(\binom{2N}N,\binom{4N}{2N}\right)+\log U_N=3N\log2+O(\sqrt N).$$
Thus a centered estimate for $\log U_N-\pi N/2$ would control the same ordinary-prime signal.

Write $X=4N$ and $B(k)=\mathbf1_{k\bmod4\in\{1,2\}}$. At level $m=p^j$ with $p$ odd, multiplicity in the numerator product minus multiplicity in the denominator product is $-\chi_4(m)B(\lfloor X/m\rfloor)$. Multiples in each residue class correspond to quotients in one residue class modulo four. Complete periods cancel. For $p^2>X$ this gives the entire valuation of $R_N$. At those primes the sum of the two binomial carries minus twice their minimum is $B(\lfloor X/p\rfloor)$, exactly the absolute valuation of $R_N$. Higher powers cost $O(\psi(X)-\vartheta(X))$, and first levels at $p\le\sqrt X$ cost $O(\vartheta(\sqrt X))$. Both are $O(\sqrt N)$. The elementary product bound $1\le U_N/V_N\le2N+1$ allows $\tfrac12\log(U_NV_N)$ to be replaced by $\log U_N$. Stirling's formula gives the displayed linear term.

For split primes $p\equiv1\pmod4$ the ratio has nonpositive valuation at every level. Beyond the square root, $U_N$ therefore counts precisely the inert primes in the two middle quotient classes and $V_N$ counts the split primes there. Their log sizes differ by $O(\log(2N+1))$. This supplies an arithmetic comparison between the two classes even when the ordinary count carries a zeta wave. The centered height estimate remains open.

## All dyadic widths from one algebraic function

For $q=2^j$, $j\ge1$, put $P_a(N)=\prod_{k=0}^{N-1}(qk+a)$ for $1\le a<q$, and $F_N=N!/2^{v_2(N!)}$. After division by $q^NN!$, the coordinates $P_a(N)$ are the degree-$N$ Taylor coefficients of $(1-z)^{-a/q}$, powers of $(1-z)^{-1/q}$. Their projective logarithmic height is
$$h_q(N)=\log\frac{P_{q-1}(N)}{\gcd_{1\le a<q,\ a\text{ odd}}P_a(N)}.$$
At an odd prime power $m$, multiples in row $a$ correspond to $1\le v\le qN/m$ with $mv\equiv a\pmod q$. Each row contains $\lfloor N/m\rfloor$ complete periods. Among the final indicators the minimum is $\mathbf1_{q\mid\lfloor qN/m\rfloor+1}$, since the minimizing label $a\equiv-m\pmod q$ is odd. Thus only primitive characters are needed. The gcd contains no factor two. Thus its odd valuations above those of $F_N$ agree at all primes $p>\sqrt{qN}$ with the selected levels. At smaller primes the excess from interchanging the minimum and the sum over powers is at most the number of levels beyond the first. At two the compensation is exact: $v_2(C_j(N))+v_2(N!)=N$, since doubling the base preserves the central binomial valuation.

The largest row satisfies $(N+1)^{-1}\le P_{q-1}(N)/(q^N N!)\le1$, by $1-1/(qk)\ge k/(k+1)$ for $k\ge1$. The two-adic compensation gives the following estimate, with absolute error bounded by $\psi(qN)-\vartheta(qN)+\log(N+1)$:
$$h_q(N)+\log C_j(N)=N\log(2q)+O(\sqrt{qN}),\qquad N\ge1.$$
Can projective heights of the coefficient vectors on this cyclic cover be controlled independently of their prime-by-prime formula?
