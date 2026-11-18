# Common quotients of the two residue unit groups

For coprime $U,V>0$ put $A=\operatorname{rad}U$ and $B=\operatorname{rad}V$. Then
$$
\gcd(\varphi U,\varphi V)\mid \varphi A\,\varphi B
      =\prod_{p\mid UV}(p-1).
$$
Indeed write $\varphi U=(U/A)\varphi A$ and $\varphi V=(V/B)\varphi B$. A common divisor divides both $(U/A)\varphi A\varphi B$ and $(V/B)\varphi A\varphi B$. The two remaining multipliers are coprime.

For the reduced generator of $nD_n$ all prime divisors lie below $L=O(n^2)$. Thus every homomorphism between $(\mathbb Z/U_n)^\times$ and $(\mathbb Z/V_n)^\times$, in either direction, has image of log order at most $\vartheta(L)=O(n^2)$. Its kernel has cubic log order: each source log order is cubic, since $U/\varphi U=\prod_{p\mid U}p/(p-1)\le\prod_{2\le k\le L}k/(k-1)=L$. The log ratio of the two group sizes differs from $\log(U_n/V_n)$ by at most $\log L$. Hence the cardinality comparison at the RH scale survives, while no homomorphism can realize it even with a kernel allowance of $e^{Cn^2}$.

For fixed disjoint prime supports the largest possible gcd stabilizes at finite exponents. At $\ell\mid A$ its exponent is $v_\ell(\varphi B)$, at $\ell\mid B$ it is $v_\ell(\varphi A)$, and elsewhere it is $\min(v_\ell(\varphi A),v_\ell(\varphi B))$. Raising the primes on both sides above these finite thresholds attains all the exponents simultaneously.

A single cyclic subgroup retains the cubic size on each side. If $\lambda$ is the Carmichael function, then $u\mid2\operatorname{rad}(u)\lambda(u)$. Indeed $p^{k-1}\mid2\lambda(p^k)\mid2\lambda(u)$ whenever $p^k\mid u$; the factor two is required at $p=2$. The exponent of a finite abelian group is realized by an element. Hence $0\le\log u-\log\lambda(u)\le\log 2+\vartheta(L)$, and the same RH comparison can be made between the maximal orders of two individual units. [Divisibility and cyclic orders](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/CommonUnitGroupQuotientsAtCoprimeModuli.lean) · [Square-conductor comparison](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheImagesOfUnitGroupsOnSquareConductors.lean)

If a separate copy of $\mathbb F_p^\times$ is used for every repeated prime, the two-torsion ranks differ by $\Omega(U_n)-\Omega(V_n)+O(n^2)$: each odd prime factor supplies one copy of $\{\pm1\}$ and the valuation at two is $O(n^2)$. Its positive cubic-over-log-squared leading term still rules out an injection with a quadratic log allowance. [Reduced heights](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheNumeratorAboveSquareRootMultiplicity.lean) · [Factor count asymptotic](../3-formalized/prime-factor-multiplicities-of-the-square-generator.md)
