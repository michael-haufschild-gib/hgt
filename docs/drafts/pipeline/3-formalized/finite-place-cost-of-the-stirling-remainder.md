# Finite-place cost of the Stirling remainder

Let $q_n=U_n/V_n$ be the reduced diagonal generator, $e_p=v_p(q_n)$, and $S_n$ its ordinary prime window. For some $C$ and all sufficiently large $n$,
$$
\log(U_nV_n)-Cn^2\le
\inf_{b_p\in\mathbb Z}\sum_{p\in S_n}|e_p-2pb_p|\log p
\le\log(U_nV_n).
$$
The upper bound follows by setting every $b_p=0$. The lower bound is at least $cn^3$ for some $c>0$. Thus subtracting twice the prime coordinates of any balanced factorial entropy leaves cubic absolute log cost.

The compact prime profile $f_p=2nW(p/n^2)$ vanishes below $e^{-8}n^2$ and has size $O(n)$ on its support. Hence $|f_p|\le p$ throughout for large $n$, so zero minimizes $|f_p-2pb_p|$. The triangle inequality transfers this bound to $e_p$ at a loss of at most $2\sum|e_p-f_p|\log p=O(n^2)$. **Lean** proves the exact mass identity, the uniform lower bound and the cubic consequence in `ordinary_absolute_prime_mass`, `square_diagonal_finite_place_cost` and `square_diagonal_finite_place_cubic_lower`. [Formal proof](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/FinitePlaceCostOfTheStirlingRemainder.lean)
