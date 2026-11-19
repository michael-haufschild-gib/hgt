# Integral range of the two-sided quotient profile

For arbitrary signed endpoint jumps on $[1,N]$, determine all simultaneous integral relations between the positive quotient cells in the full mixed Weil form. Their cumulative sum from $k$ onwards counts both directed incidences $i\mapsto ki$ on the two underlying divisors. At $k=1$ the total is twice their integral inner product. Pairing with the fixed divisor at conductor one realizes every integral profile whose total is even. The distinction between mixed intersections and self-intersections matters for recovering positivity from these relations.

With $u_i=\sum_{j\ge i}a_j$, $v_i=\sum_{j\ge i}b_j$ and zero extension past $N$, write $C_q$ for the two-sided coefficient. For every $k\ge1$,
$$\sum_{q=k}^N C_q=\sum_{i=1}^N (u_i v_{ki}+v_i u_{ki}).$$
Indeed $\lfloor j/i\rfloor\ge k$ is exactly $j\ge ki$. At one this gives $2\sum_i u_iv_i$. Conversely, given integral $w_1,\dots,w_N$ with sum $2t$, take $u=\delta_1$, $v_1=t$ and $v_k=\sum_{q=k}^N w_q$ for $k>1$. Both are integral divisors with terminal jumps back to zero. All positive tails agree, so subtracting consecutive tails recovers every $w_q$. The empty window has empty profile. For self-intersections the total is twice the nonnegative square mass.

`twoSidedCoefficient_tail` and `twoSidedCoefficient_difference` give the multiplicative correlations. The integral classification is `exists_twoSidedCoefficient_iff_even`; `quotient_profile_of_even_total` constructs the anchored realization. [Formal proof](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheIntegralRangeOfTheMixedQuotientCells.lean)
