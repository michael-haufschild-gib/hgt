# The sharp price of a mixed integral graph height

**Theorem.** Take signed lower multiplicities $u_i$ and upper endpoint jumps $b_j$. Let $c_k$ sum $u_i b_j$ over $\lfloor j/i\rfloor=k$. The signed logarithmic height $H$, degree product $P=(\sum u_i/i)(\sum b_j j)$ and fractional boundary $F=\sum u_i b_j\{j/i\}$ satisfy

$$H-P+F=\sum_k c_k(\psi(k)-k).$$

For any nonnegative weight $W$, the bound by $C\sum_k|c_k|W(k)$ on every support is equivalent, with the same constant, to $|\psi(k)-k|\le C W(k)$ for every positive $k$.

**Proof.** Taking successive differences, including the last jump to zero, writes every integral upper divisor as a sum of endpoints. The local order of the lower graph $i$ against the endpoint $j$ is $\sum_{q\le j/i}\Lambda(q)$. Subtract $j/i$, add its fractional part and group pairs with the same integer quotient. The triangle inequality gives one direction of the bound. The lower graph $1$ against one effective endpoint at $k$ realizes a single coefficient of size one, proving the converse. The zero quotient always contributes zero.

**Lean.** `exists_upper_endpoints`, `height_eq_quotient`, `mixed_height_finite_part`, `mixed_height_budget_iff`. [Proof](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/GluingIntegerGraphsAtTheirQuotientEndpoints.lean)
