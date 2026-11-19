# The signed finite part has a lower energy threshold than quotient variation

Let $u_i,v_i$ be actual conductor multiplicities and $T_k=\sum_i(u_iv_{ki}+v_i u_{ki})$. Abel summation of $C_k=T_k-T_{k+1}$ against $\psi(k)-k$ gives $\sum_{k\ge1}T_k(\Lambda(k)-1)$. Consequently the kernel of the two-sided finite part after removing fractional boundaries and common diagonal is
$$
B(i,j)=\mathbf1_{i\mid j}(1-\Lambda(j/i))+\mathbf1_{j\mid i}(1-\Lambda(i/j))-\mathbf1_{i\ne j}J(i,j).
$$
The diagonal is $2$. For $s>1/2$ its absolute double sum is bounded by the product of the two individual norms $\|n^su_n\|_2\|n^sv_n\|_2$. Indeed $|B(i,j)|\le 3+\log i+\log j$ and both $n^{-s}$ and $n^{-s}\log n$ belong to $\ell^2$. This yields cutoff-independent exhaustion by normalized rounded integer conductors and their terminal jumps.

For $s\le1/2$, fix $u=\delta_1$ and allow $v$ on positive multiples of six. Those ratios have zero von Mangoldt weight and $B(1,6j)=1-J(1,6j)\ge1/2$. For $1\le j\le M$, take the integer multiplicities $v_{6j}=M!/j$. The signed pairing is at least $(M!/2)H_M$, while the opposing square energy at $s=1/2$ is exactly $6(M!)^2H_M$. Their ratio is at least $\sqrt{H_M/24}$, and decreasing $s$ only decreases the energy. Thus the expected signed threshold is $s>1/2$, while controlling the de la Vallée Poussin variation separately requires $s\ge3/2$. The difference comes from an exact relation between adjacent quotient cells on the same divisors.


For two exhausting sections, the oriented absolute incidence at quotient $k$ is $|u_i|\,|v_{ki}|\,|1-\Lambda(k)|$. Summing along multiples and then over $i$ gives an absolutely summable majorant whenever $1/r$ and $(1-\Lambda)/r$ are square summable. The real jet is uniformly dominated on $[0,1]$ by $2\sum_{i,j}|u_iv_j|$. At each cutoff, round the two actual conductor sequences toward zero at the same integer scale and take their terminal differences as integral endpoint jumps. Dominated convergence gives both oriented prime sums and the real integral in the signed limit.
