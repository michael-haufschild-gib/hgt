# Total variation of the removed quotient head

- **Stage** 1-in-progress
- **Question** Does recomputing the rough interpolation at every moving prime wall accumulate more than its square-root price?

For any fixed increments \(|a|\le\Lambda\), sieve by the primorial at each wall \(y_i\). Write \(H_i=\min(X_i,T_i)\). The paid head is
\[
 P_i=\sum_{d\le H_i}(\mu*a)(d)1_{(d,\prod_{p\le y_i}p)=1}.
\]
Indeed prime restriction preserves Dirichlet multiplication. If both \(H_i\) and \(y_i\) increase, each divisor enters the head at most once and exits at most once. Its entire contribution to variation is at most \(2|(\mu*a)(d)|\). Summing divisors first gives
\[
 \sum_{i<N}|P_{i+1}-P_i|\le 2\sum_{d\le H_N}|(\mu*a)(d)|\le 2H_N\log H_N .
\]
The bound holds for every subdivision, with repeated cuts allowed. The same proof covers ordinary primes, full Mangoldt weights and fixed signed masks of either. In particular the entire sequence of changes down to the hyperbola costs \(O(\sqrt X\log X)\), independently of the number or speed of the prime-wall changes.

Allow the arithmetic weight itself to change at every observation. If \(\sum_i|a_{i+1}(q)-a_i(q)|\le B\Lambda(q)\) at each prime power, the path costs at most \((2+B)H_N\log H_N\). Each divisor pays twice for entering and leaving and pays its signed coefficient changes at the arrival wall. Summing those changes over divisors uses \(\sum_{q\mid d}\Lambda(q)=\log d\). In particular every prime power may switch independently from one signed weight to another at its own observation time. All such switches together cost at most \(4H_N\log H_N\).

For the original prime-power center also retain \(-y_i\Psi(\lfloor X_i/y_i\rfloor,y_i)\). On each constant-wall interval its magnitude is increasing. If the final observation is \(X\) and \(y_i=\lfloor\log(X_i+1)\rfloor^2\), its total variation is at most twice the number of distinct walls times \(\max_{y\le b(X)}y\Psi(\lfloor X/y\rfloor,y)\). The latter is \(\sqrt X\exp(O(\log X/\log\log X))\). Thus the same scale pays all changes to the actual centered reading after its terminal cofactors have been removed. The signed smaller-cofactor reading remains.

The signed difference between the original floor-centered reading and the corrected interior equals \(-y\Psi(\lfloor X/y\rfloor,y)\) up to \(\sqrt X\log X\), uniformly in the selected Mangoldt weights. At the log-square wall the smooth lower bound therefore forces this particular difference to be negative at every large endpoint, with ratio tending to one against the negative center. Its magnitude also gives a lower bound for the full path variation from a fixed starting cut. The same identity keeps the negative smooth bias at a polynomial wall.

**Sharpness question.** For the natural log-square wall and the hyperbola head, the proposed total variation for the Mangoldt weight is asymptotic to \(e^{-\gamma}\sqrt X\log X/(4\log\log X)\). The square at \(d^2\) contributes \(|\mu_{b(d^2)}(d)|\log d\). A jump from \((k-1)^2\) to \(k^2\) in the primorial changes only coefficients divisible by a prime in that interval. The total absolute change at that jump is \(O(e^{k/2})\), by counting multiples, hence \(O(\sqrt X)\) over all such jumps. The remaining input is the weighted squarefree rough population at its moving cutoff. For ordinary primes the extra singly squared prime must exceed the cutoff; determining its contribution gives a second test of the leading coefficient.
