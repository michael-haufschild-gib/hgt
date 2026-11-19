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

For the original prime-power center also retain \(-y_i\Psi(\lfloor X_i/y_i\rfloor,y_i)\). On each constant-wall interval its magnitude is increasing. If the final observation is \(X\) and \(y_i=\lfloor\log(X_i+1)\rfloor^2\), its total variation is at most twice the number of distinct walls times \(\max_{y\le b(X)}y\Psi(\lfloor X/y\rfloor,y)\). The latter is \(\sqrt X\exp(O(\log X/\log\log X))\). Thus the same scale pays all changes to the actual centered reading after its terminal cofactors have been removed. The signed smaller-cofactor reading remains.
