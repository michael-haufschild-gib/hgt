# The leading constant in both critical smooth sign populations

- **Stage** 1-in-progress
- **Question** What is the coefficient of \(\log X/\log\log X\) in the logarithm of each smooth sign population?

Put \(L=\log X\), \(F=L/\log L\), \(y=\lfloor\log(X+1)\rfloor^2\). For fixed \(a>0\), the predicted logarithm of the count of either squarefree sign at height \(X^a\), with all prime factors at most \(y\), is
\[
 \tfrac a2 L + \tfrac a2(1+\log(2/a))F+o(F).
\]
The unsigned count allowing repeated primes has the same expansion.

For \(s=1/2+c/\log y\) with bounded \(c\), partial summation of the prime number theorem gives, uniformly,
\[
 \sum_{p\le y}\log(1+p^{-s})=(e^{-c}+o(1))F,
 \qquad \sum_{p\le y}\frac{\log p}{1+p^s}=(2e^{-c}+o(1))L.
\]
In both sums first discard primes below \(\eta y\) at relative cost \(O(\sqrt\eta)\), then use \(p^{-c/\log y}=e^{-c}(1+o(1))\) on the remaining interval. The geometric Euler product has the same first asymptotic, because all quadratic and higher corrections cost \(O(\log y)\). Rankin's upper bound is minimized at \(c=\log(2/a)\).

For the lower bound exclude the prime two. On squarefree products of the remaining primes give each product weight proportional to \(n^{-s}\). The prime inclusion indicators are independent. Choose \(s\) so that the mean of \(\log n\) is \(aL-L^{2/3}\), using continuity and monotonicity between two fixed values of \(c\) straddling \(\log(2/a)\). The second asymptotic forces \((s-1/2)\log y\to\log(2/a)\). The variance is at most \(\log y\) times the mean. Chebyshev's inequality puts a fixed fraction of the weight in \([aL-2L^{2/3},aL-\log 2]\), where undoing the tilt costs only \(o(F)\) in the logarithm. Each sampled odd product and its double give one integer of each sign below \(X^a\). Recovery of the odd product makes both injections disjoint.

For the rough-part cutoff \(X^\gamma\), \(0<\gamma<1\), take \(a=1-\gamma\). The unsigned convolution upper bound costs \(X^s(X^\gamma)^{1-s}/(1-s)\) times the Euler product. A smooth product at height \(X^a\) and one prime in \((X^\gamma/2,X^\gamma]\) attain the same coefficient for each sign. Thus the leading power changes to \((1+\gamma)/2\), while the stated second coefficient uses \(a=1-\gamma\). For the smooth main term \(y\Psi(\lfloor X/y\rfloor,y)\), the coefficient is \((1+\log 2)/2\).

**Lean status.** The sharp coefficient needs the uniform prime asymptotics and the two-sided finite Euler tilt. The fixed-exponent prime asymptotics are `RHTower.tendsto_primeRpowSumIoc` and `RHTower.tendsto_primeRpowLogSumIoc`. The diagonal variance of the tilted log-product is `eulerTiltVariance_linearStat`.
