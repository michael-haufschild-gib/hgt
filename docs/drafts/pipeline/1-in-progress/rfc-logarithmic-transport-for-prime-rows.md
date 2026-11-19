# A uniform prime measure for moving cofactor rows

- **Stage** 1-in-progress
- **Question** Can sharp prime and semiprime rows be integrated in exponent coordinates with error uniform in both moving endpoints?

Let \(A(n)=\sum_{p\le n}(\log p)/p\), \(h>0\), and \(x_n=(\log n)/h\). Give integer \(n\ge2\) the interval \((A(n-1)/h,A(n)/h]\). Composite indices have zero length. Mertens' first theorem and \(n\le2(n-1)\) place both endpoints within \(\delta=C/h\) of \(x_n\), for one absolute constant. For \(1\le a\le b\) and \(F'=f\), compare each atomic term with the difference of \(F\) across its assigned interval. The mean value theorem bounds the discrepancy by \(K\delta\) times its length if \(f\) is \(K\)-Lipschitz. These intervals are consecutive. If \(|f|\le B\) on the enlarged window, the two endpoint corrections give
\[
 \left|\sum_{a<p\le b}\frac{\log p}{ph}f(x_p)-F(x_b)+F(x_a)\right|
 \le\delta\{2B+K(x_b-x_a+2\delta)\}.
\]

For \(f(t)=1/[t(1-t)]\), take \(F(t)=\log t-\log(1-t)\). On \([d,1-d]\) one may take \(B=d^{-2}\) and \(K=d^{-4}\). The resulting prime weight is exactly \(h/[p(h-\log p)]\). At \(h=\log T\), it is the normalized main term for the number of larger partners in \((T/p,2T/p]\). For \(T^d\le a\le b\le\sqrt T\) the prime-count error is uniformly small since \(T/p\ge\sqrt T\); the sum of the positive main weights is bounded uniformly in the endpoints. Thus the normalized count of actual ordered semiprimes should converge uniformly to \(F(x_b)-F(x_a)\).
