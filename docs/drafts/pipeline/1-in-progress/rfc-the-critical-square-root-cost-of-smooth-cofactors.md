# The square-root endpoint for the actual smooth cofactors

- **Stage** 1-in-progress
- **Question** At the log-square cutoff, does the positive cofactor population itself obey an exact square-root bound?

Let \(y(X)=\lfloor\log(X+1)\rfloor^2\). The count through \(X\) of squarefree integers all of whose primes are at most \(y(X)\) admits precisely the power bounds with exponent strictly greater than one half. The same conclusion holds without imposing squarefreeness. The upper bound follows from Rankin's inequality and the subpolynomial Euler price.

For the endpoint, take an integer \(t\) tending to infinity, set \(m=\lceil t/(4\log t)\rceil\), \(k=2m\) and \(X=t^{4m}\). Then \(\log X\ge t\), so every product of \(k\) distinct primes through \(t^2\) is an admissible squarefree cofactor. If \(P=\pi(t^2)\), the prime number theorem and the ceiling give \((P-k)/(kt)\to1\). In particular \(P-k\ge4kt/5\) eventually. In \((2m)!\) the first half of the factors are at most \(m\), the second half at most \(2m\); hence \((2m)!\le k^k/2^m\). Therefore
\[
  \binom Pk\ge (P-k)^k/k!\ge(32/25)^m t^{2m}=(32/25)^m\sqrt X.
\]
The ratio to the exact square root is unbounded. This is a lower bound from actual distinct integer cofactors below the actual sharp cutoff, independent of Euler-product estimates. It identifies where an exact square-root bound for the positive part of the transport fails. It leaves the square-root-plus-epsilon target intact.
