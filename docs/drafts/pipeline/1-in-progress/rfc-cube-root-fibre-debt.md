# The cube-root boundary for cofactor transport

- **Stage** 1-in-progress
- **Question** Can a single largest-pair matching cover every negative vertex whose ordered fibre has no positive vertex?

Write a negative source as \(cqr\) with \(q<r\) its two largest primes and put \(T=X/c\). The geometric obstruction of the ordered fibre is \(q^3\ge 2T\). If \(q\) is well below \(T^{1/3}\), two primes larger than \(q\) with product in \((T/q,2T/q]\) would give a positive vertex in the original fibre. This also tests fibres empty because of prime gaps.

For fixed \(0<d<1/2\), the expected ratio of the semiprime demand with smaller factor at least \(T^d\) to the ordinary prime supply is
\[
  \int_d^{1/2}\frac{dt}{t(1-t)}=\log((1-d)/d).
\]
At the cube-root boundary the proposed ratio is \(\log 2<1\). A uniform upper bound strictly below one already pays the entire geometric debt. The proof needs sharp prime counts in quotient windows and control of the transition at \(q=\sqrt T\). Having enough primes in a row pays its negative sources only. Its remaining positive primes must be retained with their signs when adjacent rows are joined.

A shorter upper-bound route uses the first Mertens prime sum. In the exponent interval \([1/3,1/2]\), \(t(1-t)\ge 2/9\). Bounding each large-partner window with the prime number theorem and summing \((\log q)/q\) gives an upper ratio \((9/2)(1/2-1/3)=3/4\), with room for endpoint perturbations. This suffices for coverage without evaluating the integral.
