# The prime-square obstruction below the half exponent

Let $v(n)=\prod_p 1/v_p(n)!$, $h=v*\mu$ and $c=\sum h(n)/n$. The positive factorial count and its dyadic ordinary-prime difference $G$ have square-root error. [Endpoint theorem](../3-formalized/the-positive-companion-to-the-prime-parity-count.md)

For sharpness below one half, the Euler factor of $\zeta(2s)(\sum h(n)n^{-s})^2$ is $e^{2z}(1-z)/(1+z)$ at $z=p^{-s}$. It is nonzero and starts with $1+O(z^3)$. Its product is holomorphic and nonzero near $s=1/2$. The square of the correction therefore has a simple zero there. A power saving below one half would continue the correction meromorphically across that point by partial summation and division by zeta, contradicting the integer order of a meromorphic square.

Even cutoffs suffice for the lower bound. Write $A(N)=\sum_{n\le N}v(n)-1-cN$. The prime sum of $G$ at $2N$ is $A(2N)-2A(N)$. If its modulus is at most $CN^b$ with $0\le b<1/2$, take $K=C/(2-2^b)$ and $g(N)=|A(N)|-KN^b$. Then $g(2N)\ge 2g(N)$. Positive $g(N)$ would imply $g(4^jN)\ge4^j g(N)$, whereas the endpoint estimate gives $g(4^jN)\le13\cdot 2^j\sqrt N$. This proves the same impossibility below one half for the uncentered sum.
