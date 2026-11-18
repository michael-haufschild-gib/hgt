# Signed covariance at odd additive gaps

Write $c(n)=1_{\mathbb P}(n)\log n-1$, $X=e^t$ and $G(y)=y^{-1/2}\Phi(-\log y)$ on $y>0$, extended by zero for $y\le1$. For odd positive gaps $d$ with $d/X\to h\ge0$, does
\[
X^{-1}\sum_{n\ge1}c(n)c(n+d)G(n/X)G((n+d)/X)
\longrightarrow -\int_0^\infty G(y)G(y+h)\,dy
\]
hold along every sequence $X\to\infty$? At $h=0$ the answer predicted by the unit norm is $-1$. This would evaluate half the gap classes throughout $d=o(e^t)$, including gaps much larger than $t$.

For $X>2$ the product of the prime indicators contributes exactly zero. Expand the two single-prime terms, shifting the second index from $n$ to $p=n+d$. They test the dilated prime measure with $G(y)G(y+d/X)$ and $G(y-d/X)G(y)$. Both continuum integrals agree after translation. The remaining unweighted integer sum is the Riemann sum of the first test. The tests converge locally uniformly as $d/X\to h$ and their tails have a common integrable majorant for bounded $d/X$. The surviving obstruction at even gaps is the genuine two-prime term.

After replacing the integer reference by its normalized restriction to odd integers, every odd-gap pair vanishes. [Growing prime sieve](../3-formalized/ecs-growing-sieve-for-integer-centering.md).
