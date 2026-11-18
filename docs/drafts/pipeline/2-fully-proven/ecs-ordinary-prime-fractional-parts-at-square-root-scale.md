# Ordinary-prime fractional parts at square-root scale

Put
\[
 R(x)=\lim_{Y\to\infty}\left(\sum_{p\le Y}\log p\,\{x/p\}
 -x(\log(Y/x)+1-\gamma)\right).
\]
For $x\ge1$ this limit exists and $R(x)/\sqrt x\to\zeta(1/2)<0$ as $x\to\infty$.

The [full Mangoldt limit](../3-formalized/ecs-fractional-part-average-of-the-mangoldt-measure.md) is $O(1+\log x)$. Subtracting the absolute sum over $p^j$, $j\ge2$, leaves $R(x)$: at fixed $x$, each omitted term is bounded by $x\log p/p^j$. For $j\ge3$, $\{x/p^j\}/\sqrt x\le p^{-j/2}$ and each term tends to zero. Dominated convergence makes their total $o(\sqrt x)$.

The square term divided by $y=\sqrt x$ is $y^{-1}\sum_p\log p\,g(p/y)$, $g(v)=\{v^{-2}\}$. This measurable test is bounded by $2/(1+v^2)$ for $v\ge0$ and continuous off the countable set $\{0\}\cup\{n^{-1/2}: n\ge1\}$. In the [dilated Chebyshev measure](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/DilatingTheOrdinaryPrimeMeasure.lean), the rescaled reading of almost every mass bin tends to its coordinate. Dominated convergence gives $\int_0^\infty g(v)\,dv$. Substitution $v=e^{-w/2}$ and the [fractional-part Mellin integral](../../../../formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean) identify that positive integral with $-\zeta(1/2)$.

The sign is for this renormalized fractional-part sum. The one-sided estimate on the unaveraged ordinary-prime error remains open.
