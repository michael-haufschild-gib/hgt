# Even-gap covariance with one fractional-part average

Put $a_n(t)=n^{-1/2}\Phi(t-\log n)$, $c_n=1_{2\nmid n}(\Lambda(n)-2)$, $V(t)=\sum_n c_n a_n(t)$ and $K(v)=e^{-v/2}\{e^v\}$. Can one bound the distant even-gap covariance with one endpoint averaged against $K$?

The [signed test](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSignedFractionalPartAverageOnTheCriticalState.lean) of the polar-centered Mangoldt wave is $O((1+T)e^{-T/2})$. The odd integer reference has the same polar term, and its discrepancy $D_2$ satisfies $e^{rt}D_2\in L^2(\mathbb R)$ for every $0\le r<1/2$ by [sieved quadrature](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/WeightedSquareErrorAfterSieving.lean). The removed powers of two give $R_2(t)=\log 2\sum_{k\ge1}2^{-k/2}\Phi(t-k\log2)$. Negative support gives $R_2(t+\log2)=2^{-1/2}R_2(t)$ for $t\ge0$. Confinement bounds it on $[0,\log2]$ and by $O(e^{2t})$ for negative $t$. Thus $e^{rt}R_2\in L^2$ on the same lines. Since $e^{rv}K(v)\in L^2$, Cauchy–Schwarz bounds both absolutely convolved discrepancies by $O_r(e^{-rT})$. Hence $K*V=O_r(e^{-rT})$ at every positive center. The [prime trace](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Decay/TheLeftTraceUpToTheRateOfTheZeros.lean) gives $e^{-dt}V\in L^2(0,\infty)$ for $d>\Theta-1/2$. Choosing $d+\varepsilon<r<1/2$ gives
$$
 \int_0^\infty e^{\varepsilon T}|V(T)(K*V)(T)|\,dT<\infty
 \qquad(0\le\varepsilon<1-\Theta).
$$

For the pair sum, truncate the averaging variable to $|T-t|\le R$ first. Confinement gives absolute summability of each row at finite $R,T$. Sending $R\to\infty$ gives the covariance in this order. Every difference is even. The absolute contribution of any fixed additive shift is $O((1+T)^2)$ uniformly for $|n-m|\le e^T/2$. The unaveraged endpoint has $n\ge e^T$ and costs $O(e^{2T}(1+\log n)n^{-5/2})$. The averaged endpoint costs $O(e^{T/2}(1+\log m)/m)$ by $K(T-t)\le e^{(T-t)/2}$. Thus for $0<\alpha<1$ the signed sum over $|n-m|>e^{\alpha T}$, integrated on $[U,U+1]$, costs $O((1+U)^2e^{\alpha U})$. The unaveraged covariance uses both endpoints at the same time. Removing the average remains open.
