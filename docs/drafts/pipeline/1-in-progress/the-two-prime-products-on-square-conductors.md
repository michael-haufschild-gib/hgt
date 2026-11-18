# The two prime products on square conductors

For $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$ write the ordinary generator of $mD_n$ as $U/V$ in lowest terms. The [square-root range](../3-formalized/prime-contact-products-at-small-multiplicity.md) gives $\log U=O(m^2)$ below $c\sqrt n$. Does the opposite bound $\log U,\log V\asymp nm^2$ hold at every $m\ge C\sqrt n$ and large $n$? At $m=n$ this would locate the RH comparison in the difference of two logs of order $n^3$.

Let $H(t)=\int B(u)B(u+t)\,du$. At lags $q=n^2v$ for $v$ in a fixed compact subset of $(0,\infty)$, the only possible large-$n$ contacts run from the low graph to one of the two upper graphs. Their continuous weight before $2/\sqrt q$ is $2H(\log v)-H(\log(v/(2+1/n)^2))$. On a closed interval inside $(e^{-8},4e^{-8})$ only the positive term survives. On a closed interval inside $(e^8,4e^8)$ only the negative term survives. Strict interior positivity of $B$ gives uniform lower bounds there. The mesh error is $O(1/(m\sqrt q))$ before dilation. After dilation the rows have size at least $c m^2/n$ with their respective signs. Above $C\sqrt n$, flooring preserves a fixed fraction. The prime number theorem supplies $\gg n^2$ log mass in both intervals.

**Proposed common leading coefficient.** When $m/\sqrt n\to\infty$, divide both logarithms by $nm^2$. Their expected common limit is
\[
 2\int_0^\infty [2H(\log v)-H(\log(v/4))]_+\,\frac{dv}{\sqrt v}.
\]
The positive and negative parts have equal integral since dilating $v$ by four doubles $dv/\sqrt v$. The bounded-lag contacts contribute $O(m^2)$. Floor errors cost $O(n^2)$, uniformly in $m$. The unresolved comparison on the diagonal is $\log U-\log V\le O(n^2)$.

Replacing $(2n+1)^2$ by $4n^2$ should cost only $O(1)$ in the continuous log generator before dilation. Indeed $H$ is globally Lipschitz, the log shift changes by $2\log(1+1/(2n))\le 1/n$, and $\sum_{p\le Cn^2}(\log p)/\sqrt p=O(n)$. This leaves one fixed dyadic profile at scale $n^2$. Compact prime-measure convergence is available for both ordinary primes and Mangoldt weights. [Prime limits for compact tests](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/PoleMomentsFromSeparatedGraphContacts.lean)

**Rounding at fixed scale.** For $m^2/n\to\tau>0$, the limiting unrounded row at $q=n^2v$ is
\[
 R_\tau(v)=2\tau\,[2H(\log v)-H(\log(v/4))]/\sqrt v.
\]
Its integral is zero. The proposed limit of $n^{-2}\log(U/V)$ is $-\int\{R_\tau(v)\}\,dv$. A strict negative upper bound only needs one interval where $-1/2<R_\tau<0$. Such intervals lie just inside the upper support endpoint. A fixed interval works simultaneously for $m^2/n$ in any compact positive range. Uniform mesh error and the prime number theorem would then give exponential decay of the generator for every prescribed constant multiple of $\sqrt n$, even where the numerator itself grows exponentially.
