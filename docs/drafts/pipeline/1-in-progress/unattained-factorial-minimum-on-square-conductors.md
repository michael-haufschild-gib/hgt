# Unattained factorial minimum on square conductors

For the actual ordinary generator of \(mD_n\), can a balanced factorial presentation divide the logarithmic price equally between its Stirling entropy and its remainder?

At every sufficiently large \(n\) and every \(m>0\) with \(m^2\le c n^3\), every prime \(p\) in the negative outer window obstructs equality. This includes \(m=n\). The window has logarithmic prime mass at least \(n^2/12\). The reduced denominator is divisible by every such prime, so its signed exponent \(v_p\) is strictly negative. The uniform row estimate gives \(|v_p|\le 1+C m^2/\sqrt p\). Since \(p> n^2/3\), a fixed sufficiently small \(c>0\) gives \(-p<v_p<0\) for the entire window. Exact equality \(2S=\log q\) requires \(2p\mid v_p(q)\) at every prime, regardless of the horizon of the presentation.

Thus \(|\log q|/2\) is the infimum at every sufficiently large factorial horizon, yet no finite presentation attains it. The obstruction holds on an interval of primes whose total logarithmic weight grows quadratically. [Prime coordinate criterion](../3-formalized/prime-coordinates-of-balanced-factorials.md) · [Negative outer window](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ANegativePrimeWindowAtEveryMultiplicity.lean)

**Cost at the finite places.** Write $H(q)=\sum_p|v_p(q)|\log p=\log(UV)$. If $E$ is the exponentiated entropy of any factorial presentation, $v_p(E)\in p\mathbb Z$. Whenever $|v_p(q)|\le p$, it follows that $|2v_p(E)-v_p(q)|\ge |v_p(q)|$. On the diagonal and at every $p\ge e^{-8}n^2$ the bound $|v_p(q)|\ll 1+n^2/\sqrt p$ places each valuation in this interval for large $n$. Below $e^{-8}n^2$ the fixed prime profile is identically zero, so the total actual absolute valuation mass is $O(n^2)$ by the row-error bound. Consequently
$$
H(q_n)-O(n^2)\le \inf_{E}H(E^2/q_n)\le H(q_n)\asymp n^3.
$$
The upper bound is attained by the exact zero-entropy presentation. Thus even presentations whose real entropy almost bisects $\log q_n$ leave cubic total finite-place cost. At a horizon $L\ge10$ strictly above all prime divisors of $q$, the exact minimum of $H(E^2/q)$ is $\sum_p\operatorname{dist}(v_p(q),2p\mathbb Z)\log p$; the prime-coordinate classification realizes nearest residues independently.

The quadratic loss should have an explicit limit. For fixed $p$ the limiting normalized valuation is
$$
c_p=\frac{2}{\sqrt p}\{6H(\log p)-2H(\log p-\log4)-2H(\log p+\log4)\}.
$$
Only bounded primes contribute to $\sum |c_p|\log p$. For $p>K n^{4/3}$ the row-size bound gives $|v_p(q_n)|\le p$, so the nearest multiple of $2p$ saves nothing. Between the fixed cutoff and $K n^{4/3}$, both long overlaps vanish for large $n$ and second-order quadrature gives bounded floor exponents. Their entire possible saving is $O(n^{4/3})$. At each fixed prime the remaining distance to $2p\mathbb Z$ is at most $p$. This gives the proposed limit
$$
n^{-2}\left[H(q_n)-\min_E H(E^2/q_n)\right]\longrightarrow\sum_p|c_p|\log p>0.
$$
Strict positivity follows from a prime between $e^8$ and $4e^8$: there only the negative translated autocorrelation contributes.
