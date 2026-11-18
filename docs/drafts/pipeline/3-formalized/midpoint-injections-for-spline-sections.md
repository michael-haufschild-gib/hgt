# Midpoint injections for spline sections

There exists a prime $p$ and a fixed $b=e_p\pm e_1$ of positive Weil degree with the following property. Extend $b$ and any integer divisor $a$ by zero to a common horizon. For all sufficiently large $k$, the three degrees at $kb,kb+a,kb-a$ are positive. Writing $S(c)$ for the ordinary small sections of $c$ gives

\[
 \lim_{m\to\infty}\frac{\log |S(m(kb+a))|+\log |S(m(kb-a))|-2\log |S(mkb)|}{m^2}=2Q(a).
\]

The ordinary log count has leading coefficient $\max(Q,0)$. The leading $k^2Q(b)$ term makes all three degrees positive. The parallelogram identity gives the stated limit. Under RH every nonzero displacement has strictly positive degree, so the middle section set squared eventually embeds in the product of the outer ones. Conversely, cofinal injections imply $Q(a)\ge0$ by the limit. Thus RH is equivalent to obtaining these injections for every $a$ and all sufficiently large translations. The arithmetic construction of such injections remains open. Already for the displacement $b$ at midpoint $3b$, every injection loses precision at two prescribed places. One prescribed place admits an explicit injection for all large multiplicities. [Congruence obstruction and denominator growth](../5-failed/congruences-obstruct-midpoint-section-injections.md)

[MidpointProductsOfSmallSections.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/MidpointProductsOfSmallSections.lean)
