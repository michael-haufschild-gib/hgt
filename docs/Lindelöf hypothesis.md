The **Lindelöf hypothesis** concerns the growth of the Riemann zeta function on the critical line. It states that, for every (\varepsilon>0),

[
\zeta!\left(\frac12+it\right)\ll_{\varepsilon}(1+|t|)^{\varepsilon}.
]

Thus (\zeta(1/2+it)) should grow more slowly than every fixed positive power of (t). Equivalently, defining

[
\mu!\left(\frac12\right)
=\inf\left{\theta:\left|\zeta!\left(\frac12+it\right)\right|
\ll_\varepsilon |t|^{\theta+\varepsilon}\right},
]

Lindelöf asserts

[
\mu!\left(\frac12\right)=0.
]

It is weaker than, and implied by, the Riemann hypothesis. It is also equivalent to the moment bounds

[
\int_0^T\left|\zeta!\left(\frac12+it\right)\right|^{2k},dt
\ll_{k,\varepsilon}T^{1+\varepsilon}
]

for every positive integer (k). ([arXiv][1])

### Best known subconvexity exponent

For the Riemann zeta function in the (t)-aspect, the convexity bound gives exponent (1/4):

[
\zeta!\left(\frac12+it\right)\ll_\varepsilon |t|^{1/4+\varepsilon}.
]

Any exponent below (1/4) is called **subconvex**. As of July 2026, the best proven exponent remains Bourgain’s

[
\boxed{\theta=\frac{13}{84}\approx0.1547619},
]

meaning

[
\boxed{\left|\zeta!\left(\frac12+it\right)\right|
\ll_\varepsilon |t|^{13/84+\varepsilon}.}
]

This improves on the classical Weyl exponent (1/6\approx0.166667), but remains far from the Lindelöf prediction (0). Bourgain’s result appeared in the *Journal of the American Mathematical Society*; recent 2025–2026 sources still identify (13/84) as the best non-explicit asymptotic exponent. ([American Mathematical Society][2])

Strictly speaking, one should say

[
\mu!\left(\frac12\right)\leq \frac{13}{84},
]

not that (\mu(1/2)=13/84), since the true value is unknown and Lindelöf predicts it is (0).

[1]: https://arxiv.org/pdf/2509.20335?utm_source=chatgpt.com "A survey of moment bounds for $\zeta(s)$: from Heath ..."
[2]: https://www.ams.org/jams/2017-30-01/S0894-0347-2016-00860-3/?utm_source=chatgpt.com "Journal of the American Mathematical Society"
