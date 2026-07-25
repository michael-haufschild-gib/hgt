Let

[
N(\sigma,T)
=#{\rho=\beta+i\gamma:\zeta(\rho)=0,\ \beta\ge \sigma,\ 0<\gamma\le T},
]

counting zeros with multiplicity. Some authors use (|\gamma|\le T), which only changes the count by essentially a factor of (2).

## Density hypothesis

The **Density Hypothesis** asserts that, uniformly for (1/2\le \sigma\le1),

[
\boxed{N(\sigma,T)\ll_{\varepsilon}T^{,2(1-\sigma)+\varepsilon}.}
]

Equivalently, if one writes

[
N(\sigma,T)\ll_\varepsilon
T^{A(\sigma)(1-\sigma)+\varepsilon},
]

the hypothesis says (A(\sigma)\le 2) throughout the critical strip. ([arXiv][1])

Its meaning is that zeros substantially to the right of the critical line must become increasingly sparse. For example,

[
\begin{aligned}
\sigma=\frac12 &: \quad N(\sigma,T)\ll T^{1+\varepsilon},\
\sigma=\frac34 &: \quad N(\sigma,T)\ll T^{1/2+\varepsilon},\
\sigma=\frac9{10} &: \quad N(\sigma,T)\ll T^{1/5+\varepsilon}.
\end{aligned}
]

This is much weaker than RH. For every fixed (\sigma>1/2),

[
\text{RH}\quad\Longrightarrow\quad N(\sigma,T)=0,
]

whereas the Density Hypothesis permits infinitely many off-line zeros, provided they are sufficiently sparse. The Lindelöf hypothesis implies the Density Hypothesis. ([arXiv][1])

## What happened at (\sigma=3/4)

Ingham proved in 1940 that

[
N(\sigma,T)
\ll_\varepsilon
T^{\frac{3(1-\sigma)}{2-\sigma}+\varepsilon}.
]

At (\sigma=3/4), this becomes

[
N!\left(\frac34,T\right)
\ll T^{3/5+\varepsilon}.
]

Huxley’s later bound,

[
N(\sigma,T)
\ll_\varepsilon
T^{\frac{3(1-\sigma)}{3\sigma-1}+\varepsilon},
]

improves Ingham for (\sigma>3/4), but the two exponents coincide at exactly (3/4). That is why (3/4) became the stubborn transition point. ([arXiv][2])

Guth and Maynard proved

[
\boxed{
N(\sigma,T)
\ll
T^{\frac{15(1-\sigma)}{3+5\sigma}+o(1)}.
}
]

Consequently,

[
\boxed{
N!\left(\frac34,T\right)
\ll T^{5/9+o(1)}.
}
]

Numerically, the progression is therefore

[
\underbrace{\frac35}*{0.6000}
\quad\longrightarrow\quad
\underbrace{\frac59}*{0.5556}
\quad\longrightarrow\quad
\underbrace{\frac12}_{0.5000\text{, Density Hypothesis}}.
]

Their clean uniform corollary is

[
N(\sigma,T)
\ll T^{\frac{30}{13}(1-\sigma)+o(1)},
]

improving the previous uniform coefficient (12/5=2.4) to (30/13\approx2.3077), compared with the conjectured coefficient (2). ([arXiv][2])

### A precision about (13/25)

The frequently quoted improvement

[
\frac35\longrightarrow\frac{13}{25}
]

refers to an **auxiliary large-values count** (R) for a critical Dirichlet-polynomial configuration with (V=N^{3/4}) and (N=T^{4/5}). It is not, strictly speaking, the final exponent in the published bound for (N(3/4,T)). After passing through the full zero-detection machinery, the stated zero-density exponent at (3/4) is (5/9). ([arXiv][2])

So the advance is genuinely historic, but its scale is best understood as closing part of the exponent gap

[
0.6\ \longrightarrow\ 0.555\ldots,
\qquad\text{with the conjectural target }0.5,
]

not as approaching the RH conclusion (N(\sigma,T)=0).

[1]: https://arxiv.org/pdf/2607.04632 "A decades-long breakthrough in zero-density estimates and primes in short intervals"
[2]: https://arxiv.org/pdf/2405.20552 "New large value estimates for Dirichlet polynomials"
