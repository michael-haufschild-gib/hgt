# Vertical contacts of signed conductor divisors

**Route** ACS arithmetic sections on signed integer spline probes.

For conductor $n$, take the integral graph $Y=G_n(T)$ with
$G_n(T)=\sum_{d\mid n}\operatorname{rad}(d)T^d$. Its degree is $n$.
For distinct conductors the content of $G_i-G_j$ is $p$ at a ratio $p^r$
in either direction and $1$ otherwise. Indeed, the first changed power of
each prime gives a coefficient of absolute value $p$. When only the
$p$-exponent changes, every changed divisor contains $p$. Gauss's lemma
therefore computes the vertical order of one Sylvester determinant for two
thickened divisors, with the product of the graph multiplicities on each
pair. There is no triple correction.

On a log mesh put $w_i=\log(1+1/i)$. Give the lower graph signed weight
$\sqrt i\,w_i f_i$ and the upper graph weight $g_j/\sqrt j$.
At $j=it$ the product is $w_i f_i g_{it}/\sqrt t$. Round each weight
after dilation by $m$. At each base use one resultant for agreeing signs
and one for opposing signs. The difference of their log orders reads
the signed product. With mesh starting at $\lfloor\sqrt m\rfloor$,
rounding costs $O_{f,g,B}(m^{-1/2})$ after division by $m^2$.
Logarithmic quadrature then gives the full smooth prime pairing.

**Remaining problem.** Construct one effective object that pays the
same-sign contact debit together with the real-place diagonal and both
pole moments on every signed ray.
