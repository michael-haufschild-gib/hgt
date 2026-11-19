# Poisson bound on the critical-line traces of confined states

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)
- **Lean:** `IsConfinedNullVector.poisson_spectrum`, `offLine_resolvent_re_neg`, `critical_line_window_le_reflected`, and `local_critical_line_mass`. [Poisson identity](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/ThePoissonSpectrumOfAConfinedState.lean#L351) · [Window bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/ThePoissonSpectrumOfAConfinedState.lean#L528)

For any confined null state $F$ at positive ratio, write $m_\gamma=|LF(i\gamma)|^2$ and $A_z=LF(z)LF(-z)$, counting all zero copies. The off-line Cauchy transform $\sum_z A_z/(p-z)$ has strictly negative real part on $\Re p>4$. For a finite off-line divisor,
$$\sum_{|\gamma-y|\le1}m_\gamma\le C_F/(1+y^2)\qquad(y\in\mathbb R).$$

**Proof.** Write $a$ for the confinement coefficient and $D$ for the Fourier power of $e^{-4u}F(u)$. Test the null equation by $F(\cdot+h)$ for $h\ge0$. The [unit tilt](qic-absolute-zero-traces-of-every-confined-state.md) gives square-summable zero traces for the state and its translate. The polarized zero formula and Plancherel give
$$\sum_\gamma m_\gamma e^{i\gamma h}+\sum_z A_z e^{zh}=-a e^{4h}\int D(x)e^{2\pi ixh}\,dx.$$
Cauchy–Schwarz gives $\sum_z|A_z|<\infty$. Since $|\Re z|<1/2$, Laplace transformation by Fubini yields, for $\Re p>4$,
$$\sum_\gamma\frac{m_\gamma}{p-i\gamma}
+a\int\frac{D(x)}{p-4-2\pi ix}\,dx=-\sum_z\frac{A_z}{p-z}.$$
The first term has nonnegative real part. The second has strictly positive real part because $\int D=\int F(u)^2e^{-8u}\,du>0$.

For a finite off-line divisor, add the real parts at $p=5\pm iy$. Each pair of resolvents sums to $2b/(b^2+y^2)$, with $b=5-z$. Both $|b\pm iy|$ exceed one, and $y^2=(b+iy)(b-iy)-b^2$ gives $(1+y^2)/|b^2+y^2|\le 2+|b|^2$. Each on-line copy with $|\gamma-y|\le1$ contributes Poisson weight at least $5/26$. The finite sum gives the bound uniformly in $y$.
