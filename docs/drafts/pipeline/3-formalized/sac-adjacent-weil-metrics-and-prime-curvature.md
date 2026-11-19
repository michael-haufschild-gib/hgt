# Adjacent real Weil metrics bound the change in prime curvature

Let $S_d(x)=1+\cdots+x^{d-1}$ and $B_d=S_d^2-d^2x^{d-1}$. The centered real Weil entries $C_d(k)$ are moments of $(1-x)B_d(x)$. Rescaling the exponential increment for the reflected residue block gives $K_d(n)=\int_0^1x^{dn}S_d B_d\ell\,dx$, where $\ell(x)=(1-x)/(-\log x)$. A unit conductor shift multiplies the integrand by $x^d$, so the difference has density $x^{dn}(1-x)S_d^2 B_d\ell$.

Since $x\le\ell(x)\le1$ and $B_d(x)\ge0$, one obtains

$$\sum_{r,j<d} C_d(dn+r+j+1)\le K_d(n)-K_d(n+1)\le\sum_{r,j<d} C_d(dn+r+j).$$

Multiplying each density by $P(x^d)^2$ gives the same comparison for every continuous signed section. For polynomial sections expansion of the four finite sums recovers the actual shifted real Weil entries. Lean proves `prime_curvature_change_between_real_metrics` and `centeredBlockMetric_glued`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheRealMetricBoundsTheChangeOfPrimeCurvature.lean)
