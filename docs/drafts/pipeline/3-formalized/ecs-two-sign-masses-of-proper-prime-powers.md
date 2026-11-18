# The two sign masses of the proper prime powers

For a continuous critical-state representative $\Phi$, set $a_{p,k}(t)=(\log p)p^{-k/2}\Phi(t-k\log p)$, $k\ge2$. For either sign $s=\pm1$,
\[
 \max_{0\le c_{p,k}\le1}\sum_{p,k\ge2} c_{p,k}s a_{p,k}(t)
 =\sum_{p,k\ge2}(s a_{p,k}(t))_+
 \longrightarrow \tfrac12\int_{\mathbb R}(s\Phi(u))_+\,du .
\]
The maximum allows independent selection of every exponent of every prime at every time. Absolute convergence follows from confinement. Selecting exactly the positive terms attains the maximum.

The [dilated prime number theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/DilatingTheOrdinaryPrimeMeasure.lean) applied to $g=(s\Phi)_+$ gives the square-layer limit $\frac12\int g$. For $k\ge3$, each fixed atom eventually leaves the support. The summable majorant $\|\Phi\|_\infty\sum_{p,k\ge3}(\log p)p^{-k/2}$ gives a zero limit for their combined absolute contribution. The same proof with $g=|\Phi|$ gives total variation $\to\frac12\int|\Phi|$.

Every thinning of the proper powers therefore has bounded late sign mass. The ordinary-prime contribution remains open. Lean proves the unconditional disjunction in `riemannHypothesis_or_properPower_sign_extrema`. [Prime-power limits](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ThePrimeNumberTheoremOnTheState.lean) · [Sharp extrema](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheTwoSignMassesOfTheProperPrimePowers.lean)
