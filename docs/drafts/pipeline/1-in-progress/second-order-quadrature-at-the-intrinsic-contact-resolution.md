# Second-order quadrature at the intrinsic contact resolution

Does one absolute constant bound each unrounded contact error by $C/\sqrt p$, simultaneously for every integral divisor, horizon and multiplicity?

Write $r=\sum |a_i|>0$, $G(u)=f_a(u)f_a(u+\log p)$ and $F(x)=G(\log x)/x$. Both endpoints of the sampled interval vanish, so its right Riemann sum equals its trapezoidal sum. The first two derivatives of each translated cubic spline are uniformly bounded. Thus $|G|+|G'|+|G''|\le Cr^2$. On $x\ge1$,
$$F''(x)=x^{-3}(G''-3G'+2G)(\log x).$$
Consequently $\int_1^\infty |F''|\le Cr^2$. The composite trapezoid error is at most $(5/4)r^{-2}\int |F''|$. The squared mass cancels against the intrinsic resolution even for a single divisor without dilation. Summing with prime logarithms would bound the unrounded error by $O(\sqrt L)$ through lag $L$. On the square conductors the resulting $O(n)$ error is uniform in the multiplicity. The integer floor loss and the signed continuous prime sum still require separate estimates.

[Trapezoid bound](../../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean) · [Degree mesh](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/UniformQuadratureForPrimeContacts.lean)
