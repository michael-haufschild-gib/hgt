# The square and cube waves of a single quartet

For a right zero \(\rho\) of multiplicity \(m\), put \(W(t)=-2m\Re(t^\rho/\rho)\) and \(U(x)=\psi(x)-\theta(x)-x^{1/2}-x^{1/3}\). A single quartet gives
\[
 U(x)=W(x^{1/2})+W(x^{1/3})+O(x^{1/4}\log^2 x).
\]
Indeed, the [quartet equivalence](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/SingleQuartetSecularAndWallRigidity.lean) gives \(E(t)=\psi(t)-t=W(t)+O(\sqrt t\log^2t)\). Costa–Pereira bounds \(U(x)-E(x^{1/2})-E(x^{1/3})\) between zero and \((\log4+4)x^{1/5}\). Conversely, the displayed two-wave law gives \(Q(y)+Q(y^{2/3})=O(\sqrt y\log^2y)\) for \(Q=E-W\). Subtract the same relation at \(y^{2/3}\). The remaining \(Q(y^{4/9})\) is \(O(y^{4/9})\) by Chebyshev and \(\Re\rho<1\). Thus the two-wave law characterizes the single quartet. [Two-wave equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoProperPowerWavesCharacterizeASingleQuartet.lean)

The normalized [odd-quotient mean](../3-formalized/a-finite-prime-multiple-count-at-the-quarter-exponent.md) should carry both waves with multipliers \(\eta(s)/(1+s)\), at \(s=\rho/2,\rho/3\), where \(\eta(s)=(1-2^{1-s})\zeta(s)\). To evaluate a power mode, give integer \(d\) mass \(d^s-(d-1)^s\). Its test is \(H(N/d)\), where \(H(y)=y^{-1}\int_0^y(\lfloor t\rfloor\bmod 2)\,dt\). Replacing this mass by \(s t^{s-1}dt\) on \((d-1,d]\) costs \(O_s(1)\) over all cells: \(|H(N/d)-H(N/t)|\le(d-t)/d\), and \(\int_1^\infty t^{\Re s-2}\,dt\) converges. The continuous integral equals \(N^s\eta(s)/(1+s)\) by the triangular Mellin transform. The coefficient remainder transfers by discrete Abel summation at \(O(N^{1/4}\log^2 N)\). An independent inequality excluding the resulting prime wave is open.
