# Limit of the proper prime-power contact on square conductors

For $D_n=e_1+2e_{n^2}-e_{(2n+1)^2}$, write $P_{\rm full}$ and $P_{\rm ord}$ for the integrated prime contacts, before flooring. Both $P_{\rm full}(D_n)-P_{\rm ord}(D_n)$ and $Q(D_n)+P_{\rm ord}(D_n)$ have finite limits through **all** integer conductors.

## Proof

The cumulative proper-power mass $A(x)=\psi(x)-\theta(x)$ satisfies $A(x)/\sqrt x\to1$. The Chebyshev decomposition bounds it below by $\psi(\sqrt x)$ and above by $\psi(\sqrt x)+\psi(x^{1/3})+\psi(x^{1/5})$. Apply the prime number theorem at $\sqrt x$ and the linear Chebyshev upper bound to the two smaller terms. [Prime number theorem](../../../../formal/GaloisForLFunctions/RHTower/ChebyshevPsiErrorInputs.lean)

Let $H$ be the cubic-spline autocorrelation, $a=e^{-9}$, $b=e^8$, and $W(v)=2H(-\log v)/\sqrt v$. Abel summation on $(aX,bX]$ gives the normalized proper-power reading
\[
W(b)\frac{A(bX)}{\sqrt X}-W(a)\frac{A(aX)}{\sqrt X}
-\int_a^b W'(v)\frac{A(Xv)}{\sqrt X}\,dv.
\]
The limit is $J=W(b)\sqrt b-W(a)\sqrt a-\int_a^b W'(v)\sqrt v\,dv$. Integration by parts gives $J=\int_a^b H(-\log v)\,dv/v=\int_{-8}^8 H(u)\,du=1$, since $H$ is the normalized eight-box spline. Chebyshev's global bound $A(y)\ll\sqrt y$ supplies domination. This is exactly the full long-lag sum with weight $2H(\log X-\log k)/\sqrt k$ since $H$ vanishes outside $[-8,8]$. [Spline support and atom pairs](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeProfileOfThreeSquareConductors.lean)

Put $s=\log n^2$, $t=\log(2n+1)^2$, and $\delta=t-s\to\log4$. For $s>8$ the two backward long lags vanish. The forward lags contribute $2J-J$ in the limit. The remaining profile at $\ell=\log k$ is $6H(-\ell)-2H(-\ell+\delta)-2H(-\ell-\delta)$. Its nonzero rows belong to one fixed finite set once $0\le\delta\le\log9$. Each row converges by continuity. This proves convergence of the entire proper-power contact. Since $Q+P_{\rm full}$ tends to minus the limiting archimedean jet, subtraction gives the asserted ordinary-prime discrepancy. [Jet limit](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheArchimedeanLimitOnTheSquareConductors.lean) · [Exact jet discrepancy](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OriginalSectionsAtDiagonalMultiplicity.lean)

For the actual generators, uniformly in all $m\ge n$, the normalized excess $(\log d_{\rm full}-\log d_{\rm ord})/m^2$ tends to the proper-power limit. Likewise $(\log d_{\rm ord}+V_{\rm ord})/m^2+Q(D_n)$ tends to the ordinary-contact discrepancy limit. Both floor-corrected mesh errors are $O(n)$ before normalization, hence $O(1/n)$ throughout this range. [Full prime mesh](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheFullPrimeIdealAtDiagonalScale.lean) · [Ordinary prime mesh](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheCoefficientIndependentPrimeMeshError.lean)
