# The integer weights after the original fractional test

Put $X=e^T$, $m=\int\Phi$, $A=\int e^{-v/2}\Phi(v)\,dv$, $N(s)=\sum_{k\ge1}k^{-1/2}\Phi(s-\log k)$ and $D(s)=N(s)-e^{s/2}A$. The whole tested weight $W_T(x)$ satisfies $W'_T(x)=m x^{-3/2}D(T-\log x)$. At the moving far edge the normalized derivative of the actual complementary weight tends to $-mA$. The sign of this coefficient is open. [Moving-edge theorem](../3-formalized/ecs-tested-state-weight-at-the-moving-far-edge.md).

**Positive weight below the test abscissa.** For $x=e^p$, $y=e^{T-p}$, the exact weight satisfies
\[
 e^{T/2}W_T(e^p)=m\int e^{v/2}\Phi(v)\{y e^{-v}\}\,dv.
\]
Under $s=e^{-v}$ the density is $h(s)=s^{-3/2}\Phi(-\log s)$ on $s>0$, extended by zero to $s\le0$. It belongs to $L^1$ and has mass $\int e^{v/2}\Phi(v)\,dv$. Averaging $\{ys+a\}$ over $0\le a\le1$ gives $1/2$. Translating $h$ by $a/y$ in the same integral bounds the error by $\sup_{0\le b\le1/y}\|h(\cdot+b)-h\|_1\to0$. At the actual far edge $p=\log(e^r+\sqrt{e^r r})$, the omitted time strip costs at most $|m|\int_{r-p}^0e^{v/2}|\Phi(v)|\,dv$ after the same scaling. Thus $e^{T/2}V_T(r)\to (m/2)\int e^{v/2}\Phi(v)\,dv>0$ whenever $r\to\infty$ and $T-p\to\infty$. Positivity uses the ground-state charge at $+1/2$. This identifies the sign of each low-abscissa complementary weight. The signs of its successive differences and their arithmetic sum still require control. Lean verification pending.

**Time-truncation error.** Put $a_n=\Lambda(n)-1$ and $E(Y)=\sup_{L\ge k\ge\lfloor Y\rfloor}|\sum_{k<n\le L}a_n/n|$. The [centered Mertens limit](../../../../formal/GaloisForLFunctions/RHTower/MertensSecondTheorem.lean) gives $E(Y)\to0$. For $R>\max(T,1)$ the signed integral over $t>R$ of every finite row through $L$ has absolute value at most
\[
 |m|e^{T/2} E(e^R)\int_{-\infty}^0 e^{-v/2}|\Phi(v)|\,dv .
\]
Indeed $v=t-\log n\le0$ and $K(T-t)=e^{(T-t)/2}$. At fixed $v$ the residual indices satisfy $e^{R-v}<n\le L$. Imposing the far-edge condition $n>u+\sqrt{u\log u}$ with $u=ne^v$ adds $e^{-v}>1+\sqrt{\log u/u}$. Since $\log u/u$ decreases for $u>e$, the surviving indices are still an interval. The same estimate holds for the true complementary row, uniformly in $L$.

For $0<d<3001/24000$, the [project strip](../../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean) and [prime error bound](../../../../formal/GaloisForLFunctions/RHTower/ChebyshevErrorExponentLaw.lean) give $|\psi(k)-k|\ll_d k^{1-d}$. Abel summation of $a_n/n$ bounds both endpoints by $O_d(k^{-d})$. The variation telescopes because $j^{1-d}(1/j-1/(j+1))\le (j^{-d}-(j+1)^{-d})/d$ by concavity of $x^d$. Consequently $E(Y)\ll_d Y^{-d}$. At $R=6T$ and $d=1/10$ the entire signed late contribution is $O_\Phi(e^{-T/10})$, uniformly through every finite row endpoint. Passing to infinite rows also requires convergence of their integrals on bounded time cuts. [Lean formalization in progress](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheLateTimeEndpointOfTheTestedIntegerRows.lean).

**Lower part of the middle range.** For $N\le X$ and $\theta>\Theta$, let $Q(x)=\psi(x)-\lfloor x\rfloor$. The endpoint of the tested Abel sum costs $O_\Phi(X^{-1/2}N^\theta)$ because $K(T-t)\le e^{(t-T)/2}$. Integrating the derivative of $W_T$ in $p=\log x$, the interior costs at most
\[
 C_\Phi\int_0^{\log N}e^{(\theta-1/2)p}|D(T-p)|\,dp
 \ll_{\Phi,\beta,\theta} X^{-\beta}N^{\theta-1/2+\beta}
 \qquad(0<\beta<1/2).
\]
The last bound is Cauchy–Schwarz against the [tilted integer variance](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/SubcriticalMeanSquareOfTheIntegerQuadrature.lean). The critical-window strip omitted from each tested coefficient costs $O_\Phi(X^{-1/2}\sqrt{\log(2n)/n})$ since its time width is $O(\sqrt{\log(2n)/n})$. Summing this error absolutely through $N$ costs $O_\Phi(X^{-1/2}\sqrt N\log^{3/2}(2N))$. Thus the proposed signed estimate for the actual complementary row is $o(1)$ through $N=X^a$ for $a<1/(2\Theta)$, by taking $\theta$ just above $\Theta$ and $\beta$ just below $1/2$. This estimate concerns the full time integral before selecting centers. Its Abel and moving-window bounds remain to be checked in Lean.

**Upper integer range on the middle time interval.** Put $X=e^T$, $k\ge X^4 e^s$ and $s\ge0$. For $t\le T$ and $n>k$, confinement gives $|\mathrm{atom}(\Phi,n,t)|\le C_\Phi e^{2t}/(\sqrt{k}\,n^2)$. Summing $(\log n+1)/n^2$ and integrating in $t$ costs $O_\Phi(X^2/\sqrt k)$. For $t>T$ impose $n>k$ in the translated reciprocal row above. Its lower index is now at least $\max(k,\lfloor e^T\rfloor)$. Subtracting the time tail at any $M\ge T$ costs $O_\Phi(\sqrt X\,k^{-1/8})$, using the ordinary prime error at $d=1/8$. On each bounded time interval confinement permits the ordered upper integer endpoint to tend to infinity. The complete signed contribution of $n>k$ on $(T/6,6T]$ therefore costs $O_\Phi(e^{-s/8})$ uniformly in $s,T$. The prime cancellation here uses the full time interval. Lean verification pending.

**Remaining estimate.** Control the signed middle range with the original orientation and the $-m^2/2$ charge. For the upper range, isolate the reciprocal polar row with its actual sign. The near-wall scale gives $C(q)=O_\Phi(e^{-r/2})$ and $q'e^{-q/2}\Phi(q)=O_\Phi(e^{-r/2})$.
