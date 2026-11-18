# The signed complement beyond the integer wall window

[Section 2.16](../../../reports/review-1811/obstacles-summary.md#216-programme-to-close-ecs) requires a strict improvement over $\operatorname{Re}\zeta(1/2)m^2$ for the full oriented fractional test, with $m=\int\Phi$. Put $X=e^t$ and $h(X)=\sqrt{X\log X}$. The open contribution contains every $n>X+h(X)$ and the entire charge $-m^2/2$. Its sign on favorable centers and its cost on the rest of the test are unknown.

**State-weighted tail.** At a favorable center $u$ put $b=\lfloor u+h(u)\rfloor$, $a_j=\Lambda(j)-1$, $A_j=\sum_{u<n\le j}a_n$ and $w_j=m\,\mathrm{atom}(\Phi,j,\log u)$. The partial sum on $(b,L]$ is
\[
 w_L(A_L-A_b)+\sum_{b<j<L}(A_j-A_b)(w_j-w_{j+1}).
\]
The positive variations $w_{j+1}>w_j$ require an upper prefix. A [two-sided bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TwoSidedPrimePrefixesAtAlmostEveryCenter.lean) controls every future prefix from both $u$ and $u+h(u)$ after removing $o(X)$ centers from the original octave. The [variation estimates](ecs-signed-variation-of-the-weighted-complement.md) treat the adjacent band by the actual wall law and the remote tail by confinement. The remaining middle interval, the complement of the selected time set and the full square charge must all fit the same strict-margin budget.

**Verified integer window.** The adverse coefficient mass at width $H$ has order $H/h(X)$. At $H=h(X)$ the signed sum is $\gamma((\psi(X+H)-\psi(X))/H-1)+o(1)$ with $\gamma>0$, and its absolute value tends to zero in measure on every late octave. Both all-future prefix bounds hold on the same centers outside the vanishing exception. [Adverse mass](../3-formalized/ecs-critical-width-of-adverse-integer-mass.md) · [Signed sum](../3-formalized/ecs-signed-chebyshev-excess-at-the-critical-width.md) · [Joint exceptional set](../3-formalized/ecs-two-sided-prime-prefixes-at-the-wall.md).

**Time and divisor bounds.** The early integral at $U=T/6$ costs $O_\Phi(e^{-T/12})$. On $t>U$, replacing $S$ by the ordered row $L(t)-m/2$ over $d>e^{t/4}$ costs $O_\Phi(e^{-U/16})$ in absolute integral. [Paper proof](../2-fully-proven/ecs-early-mass-and-the-signed-large-divisor-tail.md).

**Same centers, all horizons.** Favorable centers in every late $(X,RX]$ carry a fixed positive mass under $K(\log X-\log u)\,du/u$. There is a common set where, for every $y\ge u$, $\psi(y)-\psi(u)\ge c(y-u)-c(RX)^{1/4}$, with $c<1$ chosen close to one. At $D=\lfloor u^{1/4}\rfloor$, replacing small-divisor multiples counts by their linear terms costs at most $D\log D$ uniformly in $y$. The literal integer reference remains. Passing to the full state weight requires paying the linear drift and the intervals on which its variation changes sign. [Fractional mass](../3-formalized/ecs-positive-measure-of-signed-critical-width-centers.md) · [All future increments](../2-fully-proven/ecs-all-future-prime-increments-at-the-same-centers.md).

**Ordinary-prime transfer.** Discarding $|P-S|>\varepsilon/(2(|m|+1))$ costs $O_{\Phi,\varepsilon}(e^{-T/40})$ in time measure. In each late octave the remaining set still carries fixed positive fractional-test mass and satisfies $mP>C-\varepsilon$ for the complete oriented complementary row $C$. [Paper proof](../2-fully-proven/ecs-ordinary-prime-complement-at-favorable-centers.md).
