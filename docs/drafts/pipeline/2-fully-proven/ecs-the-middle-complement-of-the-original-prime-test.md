# The original prime test on the signed middle complement

Let $\Phi$ be the forced state, $m=\int\Phi$, $a_n(t)=n^{-1/2}\Phi(t-\log n)$, and $P$ the ordinary-prime polar error. Put $I_T=(T/6,6T]$, $K(v)=e^{-v/2}\{e^v\}$ and $J_t=(e^t,e^t+\sqrt{e^t t}]\cap\mathbb N$. For the complete charged row $mS(t)=m\sum_n(\Lambda(n)-1)a_n(t)-m^2/2$ and its charged complement $C(t)=m\sum_{n>e^t+\sqrt{e^t t}}(\Lambda(n)-1)a_n(t)-m^2/2$,
\[
 \int_D |mP(t)-\mathbf1_{I_T}(t)mS(t)|K(T-t)\,dt\ll_\Phi e^{-T/240},
 \qquad
 \int_D |mP(t)-\mathbf1_{I_T}(t)C(t)|K(T-t)\,dt=o_\Phi(1).
\]
Both estimates are uniform in the measurable set $D$. They apply on any favorable set and on its complement. The signed integral of $C$ on the middle interval remains open. [Lean proof under verification](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheMiddleTimeComplementOfTheOriginalPrimeTest.lean).

**Time restriction.** The two [exterior estimates](../3-formalized/ecs-exterior-mass-of-the-original-fractional-test.md) cost $O_\Phi(e^{-T/12})$ and $O_\Phi(e^{-T/10})$. In $I_T$, use $K\le1$ and the [absolute prime-power transfer](../3-formalized/ecs-integrated-error-of-the-proper-prime-powers.md) at $V=T/6-1$. Its tail begins at $V+1$ and costs $O_\Phi(e^{-T/240})$. The entire square charge stays in the middle row.

**Removal of the first window.** Absolute convergence gives $mS=W+C$, where $W$ is the oriented first-window sum. Every integer $1\le n\le e^t$ has $t-\log n\ge0$, where the state vanishes. The [absolute integral of $W$](../3-formalized/ecs-first-window-in-the-original-fractional-test.md) tends to zero on the full original test. Normalized ground states at the threshold differ only by sign. Their continuous representatives therefore agree up to sign everywhere. Switching sign reverses both $m$ and the atom, so $W$ agrees pointwise for the representatives in the two estimates. The triangle inequality on $D$ proves the second bound. [Uniqueness of the normalized state](../../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L67).
