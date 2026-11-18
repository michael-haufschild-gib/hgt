# Ordinary-prime comparison on favorable centers

On the forced state put $m=\int\Phi$, $x=e^t$, $h=\sqrt{x\log x}$ and
\[
 C(t)=m\left(\sum_{n>x+h}(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)-m/2\right).
\]
For each $\varepsilon>0$ there is $k>0$ such that every sufficiently late $(T,T+\log2]$ contains a measurable $B$ with
\[
 \int_B K(T-t)\,dt\ge k,\qquad mP(t)>C(t)-\varepsilon\quad(t\in B).
\]
On the same $B$ the [large-divisor lower bound](ecs-all-future-prime-increments-at-the-same-centers.md) holds for every upper endpoint $y\ge e^t$.

**Selection.** At height $X=e^T$ take favorable centers $A\subset(X,2X]$ with signed first window $W(\log u)>-\varepsilon/2$ and $|A|\ge\kappa X$. Then $B_0=\log A$ has length $\int_A du/u\ge\kappa/2$. Absolute convergence and the wall support give $mS=W+C$. Thus $mS(t)>C(t)-\varepsilon/2$ on $B_0$.

**Transfer.** The sum of the two sign-part distances between $P$ and $S$ equals $|P-S|$ pointwise. Its [absolute tail integral](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheIntegratedErrorInThePrimeSquareLayer.lean) over $t>T$ is $O_\Phi(e^{-(T-1)/40})$. Remove from $B_0$ the points with $|P-S|\ge\varepsilon/(2(|m|+1))$. The removed length tends to zero, leaving at least $\kappa/4$. On the remaining points $|m(P-S)|\le\varepsilon/2$. For $T<t\le T+\log 2$, $K(T-t)=e^{(T-t)/2}\ge1/2$, so $k=\kappa/8$ suffices. The sign of $C$ and the rest of the original fractional test remain open.

**Whole-test error on the same centers.** For $I_T=(T/6,6T]$, every measurable $D$ satisfies
\[
 \int_D |m P_\Phi(t)-\mathbf1_{I_T}(t)m S(t)|K(T-t)\,dt
 \ll_\Phi e^{-T/240}.
\]
The [exterior estimates](../3-formalized/ecs-exterior-mass-of-the-original-fractional-test.md) pay $O_\Phi(e^{-T/12})$ on the left and $O_\Phi(e^{-T/10})$ on the right. In the middle use $K\le1$ and the signed prime-square transfer at $V=T/6-1$, whose tail starts at $V+1$. The square charge in $mS$ is $-m^2/2$ throughout $I_T$. Taking $D$ to be the complement of the favorable time set uses the same error bound; its signed middle contribution is still required.

**Complete middle complement.** Let $C(t)=m\sum_{n\notin J_t}(\Lambda(n)-1)a_n(t)-m^2/2$, where $J_t$ is the actual first window. The [absolute first-window estimate](../1-in-progress/ecs-first-window-in-the-original-fractional-test.md) and $mS=W+C$ yield
\[
 \sup_{D\ \mathrm{measurable}}\int_D |mP(t)-\mathbf1_{I_T}(t)C(t)|K(T-t)\,dt\longrightarrow0 .
\]
The normalized state is unique up to sign. Changing its sign reverses both $m$ and each atom, so the oriented first-window readings agree pointwise for the two representatives. The triangle inequality then applies on the same $D$, including the complement of the original favorable set. Lean verification pending.
