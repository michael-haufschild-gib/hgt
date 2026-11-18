# Early mass and the signed large-divisor tail

Let $\Phi$ be the continuous critical representative, $m=\int\Phi$, $A=\int e^{-u/2}\Phi(u)\,du$, and $a_n(t)=n^{-1/2}\Phi(t-\log n)$. Write $P$ for the ordinary-prime polar error, $S=\sum_n(\Lambda(n)-1)a_n-m/2$ and $K(v)=e^{-v/2}\{e^v\}$. For $U\ge0$,
\[
 \int_{t\le U} (|S(t)|+|P(t)|)K(T-t)\,dt\ll_\Phi e^{(5U-T)/2},
 \qquad
 \int_{t>U}|S(t)-(L(t)-m/2)|\,dt\ll_\Phi e^{-U/16}.
\]
Here $L(t)$ is the increasing-cutoff limit of $\sum_{e^{t/4}<d\le N}-\mu(d)\log d\,R_d(t)$ for the centered multiples row $R_d(t)=\sum_{d\mid n}a_n(t)-e^{t/2}A/d$. Both bounds hold for absolute integrals.

**Early mass.** Confinement gives $|a_n(t)|\le C e^{2t}/n^2$ for $n\ge1$, so coefficients bounded by $1+\log n$ cost $O_\Phi(e^{2t})$. Apply this to the integer and prime rows. On $t\le U$ the polar term $e^{t/2}A$ and the charge $m/2$ also cost $O_\Phi(e^{2U})$. Integrating $K(T-t)\le e^{(t-T)/2}$ gives the first estimate. In particular $U=T/6$ costs $O_\Phi(e^{-T/12})$ for $T\ge0$.

**Divisor cutoff.** Put $E=\sum_n\Lambda(n)a_n-e^{t/2}A$ and $D=\sum_na_n-e^{t/2}A$. Then $S-(L-m/2)=E-L-D$. The [moving-divisor theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheLargeDivisorMomentsOfThePrimeWave.lean) gives $e^{t/8}(E-L)\in L^2$ since $1/4+1/8<1/2$. The [integer quadrature bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/SubcriticalMeanSquareOfTheIntegerQuadrature.lean) gives $e^{t/8}D\in L^2$. Cauchy–Schwarz against $e^{-t/16}$ on the positive ray gives $e^{t/16}|E-L-D|\in L^1$ there. Restriction to $t>U$ yields the second estimate.

The full square charge remains in $L-m/2$. Its signed fractional reading on late time windows is open.
