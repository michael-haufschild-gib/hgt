# Positive measure of favorable critical-width centers

Let $h(x)=\sqrt{x\log x}$ and $W(\log x)$ be the [signed initial integer window](../3-formalized/ecs-signed-chebyshev-excess-at-the-critical-width.md) of the forced state. For all $R>1$ and $\varepsilon>0$ there exists $\kappa>0$ such that, for every sufficiently large $X$, some measurable $A\subset(X,RX]$ satisfies
\[
 |A|\ge\kappa X,\qquad W(\log u)>-\varepsilon\quad(u\in A).
\]
Its logarithmic time measure is at least $\kappa/R$. Its mass under the actual fractional test at $T=\log X$ is at least $\kappa/R^2$.

**Frozen interval.** Fix $b>1$, let $H=h(X)$ and put $q_X(u)=[\psi(u+H)-\psi(u)]/H$. Translation of the integral and monotonicity bound $\int_X^{bX}q_X$ between $\psi(bX)-\psi(X+H)$ and $\psi(bX+H)-\psi(X)$. The prime number theorem and $H=o(X)$ yield mean $1+o(1)$ on $(X,bX]$. For $X\ge e$ and $X\le u\le bX$, monotonicity gives $H\le h(u)$, while $\log u\le b\log X$ gives $h(u)\le bH$. The linear Mangoldt bound at $h(u)$ therefore gives $q_X(u)\le bC$.

**Positive measure.** For $0<c<d<1$ the mean eventually exceeds $d$. Since $q_X\le c+bC\,\mathbf1_{q_X>c}$, the set $A=\{u\in(X,bX]:q_X(u)>c\}$ has measure at least $(d-c)(b-1)X/(bC)$. The variable-width slope on $A$ is at least $q_X(u)/b$. Choose $c$ close enough to $1$ and $1<b\le R$ close enough to $1$ that $\gamma(c/b-1)>-\varepsilon/2$. The signed window differs from $\gamma$ times the variable-width excess by $o(1)$ uniformly on the late ray, which gives the claim. Integrating $du/u\ge du/(RX)$ on $A$ yields the time bound.

**Fractional mass.** For $u\in A$, $v=\log(X/u)<0$, so $K(v)=e^{v/2}\ge e^v=X/u\ge 1/R$. Thus $\int_A K(\log X-\log u)\,du/u\ge\kappa/R^2$. For $t=\log u$ with $u\in A$, let $C(t)=m(\sum_{n>u+h(u)}(\Lambda(n)-1)a_n(t)-m/2)$. The wall condition kills all $n\le u$. Absolute convergence then gives $mS(t)=W(t)+C(t)>C(t)-\varepsilon$. The sign of $C$ on $A$ remains open. [riemannHypothesis_or_positive_measure_of_signed_criticalWidth_centers](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/PrimeSupportAcrossLateCriticalWidthWindows.lean).
