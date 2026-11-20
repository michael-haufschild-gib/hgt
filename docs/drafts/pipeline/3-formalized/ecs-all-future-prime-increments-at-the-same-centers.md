# All future prime increments at the same centers

For $0<c<1$ and $R>1$ there exists $\kappa>0$ such that every sufficiently late $(X,RX]$ contains a measurable $A$ of length at least $\kappa X$ with
\[
 \sum_{u<n\le y}(\Lambda(n)-1)\ge -(1-c)(y-u)-c(RX)^{1/4}-1
 \qquad(u\in A,\ y\ge u).
\]
The same centers serve every upper endpoint on the infinite ray.

**Lower envelope.** Set $g(y)=\psi(y)-cy$ and $M(u)=\inf_{y\ge u}g(y)$. The prime number theorem gives $g(y)/y\to1-c>0$. Thus $M$ is finite, increasing and $M(u)/u\to1-c$. For the lower limit, any $0<s<1-c$ eventually satisfies $g(y)\ge sy\ge su$ for every $y\ge u$. The upper limit follows from $M(u)\le g(u)$.

**Rise across a cell.** For $H>0$ write $\Delta_H f(u)=f(u+H)-f(u)$. Then $0\le\Delta_H M(u)\le\Delta_H\psi(u)$. Indeed, for $y\ge u+H$ one has $M(u+H)\le g(y)$, and for $u\le y<u+H$ one has $M(u+H)\le g(u+H)\le g(y)+\Delta_H\psi(u)$. Take the infimum. Also $M(u)\ge\min(g(u)-cH,M(u+H))$. Hence wherever $\Delta_H M(u)>0$, every $y\ge u$ satisfies $g(y)\ge M(u)\ge g(u)-cH$.

**Many centers.** Freeze $H=(RX)^{1/4}$ on $(X,RX]$. The interval sieve gives $\Delta_H\psi(u)\le CH$ throughout. The integral of $\Delta_HM/H$ equals the difference of the two endpoint means of $M$. Since $H=o(X)$, its average on $(X,RX]$ tends to $1-c$. Thus $A=\{u\in(X,RX]:\Delta_H M(u)>0\}$ has positive relative measure. The literal integer reference costs $\lfloor y\rfloor-\lfloor u\rfloor\le y-u+1$, giving the claim.

**Critical width.** At $y=u+\sqrt{u\log u}$ the additive error divided by the width tends uniformly to zero. Taking $c$ sufficiently close to one, the [state wall law](../3-formalized/ecs-signed-chebyshev-excess-at-the-critical-width.md) makes the signed reading exceed any prescribed negative level at the same centers. For arbitrarily large $y-u$, the linear drift remains.

**Signed divisor prefix.** Set $D=\lfloor u^{1/4}\rfloor$, $a_d=-\mu(d)\log d$ and $N_d=\lfloor y/d\rfloor-\lfloor u/d\rfloor$. The [floor inversion](../../../../formal/GaloisForLFunctions/RHTower/FermiNymanLogMobiusHead.lean) gives $\Delta\psi=\sum_d a_d N_d$. Keep every $d>D$ and the full reference $-N_1$. Replacing $N_d$ by $(y-u)/d$ only for $d\le D$ changes the signed count by at most $D\log D$, uniformly in $y$. Indeed $|N_d-(y-u)/d|\le1$ and $|a_d|\le\log D$. The same lower bound for the retained expression therefore loses at most $D\log D=o(\sqrt{u\log u})$. The full state-weighted complementary row remains open.

**Lean.** [positive_measure_of_all_future_centered_mangoldt_increments, centered_count_sub_lateDivisor_le, criticalState_all_future_prefixes_at_favorable_state_centers, riemannHypothesis_or_all_future_prefixes_at_favorable_state_centers](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/AllFuturePrimeIncrementsAtTheSameCenters.lean): the lower envelope, the fourth-root cell sieve, the positive-measure centers for every `c` and `R`, the signed reading at the critical width on the same centers, and the `D log D` cost of the signed divisor prefix.
