# Signed remainders below an ordered prime prefix

- **Stage** 1-in-progress
- **Question** At what scales can the signed mass below each ordered prefix be paid through its single-prime boundary?

For a squarefree prefix \(c\) let \(y=P^+(c)\), with \(P^+(1)=1\). For \(c\le X\), the signed mass in the subtree of integers starting with those factors, divided by \(-\mu(c)\), is
\[
 F_X(c)=-\sum_{X/c<m\le2X/c,\ P^-(m)>y}\mu(m).
\]
Deleting the least prime gives \(F_c=P_c-\sum_q F_{cq}\); the unit tail is excluded at every node. Here \(P_c\) counts single-prime tails. At the root \(F_1=M(X)-M(2X)\) for \(X\ge1\).

Only single-prime endings can connect a subtree to its parent under largest-pair moves. Let \(P_c\) be the number of these endings and \(E_c\) the number left exposed after optimally matching descendants. The candidate bottom-up law is \(E_c=(P_c-\sum_q E_{cq})_+\). Each row buries \(D_c=(\sum_q E_{cq}-P_c)_+\) endpoints. The minimum-cover dual gives the same count: selecting the whole parent row costs \(P_c+\sum_q m_{cq}\), while omitting it forces all child rows and costs \(\sum_q(m_{cq}+E_{cq})\). Here \(m_c\) is the maximum number of disjoint pairs in the subtree. The signed discrepancy from the exposed row then obeys \(F_c-E_c=-D_c-\sum_q(F_{cq}-E_{cq})\). This retains cancellations between buried endpoints at different depths. A uniform estimate on the signed root remainder remains necessary.

Lachand and Tenenbaum's Theorem 1.1 gives the signed rough **prefix** asymptotic in the range \(\exp((\log x)^{2/5+\varepsilon})\le y\le x/2\). Their formula (1.4) involves \(\rho'(u)\), where \(u=\log x/\log y\). At fixed \(u>1\), subtracting the two dyadic prefixes gives the predicted row fraction \(\rho(u-1)=-u\rho'(u)\). The mathematical target here is simultaneous matching with the actual integer row counts, including the sign and error at both endpoints as the prefix changes. [Lachand–Tenenbaum, corrected paper](https://tenenb.perso.math.cnrs.fr/PPP/note-som-crib.pdf)

**Exact optimality target.** Replace a prime by two larger-than-prefix primes. Integers ending in a single prime after the same ordered prefix form a row of size \(P_c\). Consecutive rows in the prefix tree form a complete bipartite graph. If \(I_c,O_c\) are the minimum cover costs with the full row included or excluded, respectively, then
\[
 I_c=P_c+\sum_j m_j,\qquad O_c=\sum_j I_j,\qquad m_c=\min(I_c,O_c).
\]
Indeed, a partially selected row may be removed if all adjacent rows are covered; otherwise it must be included in full. Thus \(I_c-m_c=E_c\). Pair the available child endings with distinct parent primes. This attains the cover cost since \(m_c=\sum_jm_j+\min(P_c,\sum_jE_j)\). The missing formal step is to identify this weighted tree and its attaining matching with the integer graph at arbitrary depth.

For each fixed \(u>1\), the predicted fraction \(g(u)\) obeys \(g(u)=1-\int_1^{u-1}g(v)\,dv/v\) for \(u>2\), with \(g=1\) up to 2. The substitution \(v=(1-t)/t\) converts the quotient prime weights \(dt/[t(1-t)]\) to \(-dv/v\). Since \(g(u)=\rho(u-1)>0\), a uniform dyadic asymptotic on compact exponent ranges would give a matching at every fixed depth leaving only prime endings. The quantifiers matter: it would give a growing roughness range by diagonalization, with no square-root error at the unrestricted root.
