# Signed remainders below an ordered prime prefix

- **Stage** 1-in-progress
- **Question** At what scales can the signed mass below each ordered prefix be paid through its single-prime boundary?

For a squarefree prefix \(c\) let \(y=P^+(c)\), with \(P^+(1)=1\). For \(c\le X\), the signed mass in the subtree of integers starting with those factors, divided by \(-\mu(c)\), is
\[
 F_X(c)=-\sum_{X/c<m\le2X/c,\ P^-(m)>y}\mu(m).
\]
Each nonempty tail has a unique smallest factor. Separate the prime tails from the longer ones. If children are indexed only by \(q>y\) for which a longer tail occurs, this gives the exact recurrence \(F_X(c)=P_c-\sum_q F_X(cq)\), where \(P_c\) counts single prime tails and \(F_X(cq)\) omits the unit tail. Equivalently, omit the unit at every node and include every possible child. Each integer has a unique path. At the root \(F_X(1)=M(X)-M(2X)\) for \(X\ge1\).

The signed sum of a subtree can reach its parent only through its single-prime endpoints when exchanges merge the last two factors. A bottom-up matching pays all deeper unmatched endpoints through the current row if every child's survivors have the row's opposite sign and their total fits in \(P_c\). The difference is then the exact number of exposed endpoints. A uniform estimate on the signed root remainder is required even where this one-sign induction fails.

Lachand and Tenenbaum's Theorem 1.1 gives the signed rough **prefix** asymptotic in the range \(\exp((\log x)^{2/5+\varepsilon})\le y\le x/2\). Their formula (1.4) involves \(\rho'(u)\), where \(u=\log x/\log y\). At fixed \(u>1\), subtracting the two dyadic prefixes gives the predicted row fraction \(\rho(u-1)=-u\rho'(u)\). The mathematical target here is simultaneous matching with the actual integer row counts, including the sign and error at both endpoints as the prefix changes. [Lachand–Tenenbaum, corrected paper](https://tenenb.perso.math.cnrs.fr/PPP/note-som-crib.pdf)
