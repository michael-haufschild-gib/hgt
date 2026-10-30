# Finite-source completion and the terminal dual boundary

**ID:** completed-arithmetic-forms-terminal-completion  
**Stage:** Formalized  
**Type:** Arithmetic covariance domain and sharp dual norm

For an increment packet supported on $1\le j\le T$, write
$M=\sum_j c_j$ and complete its accumulated energy by
$$\mathcal C_T(c)=C_T(c)+\frac{M^2}{T+1}
=\sum_{j,k\le T}\frac{c_jc_k}{\max(j,k)}.$$
The added term records the terminal accumulated mass.
Writing $a_j=c_j/j$ identifies the completed kernel with $\min(j,k)$.

For a coupling $b$, put $F_0=0$, $F_j=jb_j$ for $1\le j\le T$, and
$F_{T+1}=F_T$. The sharp dual norm is
$$\sup_c\left(2\sum_{j\le T}c_jb_j-\mathcal C_T(c)\right)
=\sum_{j=1}^T(F_j-F_{j-1})^2.$$
The maximizing increment is
$$c_j=j(2F_j-F_{j-1}-F_{j+1}),\qquad 1\le j\le T.$$
Thus finite source support removes the terminal Dirichlet edge. A probe
extended by zero beyond $T$ instead retains the terminal edge $F_T^2$;
the two domains have different dual costs.

Let $Q=T+1$ and $\widetilde F_j=F_j-jF_T/Q$. Its endpoints vanish and
$$D_Q(\widetilde F)=D_T(F)-F_T^2/Q.$$
The existing exact bridge completion gives
$$\mathcal C_T(c)-2\langle c,b\rangle+D_T(F)
=C_T(c-c_*)+\frac{(M-F_T)^2}{Q}.$$
The bridge inverse at its final interior node gives $\sum_j(c_*)_j=F_T$,
so this is exactly $\mathcal C_T(c-c_*)$. The complete covariance has zero
radical on its source coordinates, so equality determines every interior
optimizer coordinate.

Source extension has the exact law
$$\mathcal C_{T+1}(c)-\mathcal C_T(c)
=\frac{c_{T+1}(2M_T+c_{T+1})}{T+1}.$$
It increases energy exactly when this numerator is nonnegative. Cancelling
the previous total mass removes its entire terminal square.

**Lean:** `CompletedArithmeticForms/TerminalCompletion.lean`.
`finiteSourceEnergy_eq_covariance`, `finiteSourceEnergy_le_succ_iff`,
`finiteSourceMaximizer_eq_localDifference`, `finiteSourceMaximizer_mass`,
`finiteSourceEnergy_completion`, `finiteSourceEnergy_eq_zero_iff`,
`finiteSourceEnergy_schur_equality_iff`, and `finiteSourceDualCost_isGreatest`.
The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
