# Free-terminal variation for the actual Euler-deletion source

**ID:** completed-arithmetic-forms-euler-terminal-cost  
**Stage:** Formalized in Lean 4  
**Type:** Actual-source completion with a joint cutoff allowance

Let $c_j$ be the complete compensated Euler-deletion increment at $1\le X<M$,
$F_{X,M}$ its full error energy, and $M_T=\sum_{j\le T}c_j$.
The actual cumulative identity gives $M_T=1-\mathrm{modular}(X,M,T)$ for $T\ge1$;
at $T=0$ the sum is zero. Hence $|M_T|\le M+1$ at every cutoff.
The proved source-tail bound and this endpoint bound give
$$\left|F_{X,M}-\left(C_T(c)+\frac{M_T^2}{T+1}\right)\right|
\le\frac{(M+1)^2}{T+1}.$$
The free-terminal dual variation has the actual-source bound
$$2\sum_{j\le T}c_jb_j-F_{X,M}
\le\sum_{j=1}^T\bigl(jb_j-(j-1)b_{j-1}\bigr)^2+
\frac{(M+1)^2}{T+1}.$$
The more precise bound retains the negative mass discrepancy
$-(M_T-Tb_T)^2/(T+1)$. The complete infinite source is present throughout;
the finite source completion has a two-sided error, not a monotone relation
to the actual energy. This gives a controlled dual-domain transfer, not an
inner-cutoff subpower upper bound for $F_{X,M}$.

Lean: `CompletedArithmeticForms/EulerTerminalCost.lean`,
`fullErrorEnergy_finiteSource_error_le`,
`fullErrorEnergy_freeTerminal_schur_bound_with_mass`, and
`fullErrorEnergy_finiteSource_error_le_of_horizon`.
