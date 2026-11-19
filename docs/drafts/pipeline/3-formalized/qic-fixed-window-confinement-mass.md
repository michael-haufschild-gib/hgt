# Fixed-width capture of confinement mass

- **Stage:** 3-formalized
- **Lean:** [`exists_fixed_window_capturing_confinement_mass`](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/AFixedWindowCapturesTheConfinementMass.lean#L199)
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

There is an absolute integer $N\ge1$ such that every confined null state $F$ at a positive ratio with finitely many off-line ζ zeros satisfies, for every sufficiently large $y$,
$$y^2\left(\frac a2|LF(-4+iy)|^2+
\sum_{|y-\gamma|<N}|LF(i\gamma)|^2\frac4{16+(y-\gamma)^2}\right)\ge 2aM,$$
where $a$ is its confinement coefficient and $M=\int F(u)^2e^{-8u}\,du>0$. Only the starting ordinate depends on the state.

**Proof.** Put $P=aM$ and $m_\gamma=|LF(i\gamma)|^2$. The [relative-window limit](qic-high-frequency-confinement-mass.md) with half-width $x/2$ lies between $3P$ and $5P$ for all sufficiently large $x$. The weight is at least $1/5$ when $|x-\gamma|\le1$, hence $x^2\sum_{|x-\gamma|\le1}m_\gamma\le25P$.

Group copies in the relative window by $j=\lfloor|y-\gamma|\rfloor$. Their ordinates lie within one unit of $y+j$ or $y-j$. For each occupied shell both centers exceed $y/2$, so their combined mass multiplied by $y^2$ is at most $200P$. The Poisson weight in shell $j$ is at most $4/(1+j^2)$. Choose $N$ with $800\sum_{j\ge N}(1+j^2)^{-1}<1$. The discarded shells then cost at most $P$, leaving at least $2P$.
