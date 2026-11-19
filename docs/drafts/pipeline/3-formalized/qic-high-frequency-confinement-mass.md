# High-frequency confinement mass

- **Stage:** 3-formalized
- **Lean:** [`IsConfinedNullVector.localized_high_frequency_mass`](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheHighFrequencyMassOfAFiniteLayer.lean#L200)
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

Let $F$ be a confined null state at a positive ratio with finitely many off-line ζ zeros, $a$ its confinement coefficient, $M=\int F(u)^2e^{-8u}\,du$, and $m_\gamma=|LF(i\gamma)|^2$, counting multiplicities. For every fixed $0<\delta<1$,
$$
y^2\left(\frac a2|LF(-4+iy)|^2+
\sum_{|y-\gamma|<\delta y}\frac{4m_\gamma}{16+(y-\gamma)^2}\right)
\longrightarrow 4aM>0\qquad(y\to+\infty).
$$

**Proof.** Put $A_z=LF(z)LF(-z)$ on the off-line copies and $S=\sum_z A_z$. At zero translation the null equation gives $S=-aM-\sum_\gamma m_\gamma\in\mathbb R$. Reflection gives $\sum_z A_z z=0$. For $b=4-z$, the exact identity $y^2/(b+iy)=b-iy-b^2/(b+iy)$ now yields
$$-y^2\Re\sum_z A_z/(4+iy-z)\longrightarrow -4S.$$
The [boundary identity](qic-boundary-power-of-a-confined-state.md) identifies this expression with the full critical-line and Fourier power. Each fixed critical-line copy eventually lies outside the moving window, where $4y^2/(16+(y-\gamma)^2)\le4/\delta^2$. Its weight tends to four. Absolute summability of $m_\gamma$ permits dominated convergence, so the discarded contribution tends to $4\sum_\gamma m_\gamma$. Subtracting leaves $4aM$.
