# Cosine cusp of the whole zero divisor

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)
- **Lean:** [Whole-divisor cusp](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheGroundStateCuspOnTheWholeZeroDivisor.lean#L68) · [Projection to the imaginary axis](../../../../formal/GaloisForLFunctions/HTGeometry/TheCosineLossInAVerticalStrip.lean#L84)

For every threshold ground state $F$, set $A_z=LF(z)LF(-z)$ for each centred ζ zero copy $z$. With $aM$ the confinement energy, the absolutely convergent signed cosine sum satisfies
$$
\lim_{h\downarrow0}\frac1h\sum_z A_z(1-\cos(h\Im z))=4aM.
$$

**Proof.** The unit tilt of $F$ belongs to the energy domain. The same holds for its inward difference $G_h=F-F(\cdot+h)$, since its unit tilt is the difference of the unit tilt and $e^h$ times its translate. The diagonal explicit formula for $G_h$ gives the sum of $A_z K(z,h)$, where $K(z,h)=(1-e^{hz})(1-e^{-hz})$. Its bare energy has slope $8aM$ by the [weighted increment estimate](qic-critical-line-cusp-of-the-ground-state.md).

For $z=\beta+i\gamma$ and $0<h\le1$, the two terms in $K(z,h)=2-e^{hz}-e^{-hz}$ differ from their imaginary-axis values by at most $2h$ each, since $|\beta|<1/2$. For each fixed $z$ both kernels have zero derivative at zero. Thus $(K(z,h)-K(i\gamma,h))/h\to0$ with a uniform bound of four. Absolute summability of the reflected products gives the same limit after summation. Now $K(i\gamma,h)=2(1-\cos(h\gamma))$.
