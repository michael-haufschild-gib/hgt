# Critical-line cusp of the ground state

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)
- **Lean:** [Weighted increment](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheConfinementEnergyOfAGroundStateIncrement.lean#L98) · [Critical-line cusp](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheCriticalLineCuspOfTheGroundState.lean#L112) · [Divergent first moment](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheCriticalLineCuspOfTheGroundState.lean#L137)

Let $F$ be a threshold ground state, $a$ its confinement coefficient and $M=\int F(u)^2e^{-8u}\,du$. For $G_h(u)=F(u)-F(u+h)$,
$$
\int G_h(u)^2e^{-8u}\,du=o(h).
$$
If the off-line divisor is finite, the critical-line samples, counted with multiplicity, satisfy
$$
\lim_{h\downarrow0}\frac1h\sum_\gamma |LF(i\gamma)|^2(1-\cos h\gamma)=4aM>0.
$$

The first absolute ordinate moment $\sum_\gamma |\gamma|\,|LF(i\gamma)|^2$ diverges.

**Proof.** Write $D(h)=\int G_h^2$, $L_h=\log(1/h)$, $s=hL_h$, and $Q=8aM$. The [ground-state modulus](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/TheModulusOfContinuityOfTheStateIsCarriedByTheWall.lean#L928) gives $L_hD(h)/h\to Q$. At frequencies $|r|\le1/s$, the quadratic cosine bounds give $1-\cos(hr)\le 2(h/s)^2(1-\cos(sr))$. Above $1/s$ the Gamma multiplier exceeds $L_s-C$, and everywhere it exceeds $-C$. Plancherel therefore gives
$$
L_sD(h)\le\operatorname{archForm}(G_h)+CD(h)+2(h/s)^2L_sD(s).
$$
Here $L_s/L_h\to1$, $D(h)/h\to0$, and the last term divided by $h$ tends to zero since $h/s\to0$. Thus the archimedean energy has lower slope at least $Q$. The full energy is $a(e^{8h}-1)M$. [Coercivity](../../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningHalfLineTranslationEnergy.lean#L19) retains both the archimedean energy and half of the weighted square at a cost $O(D(h))$. This proves the first assertion for every threshold ground state.

Apply the [diagonal zero formula](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheOnLineResolventOfAFiniteLayer.lean#L335) to $G_h$. Each on-line copy contributes $2(1-\cos h\gamma)|LF(i\gamma)|^2$. Each off-line copy contributes $LF(z)LF(-z)(1-e^{-hz})(1-e^{hz})=O_z(h^2)$. Finiteness makes their total $o(h)$. The bare energy of $G_h$ has slope $Q$, since subtracting its confinement term from its full energy preserves the slope. Dividing by two gives the cusp. If the first absolute moment were finite, the bound $1-\cos(h\gamma)\le h|\gamma|$ would allow termwise differentiation at zero. Every term has derivative zero, contradicting $4aM>0$.
