# QIC radial exclusion at the extremal abscissa

- **Stage:** 1-in-progress
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

At Θ>½ a trial radial discrepancy of order O(√x log²x) forces exactly one conjugate pair on Re s=Θ. All multi-pair and unattained extrema are excluded. [Formalized theorem](../3-formalized/qic-the-extremal-trace-of-the-ordinary-prime-radius.md)

**Descent below the extremal pair.** Write h for the trial step, D for the limiting signed increment, U(t)=exp(−Θt) Δₕ(θ(exp t)−exp t), and w(t)=exp((½−Θ)t)(1+t)². The bound |U²−D²|=O(w) holds uniformly at all sufficiently large t, including the nodes of D. [Lean proof](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheTwoIntervalRadiusControlsEachSquaredPrimeIncrement.lean).

The single extremal pair makes D a sinusoid. Averaging θ over [x,x+1] changes it by at most log(x+1) and gives a continuous increment. On each lobe the smoothed increment has the sign of D at its crest. A sign change between a point and its nearest crest therefore requires D²=O(w) at the point. This gives (U−D)²=O(w) and, by polarization, |D(U−D)|=O(w).

The squared signed bound alone gives a first gap. For σ>(Θ+½)/2, telescoping the raw increments from [0,h] gives an O(exp(σt)) remainder after removing the extremal wave. The finite-wave Landau converse then places every other zero at Re s≤(Θ+½)/2.

For ½<a<1, interpolating the square-root and reciprocal bounds gives |U−D|≪wᵃ |D|⁻⁽²ᵃ⁻¹⁾ away from the nodes. The negative power of the sine is integrable on each period. Thus the raw signed increment error should be integrable against exp(−σt) for every σ>½. For the top-copy set S put E(t)=ψ(exp t)−exp t+Re W_S(exp t) and J(t)=exp(t)∫ₜ^∞ E(v)exp(−v)dv. The tail operator commutes with translation, so |ΔₕJ(t)|≤exp(σt)∫ₜ^∞ |ΔₕE(v)|exp(−σv)dv for ½<σ<1. The subtracted-lag identity gives exp(t/2)Φ_S(t)=−J(t)+O(1). Telescoping its increments yields Φ_S(t)=O(exp((σ−½)t)). The proved lag converse would then put every other right zero to the left of every σ>½. [Negative-power integral](../../../../formal/GaloisForLFunctions/HTGeometry/NegPowerCircleAverage.lean) · [Subtracted lag identity and converse](../../../../formal/GaloisForLFunctions/RHTower/FiniteOffLineConverse.lean#L194)

**Open.** Verify the signed estimate and weighted-integral descent. Even a complete descent leaves two arithmetic tasks: exclude a genuine single off-line quartet, and bound every confined index by two.
