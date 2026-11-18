# The extremal trace of the ordinary-prime radius

- **Stage:** 3-formalized
- **Source:** [TheBoundaryTraceOfTheTwoIntervalPrimeRadius.lean](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheBoundaryTraceOfTheTwoIntervalPrimeRadius.lean)

Let Θ > ½ be the extremal zero abscissa, F the prime-error boundary trace, h the trial quarter-period and A = exp(Θh). Put D(t) = AF(t+h) − F(t). After division by exp(Θt), the ordinary-prime radius differs from the norm of (D(t),D(t+h)) by o(1). If no zero attains Θ, the normalized discrepancy tends to −C, where C > 0 is the trial radius coefficient. Thus every nonzero trial frequency and every positive trial multiplicity satisfy radial exclusion at that abscissa.

**Proof.** The explicit-formula boundary approximation for ψ transfers to θ because ψ(x)−θ(x) = O(√x). Normalizing the first increment gives D(t)+o(1). The factor 1/A in the second gives D(t+h)+o(1). The reverse triangle inequality transfers these limits to the radius. A square-root discrepancy divided by exp(Θt) tends to zero. Almost periodicity of F passes to the norm of its two increments, so a limiting constant radius is exact at every real t. For an empty extremal line F vanishes identically.

**Lean.** `tendsto_normalizedThetaRadius_sub_boundary`, `boundaryStep_circle_of_bounded_thetaRadial`, `tendsto_thetaRadial_div_exp_of_unattained`, `thetaRadial_unbounded_of_unattained`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
