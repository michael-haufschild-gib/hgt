# QIC radial exclusion at the extremal abscissa

- **Stage:** 1-in-progress
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

Write Θ for the extremal zero abscissa, F for the prime-error boundary trace, h for the trial quarter-period, and A = exp(Θh). The corpus proves (ψ(x)−x)/x^Θ − F(log x) → 0 for Θ > ½, including infinite and unattained extremal layers.

**Radial exclusion.** The normalized θ radius tracks the norm of (D(t),D(t+h)), where D(t) = AF(t+h)−F(t). At an unattained extremum F vanishes, so the normalized discrepancy tends to the strictly negative trial amplitude. Otherwise bounded discrepancy and almost periodicity force D(t)²+D(t+h)²=C² for every real t.

**Frequency constraint.** Every bounded trial has an attained extremal line with all ordinates in |γ|ℚ. [Lean proof](../3-formalized/qic-the-extremal-trace-of-the-ordinary-prime-radius.md).

**Single-pair conjecture without a finiteness assumption.** [Equal quarter-step phases determine one ordinate, and each doubled-step phase has finite support](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/DistinctExtremalOrdinatesHaveDistinctQuarterStepPhases.lean). Choose an interval where |D| > δ and a lattice almost period 2Nh with uniform error < 2δ. Then D(t+2Nh)−D(t) vanishes on that interval and all its 2h-translates, since |D| is 2h-periodic. Discrete Cesàro averaging over the translates annihilates each phase component on the interval. Each component is a finite trigonometric polynomial, hence vanishes globally. All occupied 2h-phases must therefore be Nth roots of unity, making the top layer finite. The finite polynomial identity (D(t+2h)−D(t))(D(t+2h)+D(t)) = 0 then forces one global sign. Conjugation would then leave just one pair on the extremal line.

**Descent below one extremal pair (conjectural).** Suppose D is a single sinusoid. Write U(t) = exp(−Θt) ΔₕE(t) and ε(t) = exp((½−Θ)t)(1+t)². Subtract the squared radii at t and t+h. Summation along t+2nh gives U²−D² = O(ε), since U−D → 0 and D² is 2h-periodic. Linear interpolation of θ between consecutive integers costs O(t exp(−Θt)) after normalization. On each lobe of the sinusoid, the interpolated U has the sign of D at its midpoint and cannot change sign where |D| exceeds a sufficiently large multiple of √ε. Thus (U−D)² = O(ε), and 2D(U−D) = O(ε).

For V(t) = exp(Θt)(U(t)−D(t)), the Laplace transform of D·V is therefore holomorphic on Re s > ½. If D(t) = c exp(iωt) + conj(c) exp(−iωt), a pole of the Laplace transform of V forces poles every 2iω along its line, with residues of equal modulus. For secondary ζ zeros ρ those residues are −mult(ρ)(exp(hρ)−1)/ρ. Their absolute values are summable on each such line by the right-substrip reciprocal bound. This would exclude every secondary right zero, even without a gap below Θ. The argument would identify the actual single-quartet case; excluding that case still requires arithmetic input.

**Open.** Exclude the remaining commensurable top configurations, including an actual single quartet. The separate uniform confined-index cap also remains open.
