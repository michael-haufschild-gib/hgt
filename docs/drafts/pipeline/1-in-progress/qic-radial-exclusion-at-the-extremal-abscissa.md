# QIC radial exclusion at the extremal abscissa

- **Stage:** 1-in-progress
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

Write Θ for the extremal zero abscissa, F for the prime-error boundary trace, h for the trial quarter-period, and A = exp(Θh). The corpus proves (ψ(x)−x)/x^Θ − F(log x) → 0 for Θ > ½, including infinite and unattained extremal layers.

**Radial exclusion.** The normalized θ radius tracks the norm of (D(t),D(t+h)), where D(t) = AF(t+h)−F(t). At an unattained extremum F vanishes, so the normalized discrepancy tends to the strictly negative trial amplitude. Otherwise bounded discrepancy and almost periodicity force D(t)²+D(t+h)²=C² for every real t.

**Frequency constraint to prove.** Subtraction at adjacent starting points makes |D| periodic with period 2h. For every ε > 0 the translation orbit of D has an ε-almost period of the form 2nh with positive integer n. At this shift a sign reversal is possible only where |D| ≤ ε/2. Truncating toward zero by ε/2 therefore gives an exactly periodic uniform approximant. Each nonzero Bohr coefficient of D must have frequency commensurable with π/h. The multiplier A exp(iωh)−1 preserves every attained top ordinate.

**Single-pair conjecture without a finiteness assumption.** At any nonzero frequency difference d with exp(idh)=1, the Bohr coefficient of the squared radius is a sum over pairs (u+d,u). The step factors give |A exp(iuh)−1|². The imaginary parts of the reciprocal products all have the same strict sign, since the denominator is Θ²+u(u+d)+iΘd. Thus each phase class modulo 2π/h should contain at most one distinct ordinate. Each class for the shift 2h then contains at most two. On any interval where D is nonzero, D(t+2kh)/D(t) is constant in t for each integer k. Taking the discrete Bohr coefficient in k makes the trigonometric polynomials from each occupied phase class proportional on that interval. Distinct classes have disjoint frequencies, so at most one class can survive. Conjugation would then leave just one pair on the extremal line.

**Open.** Exclude the remaining commensurable top configurations, including an actual single quartet. The separate uniform confined-index cap also remains open.
