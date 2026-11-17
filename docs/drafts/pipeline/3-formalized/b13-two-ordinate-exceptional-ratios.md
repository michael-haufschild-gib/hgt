# Exceptional frequency ratios for two top ordinates

- **Stage:** 3-formalized
- **Result:** Fix depth δ > 0, first ordinate r > 0 and two positive masses. For ordinates r and ru with u > 0 and u ≠ 1, the ratios for which no aperture has positive CCM balance are rational and meet every compact subset of (0,∞) in a finite set.

At a reference ratio u ≠ 1, exclusion of opposite eigenvalue pairs supplies a phase with nonzero balance. A half-turn changes its sign. Choose a level strictly between the two Rayleigh extrema at a positive phase. The maximizing vector stays above the level under small perturbations of both nodes and phases. The reflected form stays below it uniformly on the compact reference unit ellipsoid. Homogeneity extends this comparison to every nonzero vector.

Choose integers q > 0 and k by Dirichlet approximation so that |2π(qu − k)| is smaller than the resulting phase window. The same bound holds at nearby ratios v. Fix the first phase exactly and advance it by 2πq per step. Modulo 2π, the second phase advances by 2π(qv − k). For v ≠ k/q, integer steps reach the window. Thus each neighborhood so obtained contains at most one exceptional ratio, k/q. Near u = 1, the concentration theorem gives a common positive aperture. A finite subcover proves the compact-set claim.

For an actual top layer outside the finite exception set, every restricted Weil ground state is reflection-odd at arbitrarily large apertures. Whether any exceptional ratio exists remains open.

[TwoOrdinateParityHasLocallyFiniteExceptionalRatios.lean](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoOrdinateParityHasLocallyFiniteExceptionalRatios.lean) proves `eventually_positive_parity_at_nodes`, `rational_of_mem_exceptionalParityRatios`, `finite_exceptionalParityRatios_on_compact` and `two_ordinate_ground_odd_outside_finite_set`. All four axiom audits give `propext`, `Classical.choice` and `Quot.sound`.
