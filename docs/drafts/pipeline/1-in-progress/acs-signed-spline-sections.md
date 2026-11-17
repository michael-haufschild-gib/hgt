# Small sections on signed spline rays

**Open target.** For each integer spline ray and every ε > 0, exhibit a nonzero rational section after increasing the logarithmic radius by εm² for all sufficiently large m.

At resolution n, sample the signed spline f at log(j/n). For each prime power k = pʳ in the support window, impose the integral valuation

    floor((2/√k) Σⱼ fⱼ fⱼₖ / j).

Negative valuations permit denominators. Let d be the positive rational generator of the resulting lattice. The logarithmic radius A is twice the product of the two sampled pole degrees minus the degree-point jet pairing with its diagonal counterterm. The small sections have coordinates z ∈ ℤ satisfying |dz| ≤ exp A.

On a fixed window, rounding all finite places changes the signed degree by at most Σₖ Λ(k), independently of the mesh and the coefficients. Before rounding, the signed degree converges to the full Weil form by logarithmic quadrature, including both poles. A nonzero section exists exactly when log d ≤ A. This leaves the arithmetic comparison of the least nonzero section with the real radius.

[Degree-point lattice](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/DegreePointSectionLattice.lean) · [Small sections](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SmallSectionsOfARationalLattice.lean)
