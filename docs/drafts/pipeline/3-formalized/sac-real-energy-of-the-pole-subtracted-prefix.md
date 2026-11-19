# The real Weil energy of the ordinary prime defect

The full lower prefix through $M$ meets the upper endpoint $M$ in logarithmic height $\log(M!)$ and opposite-degree product $M H_M$. The second difference of their defect, taken as product minus height, is $G(m)=1/(m+1)-\log((m+2)/(m+1))$.

Frullani’s formula gives moments of the density $1-\ell(x)$ with $\ell(x)=(1-x)/(-\log x)$. The estimates $x\le\ell(x)\le(1+x)/2$ compare this density pointwise with the genuine degree-one real Weil density $(1-x)/2$. Integrating against $x^nU(x)^2$ gives $D_1\le G\le2D_1$ in quadratic-form order. Integrating $2|UV|\le U^2+V^2$ gives $|G(U,V)|\le D_1(U,U)+D_1(V,V)$ for any two finite signed sections, uniformly in their support sizes.

Lean declarations include `prefix_curvature_entry`, `prefixDefectCurvature_moment`, `prefix_defect_between_weil_metrics` and `prefix_mixed_defect_le_weil_energies`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/ThePoleDefectOfFullIntegralPrefixes.lean)
