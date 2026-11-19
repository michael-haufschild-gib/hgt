# Positive measure for mixed conductor blocks

Let $K_d(n)$ be the second difference of the complete residue block of logarithmic graph heights. A Frullani difference represents $\log(a+1)-\log a$ by $e^{-at}(1-e^{-t})/t$ on $t>0$. Pairing the offsets $z,-z$ produces the nonnegative factor $e^{zt}+e^{-zt}-2$. Half the sum of these reflected densities has mass $K_d(n)$. Moving the conductor by $k$ multiplies the density by $e^{-kt}$.

Writing $x=e^{-t}$, the full mixed curvature of any two signed endpoint sections $U,V$ is the integral of $UV$ against this measure. It extends to continuous sections with exact norm $K_d(n)$, attained by $1$. Squares have nonnegative intersection. For $n\ge1$ the bound is $2d^2\|UV\|_\infty/(n+1)^3$, independently of both supports.

Lean declarations include `blockDensity_mass`, `sectionIntersection_gluing`, `sectionIntersection_bound`, `sectionIntersection_one`, `mixed_block_curvature_bound` and `sectionIntersection_square_nonneg`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/ThePositiveMeasureOfAMixedConductorBlock.lean)
