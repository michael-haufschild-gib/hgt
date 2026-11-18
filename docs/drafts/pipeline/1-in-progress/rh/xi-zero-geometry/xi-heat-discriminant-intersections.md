# Discriminant intersections of the ξ heat cover

**Target.** [§2.8](../../../../../reports/review-1811/obstacles-summary.md#28-a-geometric-question-about-actual-collisions) asks for a local multiplicity, a boundary winding formula with height cuts, a two-fold test, and vanishing on an exhaustion of positive real times.

**Local calculation.** In the time coordinate τ = τ₀ + s², the Hermite sheets are zᵣ(s) = z₀ + s yᵣ(s), with yᵣ(0) = r. Each pairwise difference has order one in s. The squared Vandermonde of an m-sheet cluster therefore has order m(m−1) in s and m(m−1)/2 in τ. This counts distinct pairs even at higher collisions.

**Finite windows.** `projectedHeatDiscriminant_local` identifies the finite divisor equation with the product of actual sheet differences up to a nonvanishing analytic factor. A shared seam contributes its divisor once. In the double cover y² = (t−a)(t−b), either fold has winding one and a contour enclosing both has winding two. Each local turn exchanges the two sheets. [Lean](../../../../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheLocalDiscriminantOfAHeatCollision.lean)

**Arithmetic question.** Every multiple zero has positive local multiplicity. Vanishing of the resulting count on an exhaustion would exclude every positive real branch time, hence prove RH by `riemannHypothesis_iff_forall_pos_not_mem_branchTimes`. The θ-kernel step is open.
