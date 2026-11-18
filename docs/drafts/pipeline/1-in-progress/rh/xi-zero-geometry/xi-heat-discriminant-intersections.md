# Discriminant intersections of the ξ heat cover

**Target.** [§2.8](../../../../../reports/review-1811/obstacles-summary.md#28-a-geometric-question-about-actual-collisions) asks for a local multiplicity, a boundary winding formula with height cuts, a two-fold test, and vanishing on an exhaustion of positive real times.

**Local calculation.** In the time coordinate τ = τ₀ + s², the Hermite sheets are zᵣ(s) = z₀ + s yᵣ(s), with yᵣ(0) = r. Each pairwise difference has order one in s. The squared Vandermonde of an m-sheet cluster therefore has order m(m−1) in s and m(m−1)/2 in τ. This counts distinct pairs even at higher collisions.

**Finite windows.** `projectedHeatDiscriminant_local` identifies the finite divisor equation with the product of actual sheet differences up to a nonvanishing analytic factor. A shared seam contributes its divisor once. In the double cover y² = (t−a)(t−b), either fold has winding one and a contour enclosing both has winding two. Each local turn exchanges the two sheets. [Lean](../../../../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheLocalDiscriminantOfAHeatCollision.lean)

**Boundary calculation.** For a spatial rectangle with zero-free edges, the moments μₖ = (2πi)⁻¹ ∮ zᵏ H′/H dz give the power sums of the enclosed zeros. The Hankel determinant det(μᵢ₊ⱼ) of size μ₀ is their squared Vandermonde. Around one cluster its winding gives the local multiplicity. Adjoining a sheet q multiplies the determinant by ∏ᵢ(zᵢ−q)². On a regular shared edge the correction is the integral of d log(Dₗ/Dᵣ), oriented by the left rectangle. [Lean](../../../../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/Analysis/TheBoundaryMomentsOfAHeatWindow.lean)

**Exhaustion.** Compact boxes exhaust all positive real times and all places with collision-free faces. Each time interval admits a complex thickening with exactly the same collisions. The winding of the projected divisor on its time boundary is the sum of their local multiplicities.

**Arithmetic question.** Every multiple zero contributes positively. Vanishing in every box is equivalent to RH by `exists_real_heat_boundary_windings`. Whether the actual θ coefficients force this vanishing remains open.
