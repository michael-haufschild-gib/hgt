# Dual phase certificates determine the full annihilator mass floor

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; uncounted
- **Obstacles:** B13, B112; sharp mass costs for arbitrary fixed finite ordinate families.
- **Statement:** For a nonempty finite family of real ordinates, arbitrary common real abscissa, and arbitrary real budget H, exact normalized positive two-prime annihilators have mass below H+epsilon for every epsilon>0 iff every real linear phase functional bounded above by one along the continuous phase line has value at the all-minus-one vector at most H. Under this dual condition every exact mass M>H is attained.
- **Novelty:** Parity classifies only the unit floor. A complete dual formula would determine the mass floor even when odd relations force a larger value, and certify that continuous phase relaxation loses no mass for exact arithmetic monomials.

## Proof gates

1. Coordinate phase functionals force H>=1 and exclude zero ordinates whenever the dual condition holds. Then produce one exact positive annihilator using the corpus's single-target factors.
2. Its positive zero combination, translated by arbitrary monomial phases, sends the phase convex hull into itself under a fixed negative contraction. Prove that zero lies in the relative interior without assuming central symmetry or a Haar-mean interface.
3. Every strict radial contraction of the closed phase convex hull must therefore be an exact convex combination of actual nonconstant monomial phases.
4. Prove the sharp dual formula by finite-dimensional convex separation. Distinguish an attained relaxed boundary from arbitrarily close exact polynomial mass; do not replace exact annihilation by approximate cancellation.

`smul_mem_of_negative_contraction` in `ArithmeticPositiveDuality/NegativeContractionConvexity.lean` and `exact_annihilator_mass_iff_phaseConvexHull` in `ArithmeticPositiveDuality/AnnihilatorPhaseMoments.lean` pass direct Lean audits with only the three standard axioms. The actual phase geometry and full dual formula have Lean drafts in `AnnihilatorPhaseGeometry.lean` and `AnnihilatorMassDuality.lean`; their kernel checks remain. No contribution is counted yet.
