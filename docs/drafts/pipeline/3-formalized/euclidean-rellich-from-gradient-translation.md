# Euclidean Rellich compactness from the gradient translation bound

- **ID:** euclidean-rellich-from-gradient-translation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** On a fixed compact Euclidean support, the complete `C¹` energy graph has compact mass projection. Every `C¹` family with common compact support and bounded mass and gradient norms is precompact in `L²`.

For an energy unit vector, `‖τ_t u−u‖₂≤‖t‖`. Choose a nonnegative
smooth probability kernel supported in the radius `ε/2` ball. Jensen and
Fubini bound its squared smoothing error by `(ε/2)²`. Actual convolution
with this fixed kernel is compact: its continuous kernel on compact input
and output supports is covered by the corpus compact-kernel theorem.
Finite nets for the smoothed unit ball give total boundedness of the original
mass image. Completeness gives compact closure. The compact operator then
maps every energy ball to a precompact mass family.

Lean: `MetaplecticMobiusDescent/Sobolev/EuclideanRellich.lean`,
`isCompactOperator_h1OnToL2` and `c1c_family_precompact`.
Source check and transitive `#print axioms` audits passed; only `propext`,
`Classical.choice`, and `Quot.sound`. No raised limits.

Provenance: Adam Benenson, rellich-kondrachov,
`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`; compact-family bridge also
follows OpenAI `CubicSieve/RadialWindows.lean`. This is an analytic input,
not a theta-residue or arithmetic-cancellation theorem.
