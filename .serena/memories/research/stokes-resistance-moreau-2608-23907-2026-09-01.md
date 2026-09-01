# Moreau Stokes resistance application sweep (2026-09-01)

Paper: arXiv:2608.23907v1, Moreau, *The Stokes resistance of an arbitrary particle: a classification of hydrodynamic symmetries*.

Formalized under `formal/GaloisForLFunctions/HTGeometry/StokesResistance/` with umbrella `HTGeometry/StokesResistance.lean`, imported by `HTGeometry.lean`.

Reusable mechanisms:
- `FiniteGroupCharacter`: Reynolds projector, fixed-space/character average, stacked invariance defect, equivariant-map character product average.
- `SymmetricTensorCharacter` and `SymmetricSquareMatrix`: arbitrary-dimension and 2D symmetric-square character formula.
- `MirrorSymmetricResponse`: exact mirror-fixed reciprocal-response projector/rank formula `(d^2 + 2d + trace(A)^2)/4`.
- `JetDimension`, `AxialWeightCount`, `SphericalWeightCount`, `AxialAliasing`: shifted jet counts, axial cubic reduction, SO/O linear counts, finite cyclic anti-alias threshold.
- `MobilityAndElimination`: inverse stabilizer equivalence and exact Schur force/torque elimination.

Concrete applications:
- Binary octahedral fundamental carrier: invariants zero, Reynolds/character zero, defect injective.
- Projective octahedral conjugation carrier: actual quotient order 24, fixed subspace exactly scalar line, character average 1.
- Doubled Clifford response commutant: exactly span of identity and swap, finrank 2.
- Abstract Q8 Artin carrier: no invariant vector; self-equivariant response finrank 1 and character self-average 1.
- Serre literal Q8 Galois representation: same zero fixed-vector and one-dimensional self-response conclusions.
- Constitutive C2 trivial/sign carriers: cross intertwiner dimension 0; mixed even/odd symmetric response dimension 2.
- Qubit swap mirror: 7 of 10 symmetric responses survive.
- Continuous involution/representation families: mirror-response finrank cannot jump.

Verification:
- Every production leaf checked with `lake env lean`.
- Every leaf targeted-built individually; umbrella deliberately not built.
- `/tmp/hgt_stokes_axioms.lean` checked representative endpoints: only standard `propext`, `Classical.choice`, `Quot.sound`, no added axioms.
- Targeted grep found no sorry/admit/axiom/opaque/unsafe, no decide/native evaluation, no trailing whitespace.
- Global `scripts/formal_tools.py lint` was red only because many unrelated concurrently added HTGeometry/RHTower modules were unreachable from their umbrellas; no Stokes module appeared in failures.
- No stale Lean process remained.

No commit/push performed.