# Canonical boundary for finite-energy Euler–FE defects

- **ID:** euler-fe-finite-energy-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Euler–FE transport theory; defect calculus.
- **Statement:** The actual Hamburger boundary on `L¹ ∩ L²` extends uniquely to a
  complex-linear continuous map `B : L²(ℝ) → L²(ℝ)` satisfying
  `‖Bg‖² = π⁻¹‖g‖²` for every `g ∈ L²`.

## Proof mechanism

Integrable elements form a linear subspace of `L²`, dense because it contains all
Schwartz functions. The actual boundary integral respects almost-everywhere equality,
addition and scalar multiplication. Its proven energy identity makes it bounded in
the `L²` norm. Extend this map by density, preserving the exact norm identity and its
agreement with every actual boundary from `L¹ ∩ L²`.

## Remaining analytic obligation

The completion must subsequently be identified with the weak imaginary boundary of
the interior Laplace transform for arbitrary `L²` data. The weak tent identity and
unit-gap vanishing are still needed before extending Beurling rigidity. This construction
alone supplies neither that classification nor height replication.

`../1-in-progress/euler-fe-hardy-laplace-transport.md` specifies the candidate Gamma–Mellin source
for the missing Laplace identification and vertical boundary convergence.

## Lean proof

Module: `formal/GaloisForLFunctions/EulerFETransportTheory/FiniteEnergyDefectsHaveCanonicalBoundaries.lean`.

- `defectBoundaryL2_agrees`: almost-everywhere agreement for every `L¹ ∩ L²` source.
- `norm_sq_defectBoundaryL2`: exact energy identity for every `L²` source.
- `normalizedDefectBoundaryL2`: the isometric embedding `√π B`.
- `defectBoundaryL2_unique`: uniqueness among continuous complex-linear extensions.

Direct `lake --old env lean` audit passed. All four depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The programme umbrella imports the module.
