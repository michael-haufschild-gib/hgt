# Squarefree-Möbius finite-Fisher hard-coarea/soft-damping universality law

Status: Stage 2 — dependency-closed paper proof; Lean formalization in progress  
Lean target: `GaloisForLFunctions.RHTower.SquarefreeMobiusFiniteFisherHardCoareaSoftDampingUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`FisherOneCornerCoareaTransform` proves two faces of a generic finite Fisher object: integrating
its hard one-corner cutoff density gives the signed height holonomy, and Laplace transforming each
oriented pair interval gives a semigroup divided difference.

`MobiusCriticalFisherLowerBoundaryBudget` proves that the same divided difference, when the height
is the physical squarefree-Möbius critical clock, is exactly the difference of its soft
exponential damping coefficients.

Existing Möbius soft/hard laws compare already-taken critical limits. No corpus theorem identifies,
at finite rank and finite Euler parameter, the global hard coarea energy and every soft damping
entry of the same Fisher pair-amplitude kernel.

## Statement

For every finite index family, natural clock labels, real Fisher weights and center, and
`sigma ≥ 1`, use the heights
`(sigma - 1) * log(label)` and the complexified Fisher pair kernel
`2 * p_i * p_j * (h_i + h_j - 2m)^2`. Then:

1. the integral over all positive hard cutoffs of the one-corner density equals the complete
   signed pairwise height holonomy;
2. for every ordered height pair and every nonzero damping parameter, the Laplace transform of
   that exact pair-amplitude interval equals the pair kernel times the difference of the two
   squarefree-Möbius damping coefficients divided by the damping parameter.

Thus global hard-cut geometry and entrywise soft arithmetic damping are two exact presentations
of one finite non-diagonal Fisher object before any critical limit or scalarization.

## Dependency-closed proof

The squarefree-Möbius clock is nonnegative for `sigma ≥ 1`: its two factors are nonnegative, with
the label-zero case handled by `log 0 = 0` and every nonzero natural label at least one. Apply
`integral_finiteFisherOneCornerCoareaDensity` to obtain the global hard identity. For each ordered
pair, apply
`squarefreeMobiusCriticalClock_orientedCutoffLaplaceCoefficient_eq_dampingDividedDifference`
with the complexified exact Fisher pair amplitude.

No limit, numerical experiment, RH premise, or probabilistic normalization is used.

## Novelty audit

Corpus audit: exact search found generic finite coarea/divided-difference laws and separate
critical Möbius soft/hard asymptotics, but no finite physical-clock theorem synchronizing global
hard energy with every entrywise soft damping coefficient.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

Exact source check passed:
`lake env lean GaloisForLFunctions/RHTower/SquarefreeMobiusFiniteFisherHardCoareaSoftDampingUniversalityLaw.lean`.

Source is wired into `GaloisForLFunctions.RHTower`; final axiom, lint, and umbrella build audit
remain pending.
