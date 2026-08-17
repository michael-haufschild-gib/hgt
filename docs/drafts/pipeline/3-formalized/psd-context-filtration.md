# Positive-semidefinite context filtration

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [BRIDGE] [LEAN PROVED]`

Lean: `formal/GaloisForLFunctions/HTGeometry/PSDContextFiltration.lean`, declarations
`psdContextFiltration`, `psdContextFiltration_mono`, and
`noiseShiftedBalancedContextKernel_posSemidef_iff`. Closed without added axioms.

Source: Proposition 8.1 of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163),
reformulated without eigenvalue computations.

## Statement

For a finite Hermitian kernel `K` and noise tolerance `epsilon`, declare a nonempty finite context
`S` admissible when

`K_S + epsilon I` is positive semidefinite.

These admissible contexts form a pre-abstract simplicial complex. If
`0 <= epsilon <= eta`, every `epsilon`-admissible context is `eta`-admissible, so the complexes
form a monotone filtration.

## Proof

If `T` is a nonempty subset of an admissible `S`, then

`K_T + epsilon I_T`

is the principal submatrix of `K_S + epsilon I_S` selected by the inclusion `T -> S`.
Positive semidefiniteness is preserved by submatrices, proving downward closure.

For monotonicity in tolerance,

`K_S + eta I = (K_S + epsilon I) + (eta-epsilon)I`.

The first summand is positive semidefinite by admissibility and the second is positive semidefinite
because `eta-epsilon >= 0`. Their sum is positive semidefinite.

For the balanced order-`r+3` kernel, every proper face is already admissible at zero tolerance,
while the full face becomes admissible exactly when `epsilon` reaches the balanced spectral margin
`1/(2r+3)`. This follows from its orthogonal constant/transverse decomposition.
