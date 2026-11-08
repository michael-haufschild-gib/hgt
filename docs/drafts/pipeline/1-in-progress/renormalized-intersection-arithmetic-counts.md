# Renormalized intersection theory of arithmetic counts

- **ID:** RIAC
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [review 0811 §2.11](../../../reports/review-0811/obstacles-summary.md)
- **Statement:** Construct quadratic arithmetic counts and parameter-dependent completed invariants at the critical conductor weight.

## Target and existing foundations

Programme [README](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/README.md).
ESG supplies the actual cutoff complexes and persistence classification.
HHAC supplies the renormalized torsion operators for `δ>0`, arithmetic prime
blocks and the critical mixed-row obstruction. Existing RIT retains ownership
of its Hodge/scattering constructions.

## Open constructions

1. A surface surrogate with an integer quadratic Riemann–Roch count on Hecke
   correspondences, independent of `Q`, with independently proved sign control.
2. Critical `δ=0` torsion compensation, including the archimedean place.
3. A completed prime chain complex with proved `s`-dependent zero detection.
4. A natural relative pair and signed-index localization recovering `M(N)`.
5. A Farey cell realization with a modular action and controlled cutoff boundary.

First formalized branch: [prime-star compensation](../3-formalized/riac-prime-star-compensation.md):
exact minimal payment, unrestricted diagonal classification, explicit negative
probes, logarithmic-square obstruction and sharp power boundary.
Second formalized branch: [completed prime boundary](../3-formalized/riac-completed-prime-boundary.md).
The faithful dense weighted embedding admits a closed extension of the actual
augmentation exactly when `2 Re(s)+δ>1`, with unique bounded extension and
exact norm. At and below the boundary, explicit finite packets obstruct every
closed extension. The [higher-degree question](../0-backlog/riac-completed-prime-koszul.md)
is whether the standard completed complex remains contractible above that threshold.
The [logarithmic compensation boundary](../3-formalized/riac-logarithmic-star-compensation.md)
is also formalized: leaf growth `(log p)^α` admits finite payment exactly
for `α>2`, with minimal positive completion and explicit negative probes.
The [vertical unitary graph comparison](../3-formalized/riac-unitary-prime-chain-gauge.md)
is formalized in every exterior degree, preserving the prescribed conductor
norms and the actual finite boundary graph closures.
The [full logarithmic torsion candidate](riac-logarithmic-torsion-completion.md)
asks for the sharp extension from prime stars to every conductor interaction.
The [canonical cone-pair candidate](../0-backlog/riac-relative-cone-normalization.md)
separates an actual relative-homology construction from a mere Euler subtraction;
it does not yet supply localization on the core.
The [modular filtration candidate](../0-backlog/riac-modular-height-filtration.md)
replaces an invariant finite cusp set by a moving cutoff with explicit matrix
height distortion; the prime-face comparison remains missing.

## Necessary distinctions

`Σ_faces(−1)^card=M(N)+P_N` for the core. Ordinary topological Euler
characteristic is `1−M(N)−P_N`. Relative subtraction must respect this sign.
Integer-valued `χ` alone is not a nonnegative count. Positive raw torsion
forms alone do not make their renormalized limit positive.

## Calibration

Curves: Manin, Stepanov, Rosati; polynomial prime complexes over finite fields.
Countermodels: Golden, complex fake, shifted data and genus-two graph.
Retain full probe rank, both degrees plus primitive data, linear Betti mass,
isolated-prime fixed points and the square-root Euler lower law.

## Completion standard

Each claimed theorem needs a dependency-closed proof, direct Lean check and
transitive axiom audit. A failed mechanism needs its strongest positive
survivor. Full programme completion requires the five constructions and their
calibrations; the presently verified foundations do not discharge them.
