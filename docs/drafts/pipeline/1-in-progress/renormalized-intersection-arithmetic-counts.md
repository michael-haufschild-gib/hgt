# Renormalized intersection theory of arithmetic counts

- **ID:** RIAC
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [review 0811](../../../reports/review-0811/obstacles-summary.md)
- **Statement:** Prove square-root-scale signed cancellation of the actual local indices, using independent arithmetic counts, product-formula heights or completed invariants.

## Target and existing foundations

The governing quantity is `S(N)=Σ_p index_p(N)=1−M(N)`. The RH-scale
objective is `|S(N)|≪ε N^(1/2+ε)` for every `ε>0`. A strict `O(√N)`
estimate is a stronger question. Each auxiliary construction must identify
its mechanism for controlling this signed sum; quadratic scaling alone
is insufficient. No such cancellation estimate is proved.

Programme [README](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/README.md).
ESG supplies the actual cutoff complexes and persistence classification.
HHAC supplies the renormalized torsion operators for `δ>0`, arithmetic prime
blocks and the critical mixed-row obstruction. Existing RIT retains ownership
of its Hodge/scattering constructions.

## Open constructions

1. A [surface count](../0-backlog/riac-surface-riemann-roch-count.md) with
   integer quadratic Riemann–Roch scaling on Hecke correspondences, independent
   of `Q`, with independently proved sign control.
2. Critical `δ=0` torsion compensation, including the archimedean place.
3. A completed prime chain complex with proved `s`-dependent zero detection.
4. A canonical relative pair on the connected core with Euler number `M(N)`;
   signed localization of the full complex is constructed below.
5. A Farey cell realization with a modular action and controlled cutoff boundary.

First formalized branch: [prime-star compensation](../3-formalized/riac-prime-star-compensation.md):
exact minimal payment, unrestricted diagonal classification, explicit negative
probes, logarithmic-square obstruction and sharp power boundary.
Second formalized branch: [completed prime boundary](../3-formalized/riac-completed-prime-boundary.md).
The faithful dense weighted embedding admits a closed extension of the actual
augmentation exactly when `2 Re(s)+δ>1`, with unique bounded extension and
exact norm. At and below the boundary, explicit finite packets obstruct every
closed extension. The [graph-closure refinement](riac-prime-boundary-graph-closure.md)
asks whether the exact closed relation there is the whole product.
The [higher-degree question](../0-backlog/riac-completed-prime-koszul.md)
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

The [signed localization theorem](../3-formalized/riac-prime-vertex-signed-localization.md)
constructs an arithmetic self-map, actual local isolating blocks and exits,
and finite relative singular homology. Its local indices sum to `1−M(N)`;
the core sum is `1−M(N)−P_N`. Local definitions use only prime products.
The indices are unbounded below, allowing signed cancellation without a
quantitative bound. The [exit-bouquet classification](../3-formalized/riac-prime-exit-bouquet.md)
constructs the full arithmetic homotopy type of each exit, with sphere labels
in the exact multiplicative window determined by the least upper neighbour.

The [proper arithmetic intersection count](../3-formalized/riac-thickened-intersection-counts.md)
constructs actual finite rings `ℤ[X]/(P,Q)`, proves their resultant cardinality,
and gives quadratic integer prime-local multiplicities and logarithmic heights
under equal thickening. Distinct cyclotomic counts recover the established
torsion intersection. The [rational-radius construction](../3-formalized/riac-rational-abel-intersection-counts.md)
now realizes Abel energy by actual integral quotient counts. An explicit
residual exact sequence removes the coincident-root factor, prime by prime;
the diagonal count is the absolute discriminant. Normalized residual counts
converge to that diagonal height with the proved finite-radius error sign.
The critical sign and the comparison controlling the signed local-index
sum remain open.

The [finite-field orientation count](../3-formalized/riac-finite-field-orientation-counts.md)
constructs actual square-root fibres of residue-field trace discriminants.
Their signed fibre counts recover polynomial Möbius signs. The aggregate
count uses established polynomial cancellation. A separate
[independent Frobenius orbit count](../3-formalized/riac-independent-frobenius-orbit-counts.md)
now derives `q^n` from normal-basis bijections and actual transporter sets.
Its orientation-cover comparison and the integer comparison remain open.

## Necessary distinctions

`Σ_faces(−1)^card=M(N)+P_N` for the core. For `N≥4`, its ordinary
topological Euler characteristic is `1−M(N)−P_N`. Relative subtraction must respect this sign.
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
