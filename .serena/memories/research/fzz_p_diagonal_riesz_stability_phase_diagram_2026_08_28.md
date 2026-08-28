# FZZ-P diagonal Riesz stability phase diagram (HC34, 2026-08-28)

Formalized and wired `FZZCigarParityDiagonalRieszStabilityPhaseDiagram.lean`.

For every positive scale, the literal diagonal Riesz perturbation has an explicit completed-square discriminant. Actual spectral reality is equivalent to nonnegative discriminant and to lying outside one bounded source-normalized coupling window. The window has an explicit positive-imaginary eigenvalue, nonzero eigenvector, exact eigenpair equation, and neutral Krein self-pairing. Its complement consists of two disjoint unbounded stable rays.

Consequence: the previously known source-gap stable coupling is highly nonunique. Local diagonal stability cannot orient parity-Mellin divisor modes. With the existing all-coupling chiral instability theorem, both canonical single-reporter linear interaction directions are terminal as standalone FZZ-P selectors.

Verification: direct Lean passed; targeted build passed (9,761 jobs); eight endpoints use only `propext`, `Classical.choice`, `Quot.sound`; lint has no HC34 finding.

Novelty boundary: generic two-by-two discriminant algebra is elementary. Corpus and primary-source searches found no source-specific Fermi parity-delay Riesz phase diagram or neutral-window/two-ray classification.
