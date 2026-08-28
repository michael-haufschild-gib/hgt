# FZZ-P full linear Riesz stability cone (HC35, 2026-08-28)

Formalized and wired `FZZCigarParityFullLinearRieszStabilityCone.lean`.

For the simultaneous literal diagonal/chiral source-Riesz perturbation, mixed trace stays real and unchanged by chiral coupling; determinant gains exactly `eta^2/E`; characteristic discriminant is `Delta_diag - 4 eta^2/E`. Actual spectral reality is iff that discriminant is nonnegative, equivalently outside an explicit hyperbolic completed-square cone.

Negative cone carries an explicit positive-imaginary eigenvalue, nonzero eigenvector, exact eigenpair, and neutral Krein self-pairing. For every chiral coupling there are two distinct stable diagonal branches; every coupling strictly between them is unstable.

Consequence: full local linear span of both canonical reporter Riesz directions is nonrigid and terminal as an FZZ-P selector. Next viable dynamics must be nonlinear, nonlocal/infinite, singular, or add an independent source channel with parity-Mellin landing.

Verification: direct Lean passed; targeted build passed (9,762 jobs); eleven endpoints use only `propext`, `Classical.choice`, `Quot.sound`; lint has no HC35 finding.

Novelty boundary: generic two-by-two algebra is standard; source-specific mixed Fermi/Krein/Riesz cone was absent from corpus and not found in primary literature search.
