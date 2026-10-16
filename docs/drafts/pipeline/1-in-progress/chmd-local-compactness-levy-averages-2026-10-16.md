# CHMD: local compactness from singular Levy averages

Status: IN PROGRESS. RH remains unproved.

## Starting evidence

The actual arithmetic and stationary generators have compact C2 operator
cores. The ordinary stationary form is the literal translation-difference
graph with kernel kappa(t). The arithmetic resolvent has an orthonormal Weyl
sequence at 1/2, so global compactness is false. The current Lean corpus also
proves confinement of approximate eigenvectors at every level above 1/2.

## Conjecture

Every compact spatial localization of the actual form embedding, hence of
the arithmetic resolvent, is compact. Combined with confinement this should
force spectral points above 1/2 to be genuine finite-multiplicity modes,
rather than additional escape spectrum.

## Proposed proof mechanism

For 0<delta<epsilon, normalize kappa(t) on [delta,epsilon] to probability
mass m_delta. The mass tends to infinity as delta tends to zero. Jensen gives
norm(u-average_delta u)^2 <= stationaryEnergy(u)/m_delta. Thus these averages
approximate the identity uniformly on bounded form sets. Each truncated
kernel is in L2; after spatial localization its integral kernel is in L2 of
the product space, hence its operator is compact. Taking the operator-norm
limit proves local compactness without requiring a Fourier-symbol bound.

Transfer through theta multiplication and bounded local inverses from the
previous operator-core theorem. Then use the actual far-field confinement
theorem to extract the spectral consequence. Do not claim full resolvent
compactness, or infer the critical signed-form sign from local compactness.

## Work plan

1. Audit corpus support for singular averages and compact integral operators.
2. Prove normalized truncated-average approximation on the actual form graph.
3. Prove compactness and transfer to the actual arithmetic resolvent.
4. Derive the strongest actual spectral consequence; verify all leaves,
   axioms, imports, lint, and owned scratch cleanup.

## Validation

Pending. Previous core capstone and local-domain hashes still match the
completed audit; all nine prior imports remain wired exactly once.
