# Smooth plateaus make the separated complete Weil matrix positive

## Mathematical target

Construct one nonnegative smooth profile supported in [0,1] with positive square
mass and Robin energy plus squared charge strictly exceeding log(2*pi). Deduce
that, for every fixed 0<c<1, the entire literal complete-Weil matrix is positive
definite for all sufficiently large horizons. This uses the existing exact
bounded spectral count theorem, not only a trial-vector calculation.

## Mechanism

For the existing smooth plateau phi_eta let M=integral(phi_eta^2), I=integral(phi_eta).
Its autocorrelation at 0<=y<=1 is at most 1-y, while M,I>=1-2eta and M<=1.
For 0<delta<=1, integration on [delta,1] gives
 B_eta >= (1-delta)(1-2eta/delta).
The complementary interval has nonnegative Robin density. Therefore
 B_eta/M + I^2/M >= (1-delta)(1-2eta/delta)+(1-2eta)^2,
which can be made arbitrarily close to2 from below. Since log(2*pi)<2, choose one
plateau with positive margin. Cauchy-Schwarz gives q=I^2/M<=1 and -log c>=1-c,
so its conductor-one energy is at least the same positive margin for all0<c<1.
All other conductor energies are larger. The exact bounded spectral count at
half that margin is zero eventually, hence all actual eigenvalues exceed a
positive threshold.

## Novelty and boundary

Existing plateau Robin estimates are upper bounds for Markov-form failure.
The new lower Robin estimate preserves the completed pole term, then uses the
already proved complete spectral exhaustion. This is full matrix positivity
inside strict separation. It does not establish endpoint c=1, overlapping
atoms, uniform horizon bounds as c approaches1, or Weil positivity on all tests.

## Status

Analytic proof under development. No theorem claimed before Lean formalization.
