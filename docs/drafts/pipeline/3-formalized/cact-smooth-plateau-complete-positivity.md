# Smooth plateaus make the separated complete Weil matrix positive

## Formalized theorem

For every b<2-log(2*pi) and epsilon>0, there is a smooth nonnegative unit-interval
plateau phi_eta with integral(phi_eta^2)>1-epsilon such that every actual
normalized complete-Weil eigenvalue is eventually>=b at each fixed0<c<1.
The same profile works for allc; the eventual horizon may depend onc.
The entire matrix is eventually positive definite, and the full quadratic
form has lower bound b times the squared Euclidean norm.

## Mechanism

Write M_eta=integral(phi_eta^2), I_eta=integral(phi_eta), B_eta=bumpRobin(phi_eta,1).
Autocorrelation is at most the overlap length1-y. Truncating the nonnegative
Robin integral to[delta,1] gives B_eta>=(1-delta)(1-2eta/delta). Together with
existing upper estimates, this proves M_eta,I_eta,B_eta->1 and completed shape
(B_eta+I_eta^2)/M_eta->2. The completed conductor-one energy exceeds its
endpoint margin for everyc<1 because charge q<=1 and -logc>=1-c.
All other conductor energies are higher. The existing exhaustive bounded
spectral-count law then excludes every actual eigenvalue below the margin.

## Novelty and boundary

Existing plateau estimates supplied upper Robin bounds for Markov failure.
The new lower estimate and exact indicator limits retain the completed pole
charge. Full spectral exhaustion supplies whole-matrix positivity. Near-unit
mass rules out obtaining this result merely by shrinking effective support.
No claim atc=1, uniform horizon as c approaches1, genuine overlapping-family
positivity, global profile optimality, or RH.

## Lean declarations and validation

- SmoothPlateausRecoverTheCompletedRobinMargin.lean:
  bumpRobin_plateau_ge; exists_plateau_completed_robin_margin.
- ThePlateauShapeAndChargeHaveTheirIndicatorLimits.lean:
  tendsto_plateau_completed_shape; tendsto_plateau_completed_margin.
- SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean:
  exists_near_unit_plateau_eventually_completeWeil_eigenvalues_ge;
  exists_plateau_eventually_completeWeilEnergy_ge;
  exists_plateau_eventually_completeWeilMatrix_posDef.

All three passed final individual `lake --old env lean` checks. Capstone
axiom outputs: propext, Classical.choice, Quot.sound. Wired into the programme
umbrella; no umbrella or full build. Only dependency oleans were produced.
