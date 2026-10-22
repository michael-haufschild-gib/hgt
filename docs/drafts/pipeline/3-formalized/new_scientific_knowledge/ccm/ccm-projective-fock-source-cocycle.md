# Projective Fock cocycle for the intact matched CCM source

Status: formalized unconditionally in
`GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveFockCocycle`.

## Frankenstein weld

This construction combines four corpus mechanisms that previously lived separately:

- trace-free Bloch splitting from matched CCM phase disks;
- exponential-inner-product positivity from `HilbertMetric.GaussianJetPositivity`;
- multiplicative reflected-ratio transport, as in corpus Fock/Gamma gauge laws;
- log-ratio affinity/holonomy conversion from `HTGeometry.ThermodynamicCycleAffinity`.

For one arithmetic atom define

`a_n(ξ) = (w_n, C_n(ξ)-w_n, S_n(ξ)) ∈ ℝ³`

and the rotating phase probe

`q_n(ξ) = (cos θ_n, cos θ_n, sin θ_n)`.

Then

`⟪a_n,q_n⟫ = C_n cos θ_n + S_n sin θ_n`,

exactly the real oriented matched CCM source symbol.  The apparent critical-weight term cancels
between the first two coordinates; unlike Schur completion, it creates no additive positive trace.

Put every atom and both probes `±q_n` into one exponential-inner-product kernel.  It is an
infinite `IsPSDKernel`.  Its reflected entry ratio satisfies

`K(a_n,+q_n) / K(a_n,-q_n) = exp(2 source_n)`.

Therefore half its real logarithm is exactly `source_n`.  Multiplying ratios over a finite packet
gives a positive projective holonomy `H_F` with

`log H_F = 2 Re(source_F)`.

Every finite actual matched prime-polar block is consequently the spectral integral of
`(1/2) log H_F`, a single multiplicative positive-kernel cocycle.  External anchor coefficients,
critical-weight correction, cofinal matrix choice, and target-fitted off-diagonals all disappear.

## Principal theorems

- `ccmActualHeadMatchedPhaseProjectiveFockKernel_isPSDKernel`
- `ccmActualHeadMatchedPhaseProjectiveAtom_inner_rotatingProbe`
- `ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp`
- `half_log_ccmActualHeadMatchedPhaseProjectiveFockRatio`
- `log_ccmActualHeadMatchedPhaseProjectiveFockHolonomy`
- `ccmActualHeadMatchedPrimePolarFiniteBlock_eq_projectiveFockHolonomy`

## New frontier

Source is now a projective affinity, not a signed linear reporter.  Kernel positivity alone still
does not force sign of its log-ratio.  Next useful question is whether the full CCM involution makes
these local affinities a closed-walk holonomy.  Corpus thermodynamic exactness says vanishing of all
closed affinities is equivalent to a global positive potential; a nonzero cycle instead exposes a
strict positive production/Fisher cost.  Either branch may yield a new rigidity dichotomy once the
arithmetic reflection graph is identified without an RH premise.

No RH claim is made by this card.
