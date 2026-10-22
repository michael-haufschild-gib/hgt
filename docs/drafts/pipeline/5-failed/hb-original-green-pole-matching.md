# Original Green poles versus the unit-source clock

Target: full temporal/metric/QNM matching. The complete canonical metric action's finite value and the original Green response's QNM pole are different observables. The previous canonical-value obstruction does not establish pole survival.

Closed matching candidate: extracting the genuine original Green-response pole, instead of the regular canonical-action value, restores matching with the unchanged complementary unit-source clock.

Lean-proved positive survivor: genuine fundamental poles survive at every interior detector and every nonzero original amplitude for a relative density-one subset of actual simple critical Xi sources. This excludes the candidate because the unchanged unit-source clock vanishes on every critical copy.

Corpus basis: `PhysicalFundamentalMoment` gives the exact pole criterion: angular coefficient, complete radial moment, and fixed onset numerator must all be nonzero. `FundamentalSourceSurvival` gives a uniform high-height nonzero bound for the original true/true radial moment. `FullCanonicalMatchingNoGo` gives only linearly many angular/canonical exceptions. The fixed onset is a compact pulse transform; its zeros must be counted with the original duration retained.

Proof mechanism: the finite-exponential-type bound for the actual onset factor counts its exceptional copies together with the established canonical exceptions and the bounded-height set. The full physical Laurent theorem transfers surviving source data to actual poles. No numerical zero is selected; the finite canonical value and the Green residue remain distinct.

## Paper argument

The unchanged derivative-pulse transform `P(z)` satisfies `P(0)=1` and
`|P(z)|≤2 exp(2|z|)`. The bound follows from
`P(z)=1−z onsetCorrection(0,−z)` and the actual transition bounds `0≤χ≤1`.
In the true/true physical channel its argument is exactly `5ρ/2−3`; no
duration is selected. Jensen's finite-exponential-type estimate therefore
bounds onset-dark simple critical copies up to height `T` by `O(T)`.

Above the corpus's fixed radial-moment threshold, a zero original residue
requires a zero angular coefficient or a zero onset. A zero angular
coefficient also makes the complete canonical action zero, by its exact
source-period formula. Its exceptional simple-critical count is already
`O(T)`. The bounded-height remainder is finite. Thus the original residue's
exceptional count is `O(T)`, whereas the actual simple critical census is
`Ω(T log T)`. The surviving fraction tends to one.

The full physical Laurent theorem makes this an actual nonremovable pole
of `continuedPhysicalSelfResponse`, with all principal corrections retained.
Its nonvanishing is independent of the interior observation point; quadratic
amplitude dependence extends survival to every nonzero original amplitude.
The full canonical action nevertheless has an analytic representative at
the same QNM. These assertions concern two explicitly different observables.

Every complementary unit-source probe is zero at every critical Xi copy,
for every returned vector. A surviving critical source therefore rules out
both equality with the genuine physical residue and equality of their zero
loci. Switching from the canonical finite value to the original pole cannot
repair this particular matching mechanism.

## Exact theorem and scope

[Lean module](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMOriginalGreenPoleMatchingNoGo.lean):

- `fundamentalPoleExceptionFinset_card_linear` and
  `fundamentalPoleExceptionFinset_relative_density_zero`: only linearly many
  exceptions; density-one survival among actual simple critical sources.
- `physicalPole_all_amplitudes_all_detectors`: each surviving unit residue
  yields a nonremovable pole for all nonzero amplitudes and all interior detectors.
- `exists_critical_regular_action_with_physical_pole`: an actual critical
  source has both an analytic full canonical action and genuine response poles.
- `not_exists_hbXiPeierls_physicalPole_matching` and
  `not_exists_hbXiPeierls_physicalPole_extinction_matching`: neither residue
  equality nor equality of zero loci with the unchanged unit probe is possible.

The receiver is exactly `continuedPhysicalSelfResponse`, with residue
`physicalSelfResidueCoefficient`, in the true/true fundamental channel.
The matching obstruction already holds at amplitude one and detector `−1`.
This does not classify every metric current, nonlocal receiver, or changed
source encoding. It proves no time-domain fixed-time extinction theorem.
General full temporal/metric/QNM matching and RH remain open.

Status: dependency-closed paper proof and Lean proof completed. Scratch check
passed in 10.21 seconds. Exact module audit passed in 9.12 seconds, two jobs.
The leaf is wired into `RHTower`; no umbrella build was run. No added axioms,
computational certificates, or raised heartbeat limits occur in the new leaf.
The global lint gate remains blocked by the separate, unwired module
`ThetaCuspHawkingBMOnsetTransgressionHorizon`; the new leaf has no lint error.
