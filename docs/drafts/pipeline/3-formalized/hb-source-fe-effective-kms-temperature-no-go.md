# HB source-FE effective KMS temperature no-go

- **ID:** HC85
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE-TEMPERATURE KMS PRODUCER NO-GO + EXACT THERMAL REALIZATION
- **Source:** read-only `rh-current-frontier-map.md` · HC84 local-cylinder product state

## Goal

Attack the hardest surviving physical producer after HC84: could Hawking KMS/Davies equilibrium
force the extended source-FE local state to be vacuum and hence force RH? Test that claim at the
exact coefficient level already present in the corpus.

Let `r(q)` be the literal source-FE recurrence ratio and set its effective thermal ratio
`Q(q)=‖r(q)‖²`. Prove `0 ≤ Q(q) < 1`, with strict positivity exactly off the critical wall. For every
off-wall copy construct an explicit positive surface gravity

`κ_eff(q) = -2π / log Q(q)`

at unit Bohr frequency, and prove the Hawking KMS Boltzmann ratio equals `Q(q)`. Then HC84's local
pair density

`p(q)=Q(q)/(1+Q(q))`

is exactly the excited Gibbs population of the corpus Davies block. Prove the source local
population `(1-p(q),p(q))` is stationary and satisfies detailed balance for every shell coupling.

This would kill positive-temperature KMS equilibrium as an RH producer: every off-wall local state
is itself an exact positive-temperature Hawking Gibbs equilibrium. Local vacuum is instead the
zero-temperature boundary and cannot follow from finite-temperature KMS alone.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` HC84 constructs the actual diagonal cylinder product state and identifies its one-mode
  density as `‖r‖²/(1+‖r‖²)`, vanishing exactly at the wall.
- `[CORPUS]` `ThetaCuspHawkingKMSFriedrichsMixingEndpoint` defines the literal Hawking ratio
  `exp(-2π ω/κ)` and proves it lies in `(0,1)` for positive `κ,ω`.
- `[CORPUS]` `ThetaCuspHawkingArakiWoodsDaviesMixingEndpoint` gives normalized Gibbs population
  `(1/(1+Q), Q/(1+Q))`, exact detailed balance, and exact stationarity.
- `[CORPUS]` source-FE modular dilation supplies the bosonic CCR identity
  `gain²-‖pair‖²=1`; HC82's recurrence ratio has the extra `sqrt 2` denominator. Together these
  force `‖r(q)‖²<1`, but that thermal interpretation is not yet in corpus.
- `[CORPUS]` `ThetaCuspHawkingHartleHawkingDoubleKMSEndpoint` already records that abstract purity
  or double-KMS thermality does not force source occupation alignment; its stronger aligned-pair
  diagnostic is an RH endpoint, not a derived producer.
- `[CORPUS NEGATIVE]` mandatory searches found no theorem constructing an exact positive Hawking
  temperature for every off-wall source-FE local state or proving Davies stationarity of that
  literal state.

## Theorem HC85-A: strict thermal-ratio range

Prove

`0 ≤ ‖r(q)‖² < 1`

for every Xi copy and

`0 < ‖r(q)‖² ↔ Re(q) ≠ 1/2`.

The upper bound must follow from the exact source-FE Bogoliubov normalization, not an added cutoff
or numerical estimate.

## Theorem HC85-B: exact effective Hawking temperature

For every `Q∈(0,1)`, prove `κ=-2π/log Q` is positive and

`thetaCuspHawkingKMSBoltzmannRatio κ 1 = Q`.

Specialize to `Q=‖r(q)‖²` off wall. No asymptotics or approximate matching are allowed.

## Theorem HC85-C: off-wall Davies equilibrium

Prove the HC84 source local population equals the normalized Hawking Gibbs population at
`κ_eff(q)` and unit frequency. Consequently, for every shell tilt/coupling parameter it is an exact
zero of the Davies population generator and obeys exact up/down detailed balance.

Also prove every positive-temperature, positive-frequency Gibbs excited population is strictly
positive. Therefore local vacuum cannot itself be a finite-positive-temperature KMS equilibrium.

## Hostile checks

- Do not confuse KMS existence with source-faithful same-sector Hartle--Hawking alignment. This card
  tests only the exact local Gibbs/Davies equations already formalized.
- Construct `κ_eff` and prove positivity; do not existentially postulate a temperature.
- Match the full normalized population pair, not only a proportional ratio.
- Prove stationarity through the actual corpus Davies generator and detailed-balance rates.
- Do not claim all CCR observables or a full interacting Liouvillean are covered.
- No RH hypothesis, computation, numerical bound optimization, or new axiom.

## Expected route impact

HC85 retires “Hawking KMS/Davies equilibrium forces vacuum” as a producer: off-wall
source states are exact positive-temperature equilibria. The positive survivor is sharp. Any viable
HB producer must add source-faithful occupation alignment, a zero-temperature/ground-state
selection, or a genuinely phase-sensitive Ward/centralizer law; ordinary thermal detailed balance
cannot orient the wall.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Araki--Woods,
  [*Representations of the Canonical Commutation Relations Describing a Nonrelativistic Infinite Free Bose Gas*](https://doi.org/10.1063/1.1704002),
  develops thermal infinite-volume CCR representations, not this source-FE effective-temperature
  identity.
- `[LITERATURE]` Davies,
  [*Markovian Master Equations*](https://doi.org/10.1007/BF01608389), gives rigorous weak-coupling
  Markovian dynamics, without Xi source ratios or RH endpoints.
- `[LITERATURE]` Higuchi--Lima,
  [*Hartle--Hawking State in the Real-Time Formalism*](https://doi.org/10.1103/PhysRevD.105.045002),
  proves Hartle--Hawking/double-KMS equivalence under horizon hypotheses, not source-FE local
  occupation selection.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining the literal Xi source-FE recurrence ratio, explicit positive Hawking temperature,
  exact HC84 Gibbs-population identification, and Davies stationarity/no-go. This is a bounded
  audit, not an exhaustive literature claim.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEEffectiveKMSTemperatureNoGo`.

- `norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_lt_half` derives the strict thermal range
  from the exact source bosonic normalization; positivity is exactly off-wall.
- `thetaCuspHawkingKMSBoltzmannRatio_effectiveKappa` inverts the Hawking exponential exactly, and
  the source specialization proves positive `κ_eff` off wall.
- `hbXiPeierlsUnitSourceFELocalPopulation_eq_effectiveHawkingDaviesGibbs` identifies the full
  normalized population pair, not only its ratio.
- Source local populations are exact zeros of every corresponding Davies generator and obey exact
  detailed balance for every shell coupling. The global off-wall realizability statement is
  unconditional.
- Every positive-temperature Gibbs excited population is positive; hence HB, Deninger/FZZ-P,
  PW-B, and canonical-copy RBH receiver-zero/local-vacuum states are incompatible with any such
  Gibbs identification.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEEffectiveKMSTemperatureNoGo`
passed all 12,192 jobs; representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules and
no HC85 finding.

## Open core after HC85

Ordinary positive-temperature KMS/Davies equilibrium is a proven dead producer and, pointwise,
selects positive occupation rather than vacuum. Hardest surviving HB branch is the stronger
source-faithful same-sector Hartle--Hawking alignment already isolated in corpus: derive occupation
alignment from quantized real theta-mirror dynamics, or prove independent charge-conjugate sectors
always evade it and retire that branch. Ground-state/zero-temperature selection and phase-sensitive
Ward-centralizer laws remain distinct possible producers.
