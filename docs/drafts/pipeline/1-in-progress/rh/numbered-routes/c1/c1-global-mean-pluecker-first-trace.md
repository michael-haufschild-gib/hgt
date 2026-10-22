# C1 global-mean Pluecker first-trace landing

- **ID:** C1-GMP-TR
- **Stage:** 1-in-progress
- **Type:** CORPUS-LED CONJECTURE LOOP
- **Source:** read-only `rh-current-frontier-map.md`, C1 `LAND + COF` burden
- **Target:** Identify the exact first trace of the new positive trace-class global-mean Pluecker polarization and decide whether its nonlocal correction can meet the completed Xi/Weil first coefficient.

## Why this is the hardest current local burden

C1 already has finite adelic bands, finite trace formula, positive trace-class nonlocal source polarization, and explicit two-pole escape. The read-only ledger states the first missing step: Lean does not identify the new polarization's trace or moments with completed Xi/Weil data. This card attacks that exact interface, not another positivity construction.

## Corpus basis

- `GammaSewnMobiusApertureStokesGlobalMeanPolarization`: positive Schatten-one operator as packet covariance plus ordered pairwise mean dispersion.
- `GammaSewnMobiusApertureStokesPhysicalPluckerOrdinaryDeterminant`: exact ordinary trace of the packet covariance.
- `NuclearRankOneTrace`: trace commutes with absolutely norm-summable rank-one series.
- `FiniteHilbertDispersion` and `PairwiseVarianceIdentity`: finite Hilbert and infinite scalar pairwise-variance laws.
- `GammaSewnMobiusApertureStokesPhysicalPluckerFirstTraceNoGo`: local covariance trace lies strictly below completed Xi's first coefficient.

## Conjecture loop

- **C1-GMP-TR.1:** The mean-dispersion operator has exact ordinary trace equal to the ordered pairwise source energy
  \[
    \frac12\sum_{z,w}a_z a_w\|m_z-m_w\|^2.
  \]
- **C1-GMP-TR.2:** This trace correction is strictly positive: two explicit adjacent packets have distinct mean vectors.
- **C1-GMP-TR.3:** The full global-mean polarization trace is exactly the old local covariance trace plus this strictly positive nonlocal dispersion.
- **C1-GMP-TR.4:** Collapse the double energy to weighted second moment minus squared barycenter norm. Then compare the exact scalar with the completed Xi first coefficient. Equality lands the first moment; a strict mismatch retires this positive candidate and forces a signed/indefinite correction.

## Current open core

**Scoped RH retirement (2026-09-05):** Lean now excludes this literal global-mean carrier's exact
all-moment completed prime--Gamma landing, using its nuclear positive root and a factor-two,
multiplicity-exact ordered-moment bridge. See [audited source law and exclusion](../../../../3-formalized/c1-global-mean-nuclear-root-firewall.md).
The isolated first-trace question below remains undecided in Lean; resolving it can no longer make
this carrier an RH producer. Wider class-space C1 is not retired.

C1-GMP-TR.1--4e are closed in Lean. Prove or refute the remaining explicit scalar identity
`rawFirstMoment - ∑u physicalNode(u) * occupation(u)^2 = thetaCuspNormalizedEvenMoment 1 / 2`;
do not claim a completed Weil landing before this comparison closes.

## Novelty discipline

Generic variance identities are classical. Novelty is not claimed for them. Candidate new knowledge is the exact unconditional trace law and strict nonlocal trace lift for this corpus-defined arithmetic Pluecker operator, followed by its source-versus-Xi comparison. External literature audit is required before any publication claim.

## Log

- 2026-08-27 — card created after mandatory corpus search; frontier map treated as read-only.

## Proved first-trace package

- [x] **C1-GMP-TR.1** Exact ordinary trace:
  \[
    \operatorname{tr}D
      =\frac12\sum_{z,w}a_za_w\|m_z-m_w\|^2.
  \]
  Absolute nuclear summability justifies passage of `opTrace` through the ordered double sum.
- [x] **C1-GMP-TR.2** Strict positivity. Every packet-coordinate mean is positive. Packets
  `(0,0)` and `(0,1)` differ at physical cell `(0,0)`, so their ordered-pair summand is strictly
  positive and therefore `tr D > 0`.
- [x] **C1-GMP-TR.3** Full trace decomposition:
  \[
    \operatorname{tr}(C+D)=\operatorname{tr}C+\operatorname{tr}D,
  \]
  with both terms identified as exact real source masses. Hence global-mean completion raises the
  local covariance first trace strictly.
- [x] **C1-GMP-TR.4a** Exact completed-Xi landing reduction:
  \[
    \operatorname{tr}(C+D)=\Theta_1/2
      \iff
    \operatorname{tr}D=\Theta_1/2-\operatorname{tr}C.
  \]
  Corpus first-trace bounds prove the right-hand target gap is strictly positive.
- [x] **C1-GMP-TR.4b** Exact Hilbert barycentric collapse:
  \[
    \frac12\sum_{z,w}a_za_w\|m_z-m_w\|^2
      =\sum_z a_z\|m_z\|^2-\left\|\sum_z a_zm_z\right\|^2.
  \]
- [x] **C1-GMP-TR.4c** Exact source collapse:
  \[
    \operatorname{tr}(C+D)
      =\sum_z a_z\sum_{i=0}^3 n_{z,i}\mu_{z,i}
        -\left\|\sum_z a_zm_z\right\|^2.
  \]
  Thus local Bernoulli covariance and packet-mean second moment telescope to one uncentered
  arithmetic moment. The full trace is strictly below `2/25`.
- [x] **C1-GMP-TR.4d** Exact physical-incidence expansion:
  \[
    \left\|\sum_z a_zm_z\right\|^2
      =\sum_u\left|\sum_{(z,i):\ell(z,i)=u}
        a_z\sqrt{n_{z,i}}\mu_{z,i}\right|^2.
  \]
  Each interior physical cell has exactly four incident packet coordinates; `(0,0)` has exactly
  one strictly positive contribution. Hence barycenter is nonzero and global trace is strictly
  below raw first moment.
- [x] **C1-GMP-TR.4e** Conserved rank-two occupation and capacity reduction. The four coordinate
  marginals of every packet sum exactly to `2`. After removing the physical-node square root,
  the global occupation amplitudes are nonnegative, summable, and have total mass `2`; moreover
  \[
    \sum_u |\operatorname{incidence}(u)|^2
      =\sum_u n_u\,\operatorname{occupation}(u)^2.
  \]
  The two-coordinate law sharpens the raw packet and global ceilings from `2/25` to `8/125`.
  Every finite physical window obeys the reciprocal-node resistance/capacity inequality, and
  every packet supplies a four-cell certificate with captured mass at least `2 a_z`. Its
  resistance is now closed exactly as
  \[
    ((e+1)^2+(e+2)^2)\left(B_p^{-1}+B_q^{-1}\right),
  \]
  where `B_p,B_q` are the two depth-zero reciprocal-gap nodes.
- [ ] **C1-GMP-TR.5** Prove or refute equality of this explicit scalar with completed Xi's first
  coefficient. Sharpened source ceiling `8/125` is compatible with audited theta bounds and therefore
  is not itself a no-go.

## Lean realization

- Module: `GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesGlobalMeanFirstTrace`
- Generic infrastructure: `GaloisForLFunctions.HTGeometry.InfiniteHilbertDispersion`
- Umbrella: `GaloisForLFunctions.RHTower`
- Main theorems:
  - `gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean_pos`
  - `gammaSewnCriticalPhysicalPluckerMeanDifference_zero_right_ne_zero`
  - `gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass_pos`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionSourceTrace_eq_nuclearTraceMass`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_nuclearTraceMass`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff`
  - `tsum_pairwise_hilbert_dispersion`
  - `gammaSewnCriticalPhysicalPluckerMeanDispersionNuclearTraceMass_eq_secondMoment_sub_barycenter`
  - `norm_gammaSewnCriticalPhysicalPluckerMeanVector_sq`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_eq_rawFirstMoment_sub_barycenter`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_lt_two_div_twentyFive`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff_rawFirstMoment`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanIncidenceAmplitude_interior`
  - `norm_gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter_sq_eq_tsum_incidenceAmplitude`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanBarycenter_ne_zero`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_lt_rawFirstMoment`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff_incidenceAmplitude`
  - `sum_gammaSewnCriticalAdjacentPrime_PluckerCoordinateMean`
  - `gammaSewnCriticalPhysicalPlucker_packetRawFirstMoment_lt_eight_div_oneTwentyFive`
  - `tsum_gammaSewnCriticalPhysicalPluckerGlobalMeanOccupationIncidenceAmplitude_eq_two`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanCollisionEnergy_eq_weighted_occupation_sq`
  - `gammaSewnCriticalPhysicalPluckerGlobalMean_finiteOccupation_cauchy`
  - `gammaSewnCriticalPhysicalPlucker_packetResistance_eq`
  - `gammaSewnCriticalPhysicalPlucker_packetCollisionCapacity`
  - `gammaSewnCriticalPhysicalPlucker_packetCollisionCapacity_closed`
  - `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedSourceTrace_eq_theta_iff_weighted_occupation_sq`

## Verification

- `lake env lean GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesGlobalMeanFirstTrace.lean` — PASS.
- `lake env lean GaloisForLFunctions/HTGeometry/InfiniteHilbertDispersion.lean` — PASS.
- `lake build GaloisForLFunctions.HTGeometry.InfiniteHilbertDispersion` — PASS (`1935/1935`).
- `lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesGlobalMeanFirstTrace` — PASS (`12792/12792`).
- Axiom audit of coordinate positivity, packet separation, positive trace, both exact trace laws,
  infinite Hilbert dispersion, source collapse, rank-two occupation conservation, `8/125` ceiling,
  weighted collision factorization, finite capacity certificates, and Xi landing criteria — PASS;
  only `propext`, `Classical.choice`, `Quot.sound`.
- Global formal lint — new modules reachable and clean; repository-wide gate remains red only on
  unrelated concurrent unreachable modules in `RHTower/Sieve` and `HTGeometry`.

## Literature audit update

Covariance operators of Hilbert-valued random variables, their trace-class positivity, and
second-moment-minus-barycenter identities are standard. Fixed-size/projection determinantal point
process literature also makes rank conservation of inclusion marginals standard, so no novelty is
claimed for the abstract mass-two law or finite Cauchy capacity inequality. No audited source
concerns this arithmetic prime-depth Pluecker family, its exact conserved physical occupation, or
its completed-Xi coefficient reduction. Candidate novelty remains only the corpus-specific exact
trace/occupation package; no broad publication claim is made.

## Sharpened open core

C1 first-trace landing is no longer an operator-trace, double-series, square-root incidence, or
rank-conservation problem. It is the single arithmetic identity
\[
  \sum_z a_z\sum_i n_{z,i}\mu_{z,i}
    -\sum_u n_u\,\operatorname{occupation}(u)^2
  =\Theta_1/2.
\]
Here `occupation ≥ 0`, `∑u occupation(u)=2`, and every packet provides a finite four-cell capacity
lower bound for the collision penalty with a closed prime/depth resistance. Generic covariance/DPP
literature does not decide this corpus-specific identity. Next loop must prove a useful cofinal
block-weight floor (equivalently a denominator upper bound), combine several bounded-overlap packet
capacities, or sharpen the raw weighted node expectation enough to separate the audited theta
interval; otherwise prove exact equality.

## 2026-08-27 constructive-interference survivor (C1-GMP-TR.4f)

- [x] Every reverse-incidence fibre has cardinality at most four, including boundary collisions.
- [x] Local finite Cauchy retains energy inside the same physical window. Summing packet windows
  therefore loses at most multiplicity four; rank-two occupation supplies the cancelling factor
  four.
- [x] The resulting unconditional additive lower bound is
  \[
    \sum_z \frac{a_z^2}{R_z}
      \le \sum_u n_u\,\operatorname{occupation}(u)^2,
  \]
  with the exact closed prime/depth formula for every `R_z` substituted in Lean.
- [x] Stronger positive-interference law: because every packet contribution is nonnegative, the
  full collision dominates all packet self-collisions simultaneously, without overlap loss:
  \[
    \sum_z a_z^2\sum_{i=0}^3 n_{z,i}\mu_{z,i}^2
      \le \sum_u n_u\,\operatorname{occupation}(u)^2.
  \]
  This is strictly sharper than replacing the four marginals by their resistance-minimizing
  distribution.
- [x] Consequently the completed first trace obeys both explicit bounds
  \[
    \operatorname{tr}T
      \le M_{\rm raw}-\sum_z a_z^2\sum_i n_{z,i}\mu_{z,i}^2
      \le M_{\rm raw}-\sum_z a_z^2/R_z.
  \]

Generic nonnegative-square interference and finite Cauchy are elementary; no novelty is claimed
for those abstract inequalities. Candidate new knowledge is their exact arithmetic realization in
the corpus-defined adjacent-prime/depth Pluecker family and the resulting explicit completed-Xi
first-coefficient burden. Literature search found fixed-size DPP background but no treatment of
this prime-depth family or either exact trace bound.

New main Lean theorems:

- `gammaSewnCriticalPhysicalPluckerIncidentPackets_card_le_four`
- `gammaSewnCriticalPhysicalPluckerGlobalMean_finiteOccupation_local_cauchy`
- `gammaSewnCriticalPhysicalPlucker_packetSelfKernel_eq`
- `gammaSewnCriticalPhysicalPlucker_globalPacketSelfCollision_le`
- `gammaSewnCriticalPhysicalPlucker_packetCoordinateResistanceCauchy`
- `gammaSewnCriticalPhysicalPlucker_packetSelfCollisionCapacity`
- `gammaSewnCriticalPhysicalPlucker_globalAdditiveCapacity_le_packetSelfCollision`
- `gammaSewnCriticalPhysicalPlucker_packetLocalScaledCollisionCapacity`
- `gammaSewnCriticalPhysicalPlucker_finitePacketWindowEnergy_le_four_collision`
- `gammaSewnCriticalPhysicalPlucker_globalAdditiveCollisionCapacity`
- `gammaSewnCriticalPhysicalPlucker_globalAdditiveCollisionCapacity_closed`
- `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_le_rawFirstMoment_sub_packetSelfCollision`
- `gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedNuclearTraceMass_le_rawFirstMoment_sub_additiveCapacity`

Sharpened open burden: compare `M_raw - packetSelfCollision` with `Theta_1/2`. This supersedes the
previous suggestion merely to combine bounded-overlap packet capacities. A useful quantitative
bound now needs either direct control of the normalized squared denominator terms `a_z^2`, or an
upper bound on the cofinal denominator strong enough to make a finite packet prefix separate the
audited theta interval. Exact equality remains possible until that scalar comparison is closed.

Verification update: direct `lake env lean` PASS; exact module-only `lake build` PASS
(`12792/12792`); expanded axiom audit PASS with only `propext`, `Classical.choice`, `Quot.sound`.
Formal lint reaches this module from `RHTower` and reports no forbidden declaration here; global
exit remains red only for unrelated concurrent unreachable sieve modules.

## 2026-08-29 hostile scalar-landing computation

Nested multicore evaluation of literal Lean formulas converged to trace
`0.015633836564185256`, while independently evaluated theta target is
`0.02310499311541897`. Stable difference `-0.0074711565512337146` is too large to plausibly be
truncation error. Independent packet transcription and theta quadrature checks pass. Diagnostic
report:
`../2-fully-proven/computations/2026-08-29-c1-scalar-landing-hostile/REPORT.md`.

Status: current global-mean carrier is `COMPUTATIONALLY KILLED, FORMAL NO-GO PENDING`. Do not retire
card until strict mismatch is proved without numerical input. Most promising proof is exact finite
packet head plus analytic cofinal tail bound for
`rawFirstMoment - packetSelfCollision`; 32% relative margin makes this materially sharper target
than prior generic `8/125` ceiling.
