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

C1-GMP-TR.1--4b are closed in Lean. Prove or refute the remaining explicit scalar identity
`rawFirstMoment - ‖barycenter‖² = thetaCuspNormalizedEvenMoment 1 / 2`; do not claim a completed
Weil landing before this comparison closes.

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
    \operatorname{tr}(C+D)=\operatorname{tr}C+operatorname{tr}D,
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
- [ ] **C1-GMP-TR.5** Prove or refute equality of this explicit scalar with completed Xi's first
  coefficient. Current source ceiling `2/25` is compatible with audited theta bounds and therefore
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

## Verification

- `lake env lean GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesGlobalMeanFirstTrace.lean` — PASS.
- `lake env lean GaloisForLFunctions/HTGeometry/InfiniteHilbertDispersion.lean` — PASS.
- `lake build GaloisForLFunctions.HTGeometry.InfiniteHilbertDispersion` — PASS (`1935/1935`).
- `lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesGlobalMeanFirstTrace` — PASS (`12792/12792`).
- Axiom audit of coordinate positivity, packet separation, positive trace, both exact trace laws,
  infinite Hilbert dispersion, source collapse, strict ceiling, and Xi landing criterion — PASS;
  only `propext`, `Classical.choice`, `Quot.sound`.
- Global formal lint — new modules reachable and clean; repository-wide gate remains red only on
  unrelated concurrent unreachable modules in `RHTower/Sieve` and `HTGeometry`.

## Literature audit update

Covariance operators of Hilbert-valued random variables, their trace-class positivity, and
second-moment-minus-barycenter identities are standard. Literature therefore defeats any novelty
claim for the generic variance algebra. No audited source concerns this arithmetic prime-depth
Pluecker family or identifies its nonlocal source trace with a completed Xi coefficient. Candidate
novelty remains only the corpus-specific exact trace package; no broad publication claim is made.

## Sharpened open core

C1 first-trace landing is no longer an operator-trace or double-series problem. It is the single
arithmetic identity
\[
  \sum_z a_z\sum_i n_{z,i}\mu_{z,i}
    -\left\|\sum_z a_zm_z\right\|^2
  =\Theta_1/2.
\]
Generic covariance literature does not decide this corpus-specific identity. Barycenter incidence
is now exposed as an explicit four-neighbor lattice square. Next loop must estimate that positive
collision penalty sharply enough to separate the audited theta interval, or prove exact equality.
