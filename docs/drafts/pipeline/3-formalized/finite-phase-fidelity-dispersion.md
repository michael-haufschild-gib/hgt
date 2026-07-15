# Finite phase fidelity dispersion

- **ID:** `finite-phase-fidelity-dispersion`
- **Status:** `[PROVED IN LEAN] [BRIDGE] [CORPUS-USEFUL] [POSITIVE RESIDUE]`
- **Scope:** general clock observability, interferometric fidelity, Loschmidt amplitudes,
  prime-squarefree phases

## Statement

Let `w_i` be finite normalized real weights and let `u_i` be unit complex phases.  Define the
weighted phase overlap

`A = sum_i w_i u_i`

and the pairwise phase dispersion

`D = sum_(i,j) w_i w_j |u_i-u_j|^2`.

Then

`D = 2 (1-|A|^2)`.

If the weights are nonnegative, the fidelity deficit `1-|A|^2` is nonnegative.  If every weight is
strictly positive, then

`1-|A|^2 = 0 iff u_i=u_j for every i,j`.

Thus the overlap is a faithful detector of relative phase agreement even though all coordinate
Born probabilities and every expectation/variance formed from them are unchanged by a unimodular
phase twist.

## Positive residue of phase blindness

`ProjectiveFisherBlindness.lean` proves that Born probabilities and their Fisher variance forget
fixed coordinate phases.  The present theorem does not stop at that no-go.  It identifies the
minimal positive replacement: retain one coherent overlap with the phase-twisted packet.

The replacement is exact, not qualitative.  Its value is the complete mean squared pairwise phase
separation, and its zero set is exactly the diagonal/global-phase configuration on positive
support.

## Physics relation

The weighted overlap is the Loschmidt amplitude or characteristic function of a finite spectral
distribution.  Its squared magnitude is an interferometric fidelity/visibility.  The pairwise
formula says that loss of visibility is exactly phase dispersion among the clock readings.

Related physics sources:

- T. Palmai and S. Sotiriadis, *Quench echo and work statistics in integrable quantum field
  theories*, arXiv:1403.7450, relates Loschmidt echoes to work distributions.
- T. Qureshi, *Interference Visibility and Wave-Particle Duality in Multi-Path Interference*,
  arXiv:1905.02223, treats pairwise multipath visibility/coherence.
- Z. Chen and X. Hu, *Resource theory of dephasing estimation in multiqubit systems*,
  arXiv:2304.14615, identifies Hamming-distance-preserving structure in multiqubit dephasing.

The formal identity is static: the phases are values attached to observational sectors.  No claim
that the differential variable is physical time is used.

## Formalization

General module:

- `formal/GaloisForLFunctions/HTGeometry/FinitePhaseFidelityDispersion.lean`.

Declarations:

- `finitePhaseOverlap`;
- `finitePhasePairwiseDispersion`;
- `finitePhasePairwiseDispersion_eq_two_mul_fidelityDeficit`;
- `finitePhase_fidelityDeficit_nonneg`;
- `finitePhase_fidelityDeficit_eq_zero_iff`.

Direct prime consumer:

- `formal/GaloisForLFunctions/RHTower/PrimeMobiusPhaseFidelity.lean`.

The squarefree Bernoulli weights underlying the finite prime Möbius packet are normalized and
strictly positive, while the existing Gelfond--Schneider theorem makes the time-one squarefree
prime phases injective.  Therefore

`prime phase dispersion = 2 x prime fidelity deficit`

and

`prime fidelity deficit = 0 iff the prime aperture is empty`.

Consumer declarations:

- `finitePrimeSquarefreePhaseDispersion_eq_two_mul_fidelityDeficit`;
- `finitePrimeSquarefreePhase_fidelityDeficit_eq_zero_iff_empty`.

## Corpus value

1. Supplies a phase-sensitive positive observable after the existing Born/Fisher no-go.
2. Converts fidelity deficit into an explicit pairwise sum that is easier to estimate and compare.
3. Gives a zero criterion requiring no compactness, dynamics, or spectral-limit hypothesis.
4. Applies directly to the existing prime Möbius/Loschmidt packet and discharges its normalization,
   positivity, and phase-separation hypotheses from existing theorems.
5. Generalizes beyond hypertranscendental functions to every finite weighted phase packet used as
   an observational clock.

## RH impact and boundary

This does not prove RH.  It establishes a useful selector distinction:

- magnitude-only Fisher data are phase-blind;
- coherent source overlap retains relative phase dispersion;
- on the prime-squarefree packet it already detects nonempty arithmetic support exactly.

For RH, the next noncircular question is whether an actual prime--archimedean coherent overlap has
a source-controlled zero or extremal set that selects critical orientation.  The theorem provides
the exact positive value to target, but the present prime consumer detects aperture support, not
the Xi critical line.

## Boundary attacks

1. **No-go-only attack.**  The result is a faithful positive phase observable with an exact zero
   criterion.
2. **Fisher redressing attack.**  Fidelity uses coherent cross-coordinate interference and is not
   a function only of Born probabilities.
3. **Dynamics attack.**  The proof is a finite weighted norm identity; no time propagation is
   assumed.
4. **RH-circularity attack.**  The prime consumer uses existing unconditional phase injectivity and
   proves only aperture detection; no critical-line conclusion is claimed.

## Verification

- Exact targets:
  - `GaloisForLFunctions.HTGeometry.FinitePhaseFidelityDispersion`;
  - `GaloisForLFunctions.RHTower.PrimeMobiusPhaseFidelity`.
- Direct source checks: both touched Lean modules.
- Axiom audit: expected only Lean/mathlib logical foundations.
