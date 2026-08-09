# Mass-shifted three-point orbit polarity no-go — formalized closure

- **ID:** `mass-shifted-three-point-orbit-polarity-no-go-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./mass-shifted-three-point-orbit-polarity-no-go.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.MassShiftedThreePointOrbitPolarity`
(umbrella: `GaloisForLFunctions.RHTower`).

Reused unchanged: `RHTower/SquaredXiThreePointOrbitPositivity.lean` (abstract chamber
positivity), `RHTower/XiSquaredEulerApertureHilbertCorrelation.lean` (aperture Hilbert/charge
splitting), `RHTower/XiEndpointStrongHeightGap.lean` (squared-height gap `41/2`),
`RHTower/CentralReciprocalMoments.lean` (critical strip, `ρ ≠ 1/2`).

## Formal theorem chain

Chamber coordinates of one multiplicity copy `q` of an Xi zero `ρ`:
`xiOrbitTransverse q = (Re ρ − 1/2)²`, `xiOrbitHeight q = (Im ρ)²`,
`xiOrbitShear q = (Re ρ − 1/2)(Im ρ)`,
`xiOrbitDetuning q = v − u`, `xiOrbitCoupling q = 4uv`.

1. `xiOrbitTransverse_lt_quarter` — the critical strip gives `u < 1/4`.
2. `fortyOne_div_two_lt_xiOrbitHeight` — the endpoint-source height gap gives `v > 41/2`.
3. `two_lt_xiOrbitDetuning` — hence `t > 2`.
4. `xiOrbitCoupling_nonneg`, `xiOrbitDetuning_add_quarter_sub_coupling` — the exact chamber
   factorization `(t + 1/4) − c = (1 − 4u)(v + 1/4)`, and
   `xiOrbitCoupling_lt_detuning_add_quarter` — hence `c < t + 1/4`.
5. `xiOrbitMatrix_posDef`, `xiOrbitMatrix_det_pos` — **every actual Xi orbit** has a positive
   definite diameter-two three-point matrix `M(H)` with entries `H(0), H(1), H(4)`.
6. `neg_inv_sq_re`, `neg_inv_sq_im`, `xiOrbitDetuning_sq_add_coupling` —
   `t² + c = (u + v)²` and the Cartesian form of `λ = −((ρ − 1/2)⁻¹)²`.
7. `xiZeroCopyReciprocalSquare_re_eq_chamber` — `Re λ = t/(t² + c)`;
   `xiZeroCopyReciprocalSquare_im_eq_chamber` — `Im λ = 2·shear/(t² + c)`.
8. `orbitH_zero_eq_xiSquaredEulerApertureOrbitMass` — the `(0,0)` entry of the positive matrix is
   exactly the positive orbit mass `Re λ`; the two detectors are computed from one coordinate.
9. `xiOrbitConfluentMinor_eq` — equation `(1)`:
   `m₀m₂ − m₁² = −(Im λ)² ‖λ‖²` with `mₖ = Re λ^{k+1}`.
10. `xiOrbitConfluentMinor_neg_of_re_ne_half`, `xiOrbitConfluentMinor_eq_zero_iff` — strict
    negativity off the critical line, vanishing exactly on it.
11. `xiOrbit_separated_positive_and_confluent_negative`, `xiOrbit_polarity_split` — the no-go:
    each actual off-line orbit is simultaneously strictly positive in the separated-point matrix
    and strictly negative in the first confluent minor.

The positive survivor named on the paper card — "first Hankel minor = cross-orbit response-slope
Hilbert dispersion − total transverse boundary charge" — is already unconditional in
`XiSquaredEulerApertureHilbertCorrelation`:
`xiSquaredEulerFiniteApertureCentralMinor_eq_hilbertGram_sub_boundaryCharge` and
`two_mul_xiSquaredEulerFiniteApertureHilbertGram_eq_pairwiseDispersion`.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/MassShiftedThreePointOrbitPolarity.lean` — clean,
  no warnings.
- `lake build GaloisForLFunctions.RHTower.MassShiftedThreePointOrbitPolarity` — green.
- `#print axioms` on statements 1–11: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella import present in `GaloisForLFunctions/RHTower.lean`.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: external novelty audit incomplete
