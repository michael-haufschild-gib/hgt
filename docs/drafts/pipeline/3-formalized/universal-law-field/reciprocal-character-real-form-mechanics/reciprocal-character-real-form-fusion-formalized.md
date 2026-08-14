# Reciprocal-character real-form fusion: Lean certification

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/reciprocal-character-real-form-mechanics/reciprocal-character-real-form-fusion-virial-reconstruction-and-gauss-admission-law.md`
- **Status:** [FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [RH EQUIVALENCE IS A SELECTION GATE]

## Certified modules

1. `formal/GaloisForLFunctions/HTGeometry/ReciprocalCharacterRealFormMechanics.lean`
   certifies:
   - the entire complexified reciprocal-character energy and finite-packet complexification;
   - exact split-axis and imaginary-axis restrictions, both locally and after finite fusion;
   - Euler--virial conservation;
   - common positive quadratic jet of the two real forms, locally and for the full finite packet;
   - hyperbolic coercivity and exact neutral radical;
   - finite-packet conservation, coercivity, and exact split/virial radicals.
2. `formal/GaloisForLFunctions/HTGeometry/ReciprocalCharacterRealFormReconstruction.lean`
   certifies:
   - positivity and injectivity of squared clock nodes;
   - first-`2r`-moment determination of the squared-clock spectrum;
   - all-future-moment reconstruction;
   - fixed-clock reconstruction of all source weights;
   - arbitrarily late compact-phase returns for the same marked prime clocks.
3. `formal/GaloisForLFunctions/RHTower/GaussReciprocalCharacterAdmission.lean`
   certifies:
   - exact realization of Gauss Hodge mass as reciprocal-character virial current;
   - the literal quadratic lower bound;
   - a uniform prime-harmonic lower bound off neutrality;
   - prime summability iff centered rate is zero;
   - universal summability over Xi zeros iff `RiemannHypothesis`.

All modules are wired into
`formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean`.

## Exact theorem surface

- `(RCV.6)`: `reciprocalPacketVirial_eq_t_mul_deriv`.
- `(RCV.7)--(RCV.8)`: `reciprocalPacketComplexEnergy`,
  `reciprocalPacketComplexEnergy_ofReal`, and
  `neg_reciprocalPacketComplexEnergy_mul_I`.
- `(RCV.9)`: `reciprocalPacket_common_quadratic_jet`.
- `(RCV.10)--(RCV.12)`: `sq_le_mul_sinh`,
  `reciprocalPacketVirial_quadratic_lower`, `reciprocalPacketVirial_eq_zero_iff`, and
  `reciprocalPacketSplitEnergy_eq_zero_iff`.
- `(RCV.13)--(RCV.14)`: `reciprocalSpectrumPoly_eq_of_moments_eq`,
  `reciprocalCharacterMoment_eq_of_eq_below`, and `reciprocalWeights_eq_of_moments_eq`.
- `(RCV.15)`: `reciprocalPrimeCharacter_exists_large_phase_return`.
- `(RCV.19)--(RCV.20)`: `gaussHodgeMassCurrent_eq_reciprocalCharacterVirial` and
  `gaussHodgeMassCurrent_virial_lower`.
- `(RCV.21)--(RCV.26)`: `summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero` and
  `forall_summable_gaussHodgeMassCurrent_iff_riemannHypothesis`.

## Audit

- Direct `lake env lean` checks pass for all three certification sources.
- `/tmp` axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for the
  mechanics and reconstruction capstones, including all newly completed finite-packet claims.
- New mechanics declarations contain none of `sorry`, `admit`, project `axiom`, `opaque`,
  `unsafe`, `decide`, `native_decide`, `norm_num`, or `omega`.
- Umbrella imports are present in `HTGeometry/UniversalLawField.lean`; Gauss admission is also
  present in `RHTower.lean`.

## Exact logical boundary

Lean proves

`(forall q, Summable (gaussHodgeMassCurrent m q)) <-> RiemannHypothesis`.

It does not prove the left side independently.  Field programme must generate that admission from
a pre-zero source trace/explicit-formula law.  Treating admission as an axiom would merely restate
RH and is forbidden.
