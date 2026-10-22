# Constrained-prolate ground fixed-Gamma Ward/budget/Xi universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED]`

## Lean-derived conjecture

The normalized constrained-prolate ground Hermite source inherits the complete dominant-theta
fixed-half-line Gamma hierarchy:

- every even ground-source moment is the exact negative normalization multiple of the
  corresponding source Gamma coordinate;
- every positive even moment obeys the exact Liouville--Ward bridge to two consecutive Gibbs
  log-Gamma coordinates;
- because the normalization is negative, the theta half-density upper budget becomes an exact
  lower budget for the first three constrained ground moments;
- the same normalized source has Fourier transform equal to that normalization times completed
  Xi.

This joins local moment coordinates, the all-order Ward hierarchy, a signed endpoint budget, and
the global Xi transform for the identical prolate limiting source.

## Corpus inputs

- `constrainedProlateGroundHermiteSourceTerm_eq`
- `fourier_constrainedProlateGroundHermiteSchwartz_scaled`
- `thetaCuspAtomRawEvenMoment_one_eq_gammaIntegral`
- `thetaCuspAtomRawEvenMoment_succ_eq_liouvilleGibbs`
- `thetaCuspLiouvilleGibbsMoment_eq_singleGammaIntegral`
- `thetaCuspFirstAtomMomentTriple_le_halfDensityBudget`

## New connector

The prolate source-identification theorem is pointwise, while the theta Gamma, Ward, and
half-density theorems are stated only for theta moments. Integrating the pointwise negative
normalization transports all three mechanisms and reverses the budget inequality. The existing
prolate capstone contains the Xi transform but none of these moment consequences.

No numerical computation is used.

## Novelty protocol

Literature search was deferred until the theorem passed

`lake env lean GaloisForLFunctions/RHTower/ConstrainedProlateGroundFixedGammaWardBudgetXiUniversalityLaw.lean`.

Nearest sources found:

- Connes, Consani, and Moscovici, work on the prolate operator and the Riemann zeta function,
  develops the prolate spectral setting;
- Romik, *Orthogonal polynomial expansions for the Riemann xi function*, develops Hermite and
  other orthogonal expansions of Xi;
- Polson, *Incomplete Gamma Representations of the Riemann Xi Function: a Thorin Bernstein
  Framework*, SSRN 6954119 (2026), studies incomplete-Gamma Xi representations;
- Berenstein and Hulsey, *Anomalous Bootstrap on the half line*, arXiv:2206.01765, studies
  boundary moment recurrences.

No source found states the exact joint law for the normalized constrained-prolate ground source:
all-order fixed-half-line Gamma moments, scaled Liouville--Ward bridge, reversed three-moment
half-density budget forced by the negative normalization, and the exact scaled completed-Xi
Fourier transform.

## Lean target

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateGroundFixedGammaWardBudgetXiUniversalityLaw.lean`
