# Schwartz spectral power-separation locality

- **ID:** `schwartz-spectral-power-separation-locality`
- **Stage:** 3-formalized
- **Type:** THEOREM / BOCHNER--SCHWARTZ INFRASTRUCTURE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `../../1-in-progress/hedenmalm-universal-positive-form-classification.md`

## Theorem

Let `Q` be a jointly continuous sesquilinear form on complex Schwartz space, pulled to the
spectral side. Let `A` be a continuous linear operator symmetric for this pulled form. Suppose
there are Schwartz packets `f,g` and inverse-power factors `h_n` such that

```text
A^n h_n = g,
A^n f -> 0,
h_n -> 0
```

in the full Schwartz topology. Then

```text
Q(f,g)=0.                                                  (1)
```

Indeed symmetry moves every power across the form:

```text
Q(f,g)=Q(f,A^n h_n)=Q(A^n f,h_n),
```

and joint continuity sends the last expression to `Q(0,0)=0`.

For a momentum-symmetric physical form, define the centered spectral momentum and positive
quadratic separator

```text
M_lambda(t)=2*pi*t-lambda,
A_(lambda,C)(t)=C^(-1)(1+M_lambda(t)^2).
```

Both are symmetric for the Fourier-pulled form. The quadratic multiplier is globally positive
and has a globally smooth reciprocal. If one compact packet lies in a strict sublevel

```text
1+M_lambda(t)^2 < C
```

and another lies in the complementary strict superlevel, direct powers contract the first packet
and reciprocal powers contract the second. Equation `(1)` is therefore the exact algebraic and
topological mechanism needed to prove their orthogonality without invoking an unavailable
Schwartz kernel theorem.

## Positive classification law

The natural Hedenmalm metric classification does not need a hidden kernel representation as its
first step. It must instead satisfy the following constructive chain:

```text
momentum symmetry
  -> symmetric positive quadratic separators
  -> Schwartz power contraction on separated compact packets
  -> spectral locality
  -> positive tempered spectral measure
  -> theta-null support on the real Xi divisor.
```

The first four arrows through arbitrary disjoint compact spectral locality are now formalized.
The remaining bridge is positive-order-zero representation and construction of the temperate
measure.

## Formal certificate

Files:

```text
formal/GaloisForLFunctions/HTGeometry/SchwartzSpectralPullbackForm.lean
formal/GaloisForLFunctions/HTGeometry/SchwartzSpectralQuadraticSeparation.lean
formal/GaloisForLFunctions/HTGeometry/SchwartzCompactPolynomialSeparation.lean
```

Theorem surface:

```text
ContinuousSchwartzSesquilinearForm.fourierPullback_clm_pow_symmetric
ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_clmPower_separation
ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_spectralPower_separation
tendsto_zero_of_tendsto_seminorm
seminorm_le_pow_mul_seminorm_zero_of_tsupport_subset
tendsto_seminorm_of_tsupport_subset_of_tendsto_seminorm_zero
tendsto_zero_of_uniform_tsupport_of_tendsto_zero_weight_seminorms
centeredSpectralMomentumCLM_apply
ContinuousSchwartzSesquilinearForm.fourierPullback_centeredSpectralMomentum_symmetric
quadraticSpectralSeparatorCLM_apply
quadraticSpectralSeparatorCLM_pow_apply
quadraticSeparationScale
quadraticPacketCoordinateBound
abs_le_quadraticPacketCoordinateBound
tsupport_quadraticSpectralSeparator_pow_subset
tsupport_quadraticSpectralSeparator_pow_packet
quadraticSeparator_inner_lt_one
quadraticSeparator_outer_inv_lt_one
seminorm_zero_zero_quadraticSpectralSeparator_pow_le
tendsto_seminorm_zero_zero_quadraticSpectralSeparator_pow_zero
hasDerivAt_quadraticSpectralSeparatorMultiplier
deriv_quadraticSpectralSeparator_pow_mul
seminorm_zero_one_quadraticSpectralSeparator_pow_le
tendsto_natCast_mul_pow_pred_zero
tendsto_seminorm_zero_one_quadraticSpectralSeparator_pow_zero
tendsto_natDescFactorial_mul_pow_sub_zero
tendsto_seminorm_weight_zero_quadraticSpectralSeparator_pow_zero
tendsto_seminorm_weight_one_quadraticSpectralSeparator_pow_zero
tendsto_quadraticSpectralSeparator_pow_zero
hasTemperateGrowth_inverseQuadraticSpectralSeparatorMultiplier
quadraticSpectralSeparator_pow_inverse_factor
tendsto_smulLeftCLM_pow_zero_of_compact_packet
tendsto_inverseQuadraticSpectralSeparator_pow_zero
ContinuousSchwartzSesquilinearForm.fourierPullback_quadraticSpectralSeparator_symmetric
ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_disjoint_quadratic_packets
ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_separated_interval_packets
exists_polynomial_zero_two_separating_compacts
polynomialSpectralMomentumCLM
polynomialSpectralMomentumCLM_apply
ContinuousSchwartzSesquilinearForm.fourierPullback_polynomialSpectralMomentum_symmetric
positivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth
inversePositivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth
ContinuousSchwartzSesquilinearForm.fourierPullback_positivePolynomialSeparator_symmetric
positivePolynomialSeparator_pow_inverse_factor
tendsto_positivePolynomialSpectralSeparator_pow_zero_of_compact_packet
tendsto_inversePositivePolynomialSpectralSeparator_pow_zero_of_compact_packet
ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_disjoint_compact_tsupport
```

## Boundary

The theorem assumes neither a measure representation nor positivity of the target Xi Bezoutian.
It proves locality for arbitrary disjoint compact spectral supports by a single polynomial
functional-calculus separator.  The positive temperate measure is not yet constructed.

Honest significance score: **35/100** in isolation. Its value is as a missing constructive link in
the potentially publication-level complete classification theorem.

## Gates

- [x] symmetric powers
- [x] abstract contraction-to-orthogonality theorem
- [x] concrete centered positive quadratic separator
- [x] canonical scale between inner and outer packets
- [x] direct-power contraction in the zeroth Schwartz seminorm
- [x] direct-power contraction in the first derivative Schwartz seminorm
- [x] lift derivative orders zero and one to every polynomial spatial weight
- [x] arbitrary fixed falling-factorial times geometric decay
- [x] exact Lean build
- [x] direct-power contraction in every higher derivative Schwartz seminorm
- [x] reciprocal-power Schwartz contraction on compact superlevels
- [x] strict quadratic-packet locality
- [x] separated compact-interval locality
- [x] one-polynomial localization to arbitrary disjoint compact supports
- [ ] spectral-measure representation
