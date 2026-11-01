# Integer-dilation independence over theta–Gamma coefficients

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [three approaches, B](argon-three-orthogonal-rh-approaches.md).

## Target

The actual functions `ζ(ms)`, indexed by all positive integers `m`, are
jointly differentially algebraically independent over
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩` in the common upper-end meromorphic field.
Consequently, for every integer `q≥2`, no nonzero finite polynomial
relation in the functions `ζ(q^j s)` and their derivatives can have
coefficients in this concrete theta–Gamma field.

This would obstruct the specified differential–Mahler realization while
preserving a full joint independence theorem. It would not exclude arbitrary
period coefficients or an unspecified nonlinear realization.

## Corpus inputs and remaining proof

The reciprocal integer-dilation tail is already jointly independent over
`ℂ(s)⟨ζ⟩` in `CompletePositiveKolchinFreeRiemannResolution`.
`JacobiThetaGammaCoefficientBoundary.thetaGamma_differentialIndependent_iff`
reduces the proposed coefficient field to the Gamma field. Neither result
alone discharges the mixed Gamma/dilation statement.

`GammaFieldCoefficientLaw` clears finite coefficient denominators and
supplies actual Gamma asymptotic shapes. `GammaJetRatioFamily` supplies a
dominant coefficient whose ratios tend to constants, with normalized limit
one. `EventualRelationFinitePhaseLaw.recurrence_collapse_of_bohr_return_eventual`
already handles arbitrary finite families of continuous almost-periodic
functions, not only jets of one scalar function.

A putative mixed relation should therefore reduce to a nonzero
constant-coefficient relation among the actual dilation jets:

1. Realize every finite dilation family and all required jets on one
   strip inside `Re s>1`.
2. Prove simultaneous almost periodicity of its finite jet monomials.
3. Clear the Gamma coefficients and apply dominant-ratio collapse.
4. Transfer the resulting line identity back to the common meromorphic
   field and contradict the certified joint dilation independence.
5. Apply the proved theta base-change equivalence; select powers `q^j`.

The finite-abscissa carrier is explicitly **rotated**:
`finiteAbscissaLSeriesUpperEndAnalyticElement f` represents
`LSeries f (−iz)`. Thus its dilation jets are not the unrotated jets used
by the theta–Gamma theorem. A constant-coefficient relation on the physical
right half-plane must be continued there, pulled back by `s=−iz`, and
transported with the nonzero jet factors `(−i)^r`. No equality of these
two carrier families may be assumed.

The generic recurrence lemma is available. The joint analytic realization,
coefficient clearing for mixed monomials, and common-field comparison remain
unproved here. No paper proof or Lean certificate is claimed.
