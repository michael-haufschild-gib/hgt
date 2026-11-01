# Integer-dilation independence over theta–Gamma coefficients

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Theorem

The actual functions `ζ(ms)`, indexed by all positive integers `m`, are
jointly differentially algebraically independent over
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩` in the common upper-end meromorphic field.
Consequently, for every integer `q≥2`, no nonzero finite polynomial
relation in the functions `ζ(q^j s)` and their derivatives can have
coefficients in this concrete theta–Gamma field.

This obstructs the specified differential–Mahler realization while
preserving a full joint independence theorem. It does not exclude arbitrary
period coefficients or an unspecified nonlinear realization.

## Corpus inputs and new contribution

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

## Paper proof

1. Replace each signed Möbius carrier by its negative inverse, except the
   first zeta coordinate. Coordinatewise mutual differential algebraicity
   preserves the certified joint independence.
2. Identify these carriers with the actual rotated functions `ζ(−imz)`.
   The dilated Möbius Dirichlet series equals `ζ(ms)⁻¹` on `Re s>1`;
   multiplication therefore gives the required identity of analytic germs.
3. Every physical jet of `ζ(ms)` is continuous and almost periodic on
   `Re s=2`: rescale the vertical zeta line and apply the nonzero chain
   factor `m^k`. Finite mixed jet monomials inherit both properties.
4. A constant polynomial relation on that line extends throughout
   `Re s>1`. Pulling back by `s=−iz` produces a relation among the rotated
   jets, with invertible factors `(−i)^k`, contradicting their independence.
5. A finite Gamma-field relation clears to analytic Gamma jet-algebra
   coefficients. Their asymptotic shapes have a dominant member; divide
   by it and use simultaneous Bohr recurrence. The resulting constant
   relation has one coefficient equal to one, contradicting step 4.
6. The theta base-change equivalence preserves this joint independence.
   Selecting the distinct positive integers `q^j` gives the stated
   differential–Mahler obstruction.

The finite-abscissa carriers are explicitly rotated; no automorphism of
arbitrary upper-end germs under rotation is assumed. Transport uses actual
analytic representatives on the right half-plane.

## Lean certificate

Module: `ArithmeticHarmonicAnalysis/IntegerDilationThetaGammaIndependence.lean`.
Namespace: `GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint`.

- `algebraicIndependent_gamma_of_line`: arbitrary almost-periodic families
  independent over constants remain independent over the actual Gamma field.
- `zetaDilation_differentialIndependent_gamma`: all physical integer dilates.
- `zetaDilation_differentialIndependent_thetaGamma`: the concrete mixed field.
- `mahlerZeta_no_polynomial_relation`: every nonzero finite jet polynomial.
- `mahlerZeta_representative`: exact physical representative `ζ(q^j s)`.

Direct production check passed with no diagnostics. All five transitive
axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
The module is imported by the ArithmeticHarmonicAnalysis umbrella.

The new contribution is the finite-family Gamma coefficient separation
and its actual-source application to all integer dilations. The arithmetic
carrier independence and theta differential-algebraic base change are
existing inputs. No priority beyond the audited corpus is claimed.
