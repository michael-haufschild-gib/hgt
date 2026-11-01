# Rational-dilation independence over theta–Gamma coefficients

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Theorem

All actual functions `ζ(rs)`, indexed by positive rationals `r`, are jointly
differentially algebraically independent over the concrete field
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩` in the common upper-end meromorphic field.

For every positive rational `q`, the orbit `ζ(q^j s)`, `j≥0`, is jointly
differentially independent over this field iff `q≠1`. Consequently no
nonzero finite polynomial in its jets, with coefficients in this field,
vanishes when `q≠1`. Both expanding and contracting rational orbits are
covered. At `q=1`, all coordinates repeat.

## Proof

1. The positive real multiplier `r` preserves the upper half-plane, so
   `ζ(rs)` has an actual analytic representative there and defines a germ
   in the existing meromorphic field. Its field jets are represented by
   the ordinary physical derivatives.
2. Algebraic independence is determined by finite subfamilies. Restrict
   the full joint index `(r,k)` to an arbitrary finite set. A positive
   common denominator `D` makes every `m_r=Dr` a positive integer.
   Distinct pairs `(r,k)` give distinct pairs `(m_r−1,k)`, even when the
   same dilation occurs at several derivative orders.
3. Use the physical line `Re s=2D`. The exact chain rule gives

   `(ζ(rs))^(k)(2D+it)=D^(−k)(ζ(m_r z))^(k)(2+i t/D)`.

   The existing integer-dilation theorem supplies continuity, almost
   periodicity, and algebraic independence over constants of all integer
   jets on `Re z=2`. Invertible real-line reparametrization `t↦t/D` and
   the nonzero coordinate factors `D^(−k)` transfer these properties to
   the chosen finite rational jet family.
4. Apply the proved physical-line Gamma coefficient-separation theorem
   at `σ=2D>0`. Finite Gamma jet-algebra asymptotics and Bohr recurrence
   forbid any nonzero relation over the actual Gamma differential field.
   Gamma coefficients stay in the physical variable throughout; no
   scaling automorphism of that coefficient field is assumed.
5. Finite-subfamily independence yields independence of all positive
   rational dilations. The existing theta differential-algebraic
   base-change equivalence extends the coefficient field to the stated
   theta–Gamma field.
6. For `q>0`, `q≠1`, the natural powers `q^j` are distinct: strictly
   increasing for `q>1` and strictly decreasing for `q<1`. Restricting
   the independent rational family gives the orbit result. At `q=1`,
   the zeroth and first orbit coordinates coincide, contradicting the
   injectivity forced by algebraic independence.

There is no common line of absolute convergence for the entire rational
family. The argument only chooses a line after restricting to a finite
jet packet, so the shrinking multipliers of contracting orbits cause no gap.

## Lean certificate

Module: `ArithmeticHarmonicAnalysis/RationalDilationThetaGammaIndependence.lean`.
Namespace: `GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaRational`.

- `exists_positive_integer_scales`: positive integer realization of each finite packet.
- `jets_line_algebraicIndependent`: exact physical-line rational transport.
- `zetaDilation_differentialIndependent_gamma`: all positive rational dilates.
- `zetaDilation_differentialIndependent_thetaGamma`: the concrete mixed field.
- `mahlerZetaMero_differentialIndependent_iff`: sharp multiplier classification.
- `mahlerZeta_no_polynomial_relation`: no nonzero finite mixed jet polynomial.
- `mahlerZeta_representative`: literal physical orbit representative.

Direct production check passed without diagnostics. All seven transitive axiom
audits contain only `propext`, `Classical.choice`, `Quot.sound`.
The ArithmeticHarmonicAnalysis umbrella imports the module.

## Scope

The integer-dilation independence, physical-line Gamma separation,
finite-subfamily principle, and theta base change already existed.
The new contribution is their finite rational-denominator transport with
exact physical jet factors, including contracting Mahler orbits.
No literature-priority claim is made.

This excludes the specified rational differential–Mahler realization.
Special-value relations, arbitrary variable period coefficients, and
other nonlinear realizations remain outside the result. No RH conclusion
follows.
