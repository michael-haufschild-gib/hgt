# Finite-index Euler-head Fredholm-response universality law

## Status

Formalized in Lean and wired into the RHTower umbrella. Kept in progress until global exhaustion
and final audit complete.

## Lean sources

- `GaloisForLFunctions.RHTower.FiniteSuperzetaFredholmLogDerivativeUniversalityLaw`
- `GaloisForLFunctions.RHTower.FredholmDeterminantEuler`
- `GaloisForLFunctions.HTGeometry.FredholmDeterminantExamples`

## Conjecture

The `Fin n` superzeta--Fredholm response law is independent of the chosen finite indexing type.
For every finite spectral packet `r : ι → ℂ`, its resolvent sum equals the cardinality-corrected
scalar-pencil logarithmic derivative of the diagonal trace-class determinant.

For the finite type of members of a finite prime set, the same determinant simultaneously has:

1. value at pencil parameter `1` equal to the finite Euler head anchor; and
2. logarithmic derivative at `1` equal to the cardinality minus the prime resolvent sum.

Thus one prime-indexed characteristic determinant carries both the multiplicative Euler-head
value and the additive spectral response.

## Corpus gap

Corpus search found the response theorem only for `Fin n`, while the Euler-head theorem uses a
finite-support diagonal operator indexed by all naturals. No theorem gives the intrinsic
finite-prime operator and its simultaneous determinant value/response law.

## Proof plan

1. Generalize the finite response proof to arbitrary `Fintype ι`, retaining the exact
   `Fintype.card ι` correction.
2. Instantiate `ι` with the subtype of members of `P`.
3. Use the finite diagonal determinant product theorem to identify the value at `1` with
   `RHTower.eulerHeadAnchor P s`.
4. Package the value and response equations in one theorem.

No numerical computation is used.

## Lean result

`formal/GaloisForLFunctions/RHTower/FiniteIndexEulerHeadFredholmResponseUniversalityLaw.lean`
proves:

- `finiteIndexedResolventValue_eq_fredholmDet1_logDeriv`;
- `finitePrimeFredholmDet1_eq_eulerHeadAnchor`;
- `finitePrimeEulerHead_fredholm_value_and_response`.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/FiniteIndexEulerHeadFredholmResponseUniversalityLaw.lean`

## Novelty status

Post-proof searches found standard sources for Euler products, Fredholm determinant product
formulas, determinant logarithmic derivatives, and resolvent traces separately. No matching
statement was located that packages the intrinsic finite-prime operator with both its finite Euler
head value and the exact cardinality-corrected prime-resolvent response. Novelty claim is limited
to this exact finite-index and finite-prime packaging; none of the classical component identities
is claimed new.
