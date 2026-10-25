# Arithmetic sharp and positive degree radicals

- **ID:** arithmetic-sharp-and-positive-degree-radicals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-II; genuine Meyer sharp-convolution algebra.
- **Statement:** Arithmetic sharp is a conjugate-linear convolution involution on genuine Poisson cohomology; a positive Hermitian degree has zero mixed reading on every null square class.

## Proof

Literal sharp multiplicativity follows from its exact Mellin transform,
source convolution multiplication, and Mellin injectivity. The already
constructed quotient reflection and conjugation maps give a conjugate-linear
involution on the actual Poisson quotient, with the same product identity.

A Hermitian degree therefore defines a complex sesquilinear pairing. On
real combinations its real part is a nonnegative symmetric quadratic form.
The existing quadratic null-radical lemma kills every real mixed part of
a null vector. Testing the imaginary multiple of the second input also
kills the imaginary part. Thus the complete complex mixed reading is zero.
No spectral sign, simplicity, or positive Hilbert realization is assumed.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/MeyerSharpConvolutionAlgebra.lean`.

- `meyerSourceSharp_convolution`
- `meyerCohomologySharp`, `meyerCohomologySharp_sq`
- `meyerCohomologySharp_convolution`
- `meyerDegreePair` and its two scalar and additive laws
- `meyerDegreePair_conj_symm`
- `meyerPositiveDegree_null_pair`

Actual-file `lake --old env lean` check passed. Four endpoint transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Temporary prints removed; ACS umbrella and README wired. This supplies the
algebraic foundation for finite positive-degree classification; that later
leaf is not certified here. External novelty unverified.
