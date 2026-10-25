# Arithmetic sharp is the Hilbert adjoint exactly for simple critical zeros

- **ID:** qii-meyer-sharp-adjoint
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** FORMALIZED. Actual-file direct Lean check and all three transitive axiom audits passed.
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** In the actual faithful full-Hasse Hilbert convolution representation, arithmetic sharp equals Hilbert adjoint for every original source if and only if RH holds and every Xi zero is simple.

## Corpus boundary

`DeningerMeyerHilbertConvolutionJets` proves the full triangular Hasse action,
the actual quotient convolution law, and operator multiplicativity.
`DeningerMeyerFaithfulConvolution` identifies the operator kernel with the
genuine Poisson boundary. `DeningerMeyerConvolutionWeilTrace` explicitly
distinguishes arithmetic sharp from the Hilbert adjoint. Corpus searches
found no theorem identifying them unconditionally.

## Formalized proof argument

Write `T_g` for the actual bounded convolution operator. Suppose
`T_(g^sharp)=T_g^*` for every source. If `g*g^sharp` is a Poisson boundary,
multiplicativity and boundary annihilation give `T_g T_g^*=0`. The operators
commute because source convolution commutes, so `T_g^*T_g=0` as well.
The Hilbert norm identity forces `T_g=0`; actual faithfulness gives that `g`
is a boundary. Thus the genuine Poisson ideal is sharp-square-root closed.
The dependency-closed theorem on the faithful-positive-degree card identifies
this condition exactly with RH and simplicity.

Conversely, assume RH and simplicity. Every Hasse block has only its zeroth
coordinate. The already proved triangular action reduces to
`(T_g x)(rho,0)=M_g(rho)x(rho,0)`. On a critical point arithmetic sharp sends
this multiplier to its complex conjugate. The coordinate formula for the
Hilbert inner product therefore gives
`inner(T_g x,y)=inner(x,T_(g^sharp)y)` for all vectors. Uniqueness of the
bounded adjoint proves the claimed identity. No new operator or spectral
realization is postulated.

## Positive survivor and implication

The exact condition for interpreting a literal arithmetic sharp square as
a positive operator Gram includes simplicity, while ordinary trace-square
positivity requires RH alone. Higher Xi jets are faithfully present in the
existing Hilbert representation; they cannot be silently replaced by
diagonal value coordinates when invoking Hilbert positivity.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/ArithmeticSharpAndTheHilbertAdjoint.lean`.
Direct `lake --old env lean` check **96392** passed. Audited endpoints:

- `meyerHilbertConvolution_apply_of_simple`
- `meyerHilbertConvolution_sharp_eq_adjoint_iff`
- `meyerHilbertConvolution_adjoint_iff_faithful_positive_degree`

All transitive audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Temporary prints are removed and the module is wired into its umbrella.
The construction uses the existing representation and certified sharp-root
criterion. External novelty remains unverified.
