# The Meyer trace radical is the quasi-inverse radical

- **ID:** meyer-trace-radical-is-the-quasi-inverse-radical
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q-II; actual all-weight source inversion and numerical radical.
- **Statement:** A genuine Meyer class u admits a quasi-inverse exactly when 1+M_u(rho) is nonzero at every Xi point. Every product uv admits a quasi-inverse exactly when all zeroth Xi values of u vanish. This is precisely the ordinary trace radical.
- **Status:** Lean-verified by direct actual-file check and transitive axiom audits. External novelty unverified.

## Actual inversion, without a completion premise

Use the literal commutative source convolution algebra modulo genuine Poisson
boundaries. A class u is quasi-regular when some actual class v satisfies

    u+v+uv=0.

The source theorem `exists_deningerMeyerSourceQuasiInverse` constructs such v
whenever 1+M_u(rho) is nonzero at every Xi point. Its proof uses actual strip
Bezout and global Xi division to produce an all-weight source; it is not a
bounded-operator inverse whose source admission remains unproved.

Conversely, evaluate u+v+uv=0 at any Xi point. Multiplicativity gives

    (1+M_u(rho))(1+M_v(rho))=1.

Therefore the first factor cannot vanish. This proves the exact inversion
criterion on the genuine quotient, including all multiplicities.

## Exact radical criterion

Call u quasi-radical if uv is quasi-regular for every actual class v. If every
M_u(rho) vanishes, each product has zero Xi values, so the inversion criterion
applies to every uv.

If M_u(rho) is nonzero at some rho, use the existing actual point source e_rho
with M_e(rho)=1 and put v=−M_u(rho)^(-1)e_rho. Then M_(uv)(rho)=−1. The product
uv cannot be quasi-regular. Thus

    u quasi-radical  iff  every zeroth Xi value of u vanishes.

The already proved trace-radical theorem identifies the right side with
vanishing of every mixed ordinary trace. Genuine boundaries require all jets,
so equality of this radical with the zero class is exactly simplicity of the
Xi divisor. No assertion of simplicity or absence of the radical is made.

The formal statement uses the displayed universal inversion condition as the
definition of the quasi-inverse radical.
The result concerns all products, not only scalar multiples or finite packets.
It does not assert global nilpotence of radical elements: local jet orders need
not have a common finite bound.

## Relation to positive degrees

This identifies the algebraic obstruction exposed by ordinary trace. It does
not by itself show that every positive algebraic degree kills the entire
radical or has no infinite source tail. Passing arbitrary positive functionals
through infinite expansions still requires an independent proof. Finite-packet
positivity and character classification remain separate unverified Lean candidates.

## Exact dependencies

- `DeningerMeyerConvolutionInverseSource.exists_deningerMeyerSourceQuasiInverse`.
- `MeyerNumericalRadicalAndMultiplicity`: exact trace radical and simplicity criterion.
- `PositiveMeyerDegreesCanForgetClasses`: actual point degrees and product formula.
- Actual quotient convolution and finite point-source interpolation.

## Lean certificate

`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerQuasiInverseRadical.lean`
passed direct `lake --old env lean` recheck **13602** after correcting the
conditional simplification from **62163**. All four transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`:

- `meyerQuasiRegular_iff_values`
- `meyerQuasiRadical_iff_values_zero`
- `meyerQuasiRadical_mk_iff_trace_radical`
- `meyerQuasiRadical_eq_zero_iff_simple`

The module is wired into the umbrella. No olean build is needed without an
actual importing module. No extra analytic premise or source-realization
field is introduced.
