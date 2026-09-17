# HB literal causal source polarization

- **ID:** HB-B2-causal-source-polarization
- **Stage:** 2-fully-proven
- **Type:** BRIDGE
- **Source:** `ThetaCuspHawkingBMJointSourceAmplitude`, `ThetaCuspHawkingBMJointSourceTimeField`, `ThetaCuspHawkingBMFullNativeWave`, `ThetaCuspHawkingBMOriginalCausalPotential`; HB B2

## Exact statement

For an actual Xi copy `q`, branch `br`, and physical null wedge `0 <= p <= r`, put
`s = physicalRate q br`.  The literal retarded causal field obeys

`originalPotential(q,br,a,p,r,X,k) = a^2 originalPotential(q,br,1,p,r,X,k)`.

Consequently the genuine two-leg causal source and field are

`F[a,d] = a*d timeOriginalForcing(q,br,1)`,
`U[a,d] = a*d originalPotential(q,br,1)`.

They are symmetric in the two legs, obey the original forced wave equation, retain
the fixed onset and Dirichlet boundary condition, and satisfy the diagonal identities
`F[a,a]=timeOriginalForcing(q,br,a)` and
`U[a,a]=originalPotential(q,br,a)`.

## Dependency-closed paper proof

`sourceAmplitude` is, by definition, an amplitude-free factor times `a^2`.  Every
coefficient in `radialLift`, `radialLiftFirst`, `radialLiftSecond`,
`reducedCoefficient`, `timeReducedCoefficient`, and `timeOriginalForcing` is that
same source amplitude times an amplitude-free factor.  Thus each is exactly `a^2`
times its unit-amplitude value; in particular this recovers the already formal
`timeOriginalForcing_quadratic` identity.

`oddSource` is the difference of two `timeReducedCoefficient` values, so has the
same exact homogeneity.  On `p,r >= 0`, `fullNullResponse_native` writes the
response as the literal finite double interval integral of an amplitude-free native
Riemann kernel times `oddSource`.  Pull `a^2` through the inner and outer finite
integrals (the two applications of `intervalIntegral.integral_const_mul`) to obtain

`fullNullResponse(q,s,a) = a^2 fullNullResponse(q,s,1)`.

Likewise `nullLift` is `radialLift(s,0,a,1)` times the amplitude-free fixed onset,
so it is quadratic.  The defining equality

`originalPotential = fullNullResponse + nullLift * sourceProfile`

then proves the stated quadratic field identity.  The physical wedge is contained
in `p,r >= 0`, so no extension across a forbidden chamber occurs.  Multiplication
by the constant `a*d`, followed by `originalPotential_wave` at unit amplitude,
gives the polarized wave equation.  Boundary and before-onset identities follow by
the same multiplication from `originalPotential_boundary` and
`originalPotential_before_onset`.  On the diagonal, `a*d=a^2`, completing both
identities.

This is not a carrier reconstruction: the existing closed no-go
`not_exists_originalPotential_source_decoder` proves that the unchanged HB carrier
cannot determine the actual field, precisely because it loses this squared-amplitude
datum.

## Consequence for B2

The retarded leg required by the literal eight-face Peierls balance is now fixed:

`paired source -> U[a,d] -> finite Green/action faces -> noncompact cap/contact holonomy`.

It neither identifies a left-QNM limit nor proves the cap/contact comparison.  Those
are the sole remaining B2 content; the latter must yield `contactField` or a nonzero
holonomy mismatch that kills the realization.

## Lean status

Paper proof closed.  The intended leaf is a direct formalization of the displayed
finite-integral scalar pull and wave linearity.  Its target import currently stops
before elaboration at absent transitive artifacts recorded in F379; no broad build,
axiom, or unverified Lean theorem is claimed.
