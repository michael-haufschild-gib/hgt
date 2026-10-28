# Faithful scale transport on completed arithmetic apertures

## Actual domain and result

H_A is the existing CHMD apertureGraphCompletion for A>0, inside the original
complete source graph. Literal translation of smooth compact sources extends to
a bounded real linear map T_(A,t):H_A->H with image in H_(A+|t|).

For every bounded shift range |t|<=T there is C>=1, uniform over all p in H_A,
such that

||T_(A,t)p||^2 <= C||p||^2 and ||p||^2 <= C||T_(A,t)p||^2.

The map is injective and retains all mixed full-Weil pairings:

W(T_(A,t)p,T_(A,t)q)=W(p,q).

Every strip Fourier readout retains its exact source transformation:

FT(T_(A,t)p,z)=exp(i z t) FT(p,z),  |Im z|<=1/2.

This includes both poles at z=-i/2 and z=i/2, with factors exp(t/2) and exp(-t/2).
No radical quotient or synthetic replacement source is used.

## Dependency-closed proof

Represent each aperture-core vector by one of its literal smooth tests. The
bounded-window estimate applied to a difference f-g shows that equal graph
lifts have equal translated lifts. Thus the chosen representative defines a
well-defined linear map on the actual graph core. The same estimate bounds it
in the original graph norm.

Extend this bounded map along the existing isometric dense aperture-core
inclusion into the complete aperture. The extension agrees with every smooth
representative. A translated smooth source has support radius r+|t|<A+|t|, so
its image belongs to the enlarged aperture core. Closedness passes this property
to the completion.

Both sides of each graph-norm inequality are continuous, so the simultaneous
upper and lower bounds extend by density. The lower bound gives injectivity.
Full Weil energy is continuous on the graph and translation invariant on the
core; polarization gives the complete mixed identity. The existing strip
Fourier readout is continuous, and its compact-test translation law has factor
exp(i z t). Density therefore gives the stated strip identity, including both
pole coordinates.

## Lean status

File:
`formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CompletedAperturesCarryTheLiteralScaleTransport.lean`.

Key declarations:

- `apertureScaleTransport`
- `apertureScaleTransport_test`
- `exists_apertureScaleTransport_two_sided_bound`
- `apertureScaleTransport_injective`
- `weilForm_apertureScaleTransport`
- `weilBilin_apertureScaleTransport`
- `apertureScaleTransport_mem_target`
- `graphFourierReadout_apertureScaleTransport`

Individual no-olean audit passes. Printed capstones use only `propext`,
`Classical.choice`, `Quot.sound`.

## Scope and positive survivor

This is the complete-aperture positive replacement for unrestricted graph
control of translated compact sources. Aperture and shift range are explicit;
no constant uniform in their unbounded growth is asserted. The result supplies
faithful local source morphisms and preserves the full form and its polar
readouts. It does not determine the sign of the unpaid complement, identify a
complete growing Ramanujan family, or bound critical source energy above.
