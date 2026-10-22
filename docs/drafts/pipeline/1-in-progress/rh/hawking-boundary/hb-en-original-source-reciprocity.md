# Original source reciprocity in physical time and radius

Target: full temporal/metric/QNM matching. The missing identification concerns
the physical causal source pairing, including its source, lift and boundary
terms. An abstract skew pairing does not supply that identification.

[BRIDGE] Candidate: the original full-theta Dirichlet kernel and actual
quadratic reduced forcing admit reciprocity on the entire physical time and
radial domains. This would construct the reduced-source bulk pairing before
attempting its metric, angular-boundary and QNM identification.

Write `f_b(t,x)=timeReducedCoefficient(physicalRate(q,b),a,t,x)` and
`K(h,x,y;X,k)=nativeDirichletCausalKernel(q,h,x,y,X,k)`. The kernel
includes the full theta-square circular mean, both causal indicators,
the reflected image and the original factor `1/2`. Source time is unchanged.
The physical event measure is `dt dx` on `t>0, x<0`.

## Paper proof

Put `g=sourceGrowthExponent(q)` and `alpha=(g+2)/2`. The established
source and kernel estimates give `1<=g<alpha<2`,

`|f_b(t,x)| <= A exp(-alpha*t) exp((2-alpha)*x)`,

`|K(h,x,y;X,k)| <= C exp(g*(h+|k|))` for `h>=0`.

For `h<0` both causal indicators vanish. Thus the original two-event
density `f_b(t,x) K(s-t,x,y;X,k) f_c(s,y)` is bounded by a constant times

`exp(-(alpha+g)*t) exp((g-alpha)*s)`
`* exp((2-alpha)*x) exp((2-alpha)*y)`.

Every factor is integrable on its original half-ray. The density is
measurable: extend the kernel's `arcosh` argument by `max(1,z)` to obtain
a continuous representative and remove that extension on each causal cone.
The complete four-variable source integral is therefore absolutely admitted.

The invariant defining the circular mean is symmetric in `x,y`;
the image invariants at `(x,-y)` and `(y,-x)` agree as well. Consequently
`K(h,x,y)=K(h,y,x)` with the original causal supports intact.

The admitted future response equals
`A_c(t,x)=integral K(s-t,x,y) f_c(s,y) ds dy`.
To verify this against its existing definition, interchange the admitted
future-delay and radial integrations, translate `s=t+h`, and use the
kernel's zero negative-delay support and the source's zero pre-onset support.
The corresponding past integral is
`R_b(s,y)=integral K(s-t,y,x) f_b(t,x) dt dx`.
Fubini and radial symmetry then give the exact identity

`integral f_b A_c = integral R_b f_c`.

The causal difference is the antisymmetric two-source density:

`integral f_b (R_c-A_c)`
`= integral K(s-t,x,y) [f_c(t,x)f_b(s,y)-f_b(t,x)f_c(s,y)]`.

No reciprocity premise or late-onset replacement enters this derivation.
Multiplication by the unchanged angular theta-square at the testing point
restores the other full reduced-source factor and preserves the identity.

The literal completed scalar and its square are invariant under
`rho -> 1-rho`; the actual rates exchange branches. Thus the full kernel
is invariant, and the admitted square-source causal pairing obeys
`P(reflect(q),true,false,a,d) = -P(q,true,false,d,a)`.
Both independent amplitudes are retained. This is a proved transport law
for the source integrals, not an assumed property of a packet propagator.

## Exact scope

This constructs time/radial reciprocity for the full angular **reduced**
source bulk. The square/gradient source reduction still has its original
lift and characteristic cap terms. The retarded kernel integral must be
identified with the existing null-coordinate physical field; the future
field's advanced wave equation and full metric reconstruction must be
proved. Its pairing must then be attached to the complete metric/QNM
action with angular boundaries retained. No such attachment, extinction
selector or RH proof follows from bulk reciprocity alone.

## Lean status

[FullSourceRadialReciprocity](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullSourceRadialReciprocity.lean)
proves absolute admission, identification of the established future response
with its source-event integral, exact retarded/advanced radial reciprocity,
the antisymmetric two-source decomposition, full square-source admission,
and physical branch reflection. No unproved reciprocity premise is used.

Scratch check passed in 9.34 seconds. Isolated exact module audit passed
in 11.95 seconds (two jobs). Two missing prerequisite oleans were compiled
sequentially in 43.08 and 18.15 seconds. The new leaf is wired into its
umbrella; no umbrella build was run.
Global lint reports only the separate unwired
`ThetaCuspHawkingBMOnsetTransgressionHorizon` module as an error.
