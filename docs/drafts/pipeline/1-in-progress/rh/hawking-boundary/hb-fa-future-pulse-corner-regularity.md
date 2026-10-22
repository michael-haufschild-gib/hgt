# Future pulse: characteristic corner regularity

Target remains full temporal/metric/QNM matching. DN77 closes only the original
future scalar bridge. The next necessary bridge is differentiability of its
actual pulse response, retaining both full angular fields and all boundaries.

[BRIDGE, paper derivation] Write target null coordinates `p=tau+x`, `r=tau-x`,
`w=r-p>0`, and compact source coordinate `z=exp(2*y)`. Above `v=r`, put
`a=v-r`, `b=1-z`. The actual direct invariant is

```
I-1 = 2*(1-exp(-w-a))*(exp(a)-1+b)/((1+exp(-w))*(2-b)).
```

The corner `a=b=0` invalidates a single chart which requires a strictly
positive factor after extracting only `sqrt(a)`. This is a coordinate
obstruction, not evidence that the pulse field is nonsmooth.

For a finite positive span `T`, split the unit square `(a/T,b)` into
two triangles. Their exact parametrisations and Jacobians are

```
first:  a=T*t,   b=t*u,  Jacobian=T*t;
second: a=T*t*u, b=t,    Jacobian=T*t.
```

Both satisfy `I-1=2*t*H`, where

```
H_first =(1-exp(-w-T*t))*(T*expc(T*t)+u)
          /((1+exp(-w))*(2-t*u));
H_second=(1-exp(-w-T*t*u))*(T*u*expc(T*t*u)+1)
          /((1+exp(-w))*(2-t));
expc(a)=(exp(a)-1)/a, continuously extended at zero.
```

For `w,T>0`, `t,u in [0,1]`, both H are strictly positive, including
the corner. Use `w=exp(W)`, `T=exp(L)`, `t=sin(A)^2`, `u=sin(B)^2`.
The signed radius `2*arsinh(sin(A)*sqrt(H))` is globally smooth and
equals `arcosh(I)` at `A=arcsin(sqrt(t))`, `B=arcsin(sqrt(u))`.
The corpus already proves smoothness of the actual full angular fields
at every positive-height circle point. Thus the original pulse, after
cancelling its exact `exp(2*y)` factor against the radial Jacobian, has
smooth compact integrands in these two charts. A fixed-cube integral then
permits derivatives in every target variable through this corner.

Lean verified: exact invariant factorisation; positive factor on both
closed triangles; actual-radius equality; original pulse factorisation;
smooth full-source chart integrand; equality of the chart integral with the
finite upper direct compact integral. The exact square-to-triangles formula is

```
integral_0^1 da integral_0^1 db F(a,b)
 = integral_0^1 dt integral_0^1 du t*F(t,t*u)
 + integral_0^1 dt integral_0^1 du t*F(t*u,t).
```

It follows from ordinary triangle Fubini and affine interval substitution,
including the boundary `t=0`. `upperSample_original` identifies each compact
sample with the original future pulse divided by `4*exp(2*y)`; the circle
radius is the original causal invariant, not a replacement. The auxiliary
clamp in the globally continuous sample extension is inactive on the square.
`upperDirectAction_smooth` is unconditional in the original Xi copy, physical
branch, amplitude, and all five real target/cutoff coordinates. Positive radial
width and finite span are parametrised by their logarithms.

Lower direct and image assembly, the single smooth cutoff and the omitted
source-horizon strip limits are now verified in `ThetaCuspHawkingBMFuturePulseAssembly`.
`ThetaCuspHawkingBMFuturePulseIdentity` identifies the full compact expression
with admitted A_P in original source-event coordinates and transfers smoothness.
Cap regularity and noncompact left-QNM admission remain separate obligations.
No finite chart result alone proves full matching or RH.

Search evidence: existing retarded horizon `expc`/`arsinh` charts and fixed-cube
smooth integration apply. Existing even-entire square factorisation requires
complex analyticity, not established for the complete real-smooth angular
source, so it does not close this step. Broad arXiv transmutation search found
arXiv:2601.03616 (June 2026 revision); its positive-semidefinite generator
hypothesis is not established for this physical source. No theorem from it
is used.

Lean leaf: `ThetaCuspHawkingBMFuturePulseCorner` (575 lines). Scratch passed in
42.12 seconds; exact leaf audit passed in 85.13 seconds, two jobs, no warnings.
Audited bytes match the installed source; its olean is present. Umbrella import
wired without building the umbrella. Repository lint still reports the existing
unreachable `ThetaCuspHawkingBMOnsetTransgressionHorizon` module; no issue names
the new leaf.

## Assembly facts

For the lower direct region use `v=p+w*alpha`,
`z=exp(-w*(1-alpha))*beta`. Its invariant factors as

```
I-1=2*alpha*(1-beta)*Hlower,
Hlower=exp(-w)*w*expc(w*alpha)/((1+exp(-w))*(1+z))>0.
```

For the upper image region use `v=r+T*alpha`, `z=beta`:

```
I-1=2*alpha*Himage,
Himage=T*expc(T*alpha)*(1-exp(-w-T*alpha)*beta)
       /((1+exp(-w))*(1+beta))>0.
```

These paper identities give signed smooth radii with prefactors
`sin(A)*cos(B)` and `sin(A)`, respectively. The strict positivity uses `w,T>0`.
Neither has the double-zero corner requiring the two-triangle subdivision.

A single smooth finite cutoff suffices for every target time: set
`T(r)=1+exp(-r)`. The inspected mathlib theorem `Real.add_one_le_exp (-r)`
gives `r+T(r)>=2`; the actual onset pulse vanishes whenever `v>1`.
Thus truncating both upper regions at `r+T(r)` loses no pulse contribution.
There is no need for separate cutoff patches when assembling the global pulse
regularity proof. These assembly identities are now Lean verified in
`ThetaCuspHawkingBMFuturePulseAssembly`; `ThetaCuspHawkingBMFuturePulseIdentity`
attaches the complete compact formula to the original source-event integral.
