# HB modular energy domain and full weak angular response

Stage: formalized in Lean 4; final leaf audit passed. Type: `[BRIDGE]`.
RH remains open.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → physical
causal response and left-QNM pairing → independent fixed Hawking-clock extinction → RH.

The actual modular energy domain is constructed with a proved dense, injective
embedding into the original angular L² space. Its associated self-adjoint operator
supplies a unique finite-energy weak response to the complete cusp-subtracted
mixed Einstein forcing at every actual Xi occurrence, on both physical branches.
No form-domain, density, closability, inverse, or critical-line premise is supplied
to this final existence result. Smooth reconstruction and physical causal admission
remain open.

## Actual smooth modular core

Let `mu=UpperHalfPlane.volume.restrict ModularGroup.fd`. This is the original
invariant measure `dx dy/y²` on the modular cell. The previously proved forcing
vector F belongs to `H=Lp C 2 mu` and represents the full literal expression

`F=(L/2)S²-(Delta-L)(chi*H0)`.

Both Weyl terms, all signed Fourier modes and cross terms, and all cutoff
derivatives remain in F. Its construction and Xi modular matching are in
[the full forcing card](hb-global-angular-forcing-and-modular-continuation.md).

The smooth core consists of all globally real-smooth PSL2Z-invariant functions on
the upper half-plane with compact support in the quotient, represented in H.
Compact quotient support means that the field vanishes on the closed modular
cell outside some compact subset of the upper half-plane. The definition imposes
no vanishing condition on the joined modular sides.

For every compactly supported smooth test inside the cell interior, construct
its actual periodization

`Per(f)(z)=sum_(gamma in PSL2Z) f(gamma*z)`.

Proper discontinuity makes the sum a fixed finite sum in a neighborhood of each
point. The actual rational Mobius action is real smooth; thus the full periodization
is smooth, including at modular seams. Reindexing proves invariance. No nonidentity
projective modular translate can take a point of the closed cell into its interior
while contributing such a test, so `Per(f)=f` pointwise on the closed cell.

The corpus proves that the modular boundary has zero invariant measure. If an
L² vector is orthogonal to this constructed core, transport its scalar moments
to the complex coordinate. Smooth-test separation on the open cell interior
makes it zero there almost everywhere. The boundary-null theorem makes it zero
in H. Hence the full smooth modular core is dense in the actual H.

## Finite energy and faithful completion

For a real tangent direction v in the complex coordinate, define the literal
weighted derivative

`D_v f(z)=y*fderiv_R(f o ofComplex)(z)(v)`.

The hyperbolic orthonormal directions are v=1 and v=I. Chart smoothness makes
these derivatives continuous. Outside the compact support region, the field is
locally zero in the cell interior, so its actual derivatives vanish. A compact
bound, followed by the boundary-null theorem, proves that both derivatives belong
to H. Finite energy is therefore proved for every field in the full core.

Use the Hilbert space of triples `H ⊕ H ⊕ H` with the sum-of-squares norm.
For each core field retain the triple

`(f,D_1 f,D_I f)`.

Let V be the closure of the linear span of these actual triples and let
`J:V -> H` be scalar projection. V is a complete Hilbert space and
`||Jv|| <= ||v||`. The density theorem above proves that J has dense range.

Injectivity requires a further analytic proof. The native measure's pushforward
is proved equal to planar measure restricted to the complex cell and weighted
by `1/y²`. For a smooth compact test g supported strictly inside that cell,
this gives the exact identity

```
integral D_v f * (y*g) dmu = -integral f * (y²*partial_v g) dmu.
```

Squared height cancels the actual invariant density on both sides. The planar
integration-by-parts theorem requires differentiability of the field only on the
test support, so no unproved extension across the real axis is used. Compact
support controls every integrability premise.

Each identity is a continuous linear constraint on the triple Hilbert space.
Its closed kernel contains the original graph, its linear span, and its closure.
If a completed graph vector has zero scalar component, all compact test moments
of y times either gradient component vanish. These weighted components are locally
integrable on the cell interior. Smooth-test separation, positivity of y, and the
boundary-null theorem force both components to vanish in H. Consequently J is
injective. This proves closability of the actual differential graph and completes
the faithful modular form domain.

The closure uses the full globally modular core. Interior tests establish density
and detect gradients; their energy closure is not substituted for that full core.

## Constructed operator and actual forcing response

The existing Friedrichs construction applies to the proved complete domain and
continuous, dense, injective J. It constructs

`C=J*J.adjoint`, `A=C^(-1)` on the actual closed inverse graph.

A is self-adjoint and represents the value-plus-gradient inner product on V.
The exact decomposition is

```
<v,h>_V = <Jv,Jh>_H + sum_(i=1,I) <D_i v,D_i h>_H.
```

For the physical branches `s=rho-2` and `s=-rho-1`, put
`L=(2s+1)(2s+2)`. The existing Xi support theorem proves Im L is nonzero on both
branches. The actual operator therefore has a bijective shift `A-(1-L)`.
Apply its proved inverse to the original vector -F and use the adjoint form lift
to obtain h in V satisfying, for every v in V,

```
<v,h>_V - (1-L)*<Jv,Jh>_H = -<Jv,F>_H,
```

or equivalently

```
sum_(i=1,I) <D_i v,D_i h>_H + L*<Jv,Jh>_H = -<Jv,F>_H.
```

This is the finite-energy weak form of `(Delta-L)h=F`. For two solutions,
self-testing their difference and taking imaginary parts gives
`Im(1-L)*||J(h-k)||²=0`. Nonreality and injectivity of J give h=k.
`weakResponse` constructs this unique response; `weakResponse_spec` proves its
full forcing equation for every actual Xi occurrence and both branches.

## Lean surface and audit

All five modules are under `formal/GaloisForLFunctions/RHTower/`.

| Module | New public theorems | Proved surface |
|---|---:|---|
| `ThetaCuspHawkingBMSmoothModularPeriodization` | 4 | Actual locally finite smooth invariant extensions; exact cell values |
| `ThetaCuspHawkingBMSmoothModularCore` | 7 | Full modular-core density; boundary-null admission; actual finite derivative energy |
| `ThetaCuspHawkingBMModularWeakDerivative` | 4 | Native measure transport and literal weighted integration by parts |
| `ThetaCuspHawkingBMModularEnergyDomain` | 7 | Completed graph, dense contractive projection, preserved test identities, injectivity |
| `ThetaCuspHawkingBMGlobalAngularWeakResponse` | 7 | Actual self-adjoint operator and physical resolvent; full weak response existence and uniqueness |

All eight development scratch modules passed `lake env lean` without warnings.
All five exact-source leaves passed their individual `lake build <module>` audits
in a cache-only package, taking 2.9s, 8.4s, 11s, 18s and 10s respectively.
Only these five leaves compiled; existing dependencies were reused. Their source
bytes match the canonical files, their ten new olean/ilean artifacts are installed,
and each leaf is imported once by the RHTower umbrella. No umbrella build ran.

One scratch `lake env lean` audit checked exactly the 29 new public theorem
axiom sets. Every result contains only `propext`, `Classical.choice` and `Quot.sound`;
no added axiom or numerical certificate supplies proof. The source index refresh
and `scripts/formal_tools.py lint --check-generated` passed; the lint report has
existing large-file warnings. Scoped whitespace checks passed. No numerical
experiment ran. The frontier map remains read-only.

## Remaining physical bridge

The [interior regularity proof](hb-interior-elliptic-regularity.md) derives the actual
local distributional equation and complete cutoff commutator and proves H² for
every compact interior localization. Higher regularity remains necessary.
Obtain a smooth global representative of the weak response and identify its actual
hyperbolic differential equation across the modular charts. Construct the global
cusp-cutoff extension and assemble `chi*H0+h` as the full angular response.
Prove the physical causal prescription for the reconstructed vector metric.
The weak resolvent theorem does not establish this prescription or the horizon,
radial boundary, gauge and left-QNM conditions by itself.

Complete the SS/VV response sectors, retain the correction's actual linear image
in the original left pairing until its domain and boundary terms justify reduction,
and derive independent fixed Hawking-clock extinction. These remain necessary
for RH closure.
