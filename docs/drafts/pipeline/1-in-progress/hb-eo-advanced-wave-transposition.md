# Advanced wave equation for the original source

Target: identify the admitted full-source future integral, its retained lift
and source-derived cap with the physical advanced solution. This is required
for full temporal/metric/QNM matching; bulk skewness alone does not establish it.

[BRIDGE] Candidate: derive the advanced equation weakly from the original
kernel's closed-cone Goursat identity. Place derivatives on compact tests
before admitting the infinite source integral. Retain the full angular
Laplacian, the source vertex, the Dirichlet image and the original onset.

The available angular-jet estimates allow an unspecified exponential growth
exponent. They do not supply the strict bound below source decay needed to
differentiate the infinite future integral by those estimates. This is a
failure of that proposed justification, not a proof that the future field
lacks derivatives.

## Kernel transposition

In source-based null coordinates, the existing theorem gives
`H(u,v)=Q+integral[0,u] integral[0,v] J(a,b)` for `u,v>=0`, where
`H` is the original full-theta Riemann kernel and
`J=angularAction/(4*cosh(targetRadius)^2)`.

For smooth tests `phi,psi` with `phi(U)=psi(V)=0`, integration by parts
twice gives

`integral[0,U] integral[0,V] H(u,v)*phi'(u)*psi'(v)`
`= Q*phi(0)*psi(0) + integral[0,U] integral[0,V] J(u,v)*phi(u)*psi(v)`.

All integrals here are compact. This retains the source delta coefficient;
the two characteristic edges create exactly that vertex term.

## Angular transfer and the original infinite source

Write the angular chart as `z=X+ik`, with physical height `exp(k)`.
For a smooth compact test `psi`, define

`T(psi)=DX²(exp(k)*psi)+Dk²(exp(-k)*psi)+Dk(exp(-k)*psi)`.

Two directional integrations by parts give the exact identity

`integral exp(-k)*psi*angularAction(q,t)`
`= integral T(psi)*angularKernel(q,t)`.

The source field has no compact-support assumption. Its global angular
smoothness admits every localized product. Differentiating the test preserves
compact support. With `g=sourceGrowthExponent(q)<2`, the existing native-mean
estimate therefore bounds this pairing by

`Cq*exp(g*arcosh(t))*integral norm(T(psi))*exp(g*abs(k))`.

For the original future density and `g<alpha=(g+2)/2<2`, the joint
source/test product is bounded by a constant times

`exp(-alpha*tau)*exp((g-alpha)*h)*exp((2-alpha)*y)`
`*norm(T(psi)(z))*exp(g*abs(im(z)))`.

The first two source factors are integrable on `h>0,y<0`; the angular
factor is integrable by compact support. Admitted Fubini consequently gives

`integral T(psi)(z)*originalFutureResponse(tau,x,z)`
`= integral[h>0,y<0] testedDirichletAngularKernel(h,x,y)`
`  *timeReducedCoefficient(physicalRate,amplitude,tau+h,y)`.

Here `testedDirichletAngularKernel` is exactly one half the direct-cone
angular pairing minus the image-cone angular pairing, with both original
causal indicators. The fixed onset remains inside `timeReducedCoefficient`.
This source-level angular identity does not yet establish the temporal wave
equation, the lift/cap equations, or the full physical action.

The exact identities passed scratch checking and the isolated leaf-module
audit: `AdvancedKernelTransposition`, 119.64 seconds, two jobs. The module
is wired into `RHTower.lean`; the umbrella was not built.
Global lint reports the separate unwired `OnsetTransgressionHorizon` module.

[Formal proof](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMAdvancedKernelTransposition.lean):
`coneKernel_transposition`, `angularAction_compact_transposition`,
`tested_angularAction_growth`, `dirichlet_angular_transposition`,
`testedSourceDensity_integrable`, `original_future_angular_transposition`.

## Required closure

For a source event `(s,y)` and target null coordinates `p=tau+x`,
`r=tau-x`, the advanced cone distances are
`u=s+y-p`, `v=s-y-r`. The kernel is `H_y(v,u)`: the null arguments
are swapped. The time/radius Jacobian is `1/2`, the original Dirichlet
kernel carries `1/2`, and the principal wave operator is `4*Dp*Dr`.
Their product is one, fixing the source vertex coefficient. The image
vertex has radius `-y>0`, outside tests compactly supported in `x<0`.
These changes of variables and the general compact temporal-test identity
still require Lean proofs; a separated-test identity alone is not the
completed weak wave equation.

1. **Lean proved:** the displayed source-vertex identity for separated null
   tests of the actual kernel.
2. **Lean proved:** angular transfer, strict tested growth, both original
   Dirichlet cones and joint Fubini for the complete infinite future source.
3. **Open:** general compact temporal tests, the null-coordinate Jacobian
   and the complete weak wave equation for the existing future response.
4. **Open:** original lift/cap equations and boundary data, followed by
   identification with the full physical metric/QNM action.
