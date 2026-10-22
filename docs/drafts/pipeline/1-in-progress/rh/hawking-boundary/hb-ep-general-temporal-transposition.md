# General temporal testing of the original advanced kernel

Target: the temporal part of full temporal/metric/QNM matching, for the
original full-theta advanced response. Full matching and RH remain open.

[BRIDGE] Lean verified the original kernel's general temporal weak equation.
Scratch checking passed; the exact leaf audit passed in 40.29 seconds,
two jobs. The module is wired into `RHTower.lean`; no umbrella was built.

## Exact kernel identity

Let `Q=fullSquarePotential(q)(X,exp(k))`, `K_D` be the existing native
Dirichlet causal kernel, and `A_D` be one half the direct-cone angular
action minus the image-cone angular action, with their original indicators.
For every smooth compact joint time/radius test `phi`, the proved formula is

`integral[d tau d x] {K_D(s-tau,x,y)*wave(phi)(tau,x)`
`  - A_D(s-tau,x,y)*phi(tau,x)/cosh(x)^2}`
`= Q*(phi(s,y)-phi(s,-y))`.

Here `wave=partial_tau^2-partial_x^2` uses actual directional derivatives.
The residual integrand is absolutely integrable. If `y<0` and
`tsupport(phi)` lies in `x<0`, the image term vanishes and the right side
is exactly `Q*phi(s,y)`. Tests need not separate in time and radius.

## Proof mechanism

1. The native closed-cone Goursat formula is
   `H=Q+integral[0,u] integral[0,v] J`, with
   `J=angularAction/(4*cosh(targetRadius)^2)`.
2. Two compact integrations by parts for a general joint test give
   `integral H*eta_uv=Q*eta(0,0)+integral J*eta`.
3. In the actual advanced chart
   `tau=s-(u+v)/2`, `x=y+(u-v)/2`, the mixed test derivative is
   `wave(phi)/4`. Symmetry of the second derivative cancels the mixed
   time/radius terms.
4. Compact support of the test and its directional derivatives supplies
   all far-edge conditions and admits passage from a finite rectangle
   to the entire positive cone.
5. Decomposition into measure-preserving shears, one real scaling and a
   translation proves `map(pastVertex,volume)=2*volume`. Thus target area
   is `du dv/2`. Together with the kernel's original half-factor, the
   source coefficient is one.
6. Direct and image integrals are each admitted before subtraction. The
   image vertex is `(s,-y)`; its disappearance follows from physical test
   support, without discarding an edge or a kernel term.

The installed Zeta23 `PrimeSideB/PPKernel` shear proof supplied the useful
measure-preserving mechanism. The formalization uses its mathlib ingredients
directly. Corpus deep searches had partial compiler coverage; applicability
was checked by Lean.

[Formal proof](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMGeneralTemporalTransposition.lean):
`coneKernel_joint_transposition`, `pastVertex_volume`,
`temporalConeResidual_integrable`, `temporalConeResidual_integral`,
`dirichletWaveTest_integrable`, `dirichletWaveTest_integral`,
`physical_dirichlet_wave_transposition`.

## Whole-route consequence and remaining closure

General temporal tests, the actual source-coordinate Jacobian and both
source vertices are now identified at kernel level. The complete admitted
future response and its retained metric/QNM action are still not identified.

For the original future field `A`, original source coefficient `S` and
angular test operator `T` from the angular transposition theorem, the next
identity to prove is

`integral A*[exp(-k)*psi*wave(phi)-T(psi)*phi/cosh(x)^2]`
`= integral exp(-k)*Q*S*psi*phi`.

The existing `FullSourceRadialReciprocity.futureResponse_event_integral`
already identifies the original future response with its source-event
integral on `s>0,y<0`, retaining the fixed onset. This change of variables
does not need rebuilding. Its admission argument gives the source-event
majorant
`C*exp(-g*tau+g*abs(k))*exp((g-alpha)*s)*exp((2-alpha)*y)`
with `g<alpha<2`, uniformly in target radius and horizontal position.
Compact target tests therefore supply the relevant joint majorants.
Angular derivatives must be transferred to tests before admitting infinite
source integration; the corpus does not supply the required strict
pointwise angular-jet growth estimate. The remaining formal obligations
are uniform joint test/source admissions and the corresponding interchanges.

The lift/cap equations, complete physical metric/QNM matching, extinction
and RH remain open. No replacement field or assumed matching is introduced.

Global formal lint reports one separate existing error: the unwired
`ThetaCuspHawkingBMOnsetTransgressionHorizon` module. The new module passed
its exact audit and is wired into its umbrella.
