# HB original wave equation and ingoing source continuation

- **ID:** hb-original-wave-and-ingoing-source-continuation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Source:** [cusp spectrum and causal continuation](../1-in-progress/hb-cusp-spectrum-and-causal-continuation.md)
- **Statement:** The original mixed stream has its actual normalized wave equation. A fixed smooth ingoing onset gives the complete differentiated source tensor, an absolutely convergent current transform, and an entire regularization preserving the original source coefficient.

RH remains open. Chain: literal theta cusp → Xi occurrence → retained spin-two
source → original causal response and left-QNM pairing → independent
Hawking-clock extinction → RH.

## Original differential operator

Write `f=r²-1` and use the existing actual tortoise coordinate
`x(r)=(log(r-1)-log(r+1))/2`, whose derivative is `1/f` on r>1.
Thus its radial differentiation is `D_x=f*partial_r`. The new proof retains
the differentiated coefficient:

`D_x² psi=f²*partial_r² psi+2*r*f*partial_r psi`.

For the original stream profile H, construct the actual field `psi=H/r`.
Its complete coordinate two-jet is the product of the already proved actual
H jet and the actual reciprocal-radius jet. No time or spatial derivatives
are supplied as premises for this field.

The original master acting on a transverse covector has angular slot
`D_ang=roughLaplacian+identity`. Its exact normalization is

`(partial_t²-D_x²)psi*A-(f/r²)*psi*D_ang(A)=-(f/r³)*M(H,A)`.

This is proved directly from the original master and actual normalized jets.
For the constructed mixed response, both radial factors and the original
coefficient `c=s*(s-1)/4` remain. Since the original mixed master equals 2C,
the normalized wave source is exactly `-2*f*C/r³`. C is the complete original
quadratic current, including both the squared-source covector J and the
gradient-source covector K. This does not assume a reduced angular wave model
or positivity of an unconstructed spatial operator.

## Literal current and ingoing time

Fix an actual Xi occurrence, either branch, amplitude a, exterior radius r,
angular point z and component k. Let `v=2s` be the doubled physical rate.
The actual original envelope in ingoing time `u=t+x(r)` is

`a*exp(s*(u+log(1+1/r)))`.

Let C0(r,z,k) be the original current evaluated at ingoing time zero. It is
constructed from that envelope and the original J and K. Quadratic scaling
and the proved coordinate change give the exact identity

`C(t,r,z,k)=exp(v*(t+x(r)))*C0(r,z,k)`.

At every actual Xi occurrence, `Re(v)<-2`, independently of RH. For `Re(w)>0`,
the original current switched sharply at u=0 therefore has an absolutely
convergent time integral

`integral_(t>-x(r)) exp(-w*t)*C(t,r,z,k) dt
 = exp(w*x(r))*C0(r,z,k)/(w-v)`.

The factor `exp(w*x(r))` is derived from the onset surface. The source rate v,
angular fields and source amplitude stay fixed while w varies.

## Complete smooth-onset tensor

Use one fixed function `chi=Real.smoothTransition`: chi is zero before zero,
one after one, and smooth throughout. Put `C_sw=chi(u)*C`.

The actual orbit-coordinate jet of C is proved from the original envelope;
its time and radial derivatives are exactly vC and the original currentFirst.
Differentiating the actual onset gives

`partial_t C_sw=chi*v*C+chi'*C`,

`partial_r C_sw=chi*C_r+chi'*C/f`.

The original tensor reads these derivatives as
`S_t=f*C_r/r²` and `S_r=C_t/(r²*f)`. Consequently every component of the
switched source is the original source multiplied by chi, plus an onset tensor
whose two nonzero blocks are

`I_t=chi'*C/r²`, `I_r=chi'*C/(r²*f)`.

Both angular components and all symmetric partners are included. Lean proves
the full sixteen-component identity, complete vanishing before u=0, and exact
agreement with the original literal mixed tensor after u=1. This is a
constructed source extension in the current sector. It is not a proof of
admission to the full nonlinear source domain or of a retarded solution.

## Actual smooth source transform and continuation

For fixed v define the finite transition correction

`K_v(w)=integral_(0,1] (chi(u)-1)*exp((v-w)*u) du`.

The bounded transition difference, extended by zero on the positive half-line,
is in L2. Its transform on the finite interval is entire by the corpus's
proved truncated-Laplace theorem. Thus K_v is entire in w. Absolute convergence
and exact integration of the exponential give, when `Re(w)>Re(v)`,

`integral_(u>0) chi(u)*exp((v-w)*u) du=1/(w-v)+K_v(w)`.

The smoothly switched original current is evaluated in the original ingoing
chart and weighted by `exp(-w*(u-x(r)))`, the Laplace weight for static time.
Its actual half-line integral therefore converges for `Re(w)>0` and equals

`C_hat_sw(w)=R(w)*(1/(w-v)+K_v(w))`,

where `R(w)=exp(w*x(r))*C0`. Define

`N_sw(w)=R(w)*(1+(w-v)*K_v(w))`.

Lean proves N_sw entire, `C_hat_sw=N_sw/(w-v)` in the genuine convergence
chamber, and the exact physical-rate value

`N_sw(v)=R(v)=C(t=0,r,z,k)`.

Thus the fixed smooth onset preserves the original source-pole coefficient.
Its complex value is retained; nonvanishing is not assumed. These are integral
and analytic-continuation theorems for the actual source, not fitted scalar
response data or claims about a Green denominator.

## Remaining hard step

Construct the full retarded inverse for the original wave/operator domain and
the source above, retaining its radial endpoints, global modular cusp terms,
continuum and required source constraints. Continue that response from its
causal chamber and determine its source-dependent cusp coefficient. A proved
time transform at fixed radius and angular point does not supply spatial
integrability, a physical response domain, or the continued inverse.

The existing radial continuous-source Green action applies to its stated
reduced boundary problem and supported-source domain. It still needs an exact
operator, parameter and full-source identification here; its denominator
alone cannot replace those obligations. The complete response must then enter
the original left-QNM pairing. Gauge, other sectors, independent extinction
and RH remain open. No numerical experiment was used.

## Lean surface and audit

All modules use prefix `GaloisForLFunctions.RHTower.ThetaCuspHawkingBM` and
namespace `RHTower.D4BMModularCore`.

| Module suffix | New public theorems |
|---|---:|
| `StreamWaveOperator` | 4 |
| `MixedIngoingCurrent` | 2 |
| `MixedCurrentLaplace` | 4 |
| `MixedCurrentField` | 3 |
| `MixedCurrentCutoff` | 5 |
| `SmoothOnsetLaplace` | 3 |
| `MixedSmoothCurrentLaplace` | 5 |

All seven development leaves passed `lake env lean` in scratch. All seven
exact canonical `lake build <module>` audits passed in an isolated package
using existing dependency caches; no dependency or umbrella build was run.
Canonical sources and installed olean/ilean pairs were byte-checked against
the audit copies. All seven imports are wired exactly once into RHTower.

A scratch audit of only these 26 new public names passed: each depends only
on `propext`, `Classical.choice`, and `Quot.sound`. No added axiom, proof debt,
or computational certificate was used. Scoped whitespace checks passed.
The index was refreshed. Repository-wide `lint --check-generated` reported
an unrelated unreachable `DivisorCoreMellinStrip` module, stale generated
`LEAN_API.md` and `LEAN_OVERVIEW.md` during concurrent corpus edits, and 141
large-file warnings. It reported no proof debt or unwired new HB module.
The frontier map was not edited by this work.
