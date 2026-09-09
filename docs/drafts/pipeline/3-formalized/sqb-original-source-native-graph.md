# SQB original corrected source in the native closed graph

Status: 58 public declarations formalized, individually built and axiom-audited.
RH remains unproved. Frontier map is read-only.

Full chain: original modular source → entire-transform operator → independent
occurrence at every full Xi parameter → critical-line classifier → RH.

## Exact result

For every actual Xi copy q, let rho be its full complex zero, let
`e=1+(rho/2)(1−rho/2)`, and let R be the original globally glued corrected
source. Its native L² vector is V. Let H be the complete original cutoff-forcing
vector, already proved nonzero. The native operator is `A=1−Delta_H`, constructed
from the original modular value-and-gradient form; its bounded inverse is B.

The new construction proves, with no source-domain or convergence premise,

`V belongs to domain(A)`,

`A V − e V = H`,

`V − e B V = B H`.

These identities identify the original source itself. They retain every signed
Fourier–Bessel family, the original invariant measure, closed-cell seams and
elliptic points. They do not make H zero or prove entire-transform occurrence.

## Compact modular approximants

Put `a_n=n+3` and `beta_n(y)=smoothWeight(a_n,a_n,y)`. The previously proved
smooth-weight construction gives beta in [0,1], equal to one below a_n and
zero above 2a_n, with order-j derivative bounded by `C_j/a_n^j`.

The height formula glues to a globally smooth modular cutoff. Parabolic
translations preserve height. At a nonparabolic closed-cell overlap both
heights are below 2; since a_n≥3, both cutoff germs equal one there. Thus
cell-germ gluing is valid on the entire closed cell. The cell support lies in
the compact truncated cell of height 2a_n. Multiplication by the complete
original R gives an actual compact modular core field f_n.

The full compact-core operator theorem supplies each native domain vector V_n
and its exact representative `f_n−Delta_H f_n`. The cutoffs have norm at most
one and eventually equal one at every point. The existing strong bounded
multiplier theorem therefore gives `V_n → V` in the original Hilbert norm.

## Complete vertical derivative and cutoff errors

The actual full Fourier–Bessel derivative theorem expresses each vertical
value derivative as three shifted families: one with the power lowered by one,
and two with Bessel order shifted by ±1 and derivative index raised by one.
The existing full-family estimates bound all three after multiplication by
any fixed real height power. Adding both signed families bounds the derivative
of the complete scalar tail, without truncation.

On the upper cell, the original corrected source germ equals that full tail.
On the compact lower cell, global smoothness bounds the actual weighted
vertical derivative. Thus `D=y∂yR` is a genuine vector in native L².

Set `delta_j,n(y)=y^j beta_n^(j)(y)`. On y≤2a_n the uniform derivative estimate
gives `|delta_j,n|≤2^j C_j`; above 2a_n all derivatives vanish. For j>0 these
multipliers eventually vanish at every fixed point. They therefore converge
strongly to zero on every native Hilbert vector.

The full two-coordinate Laplacian product rule, transferred through the actual
source and cutoff germs, gives on every closed-cell point

`Delta_H f_n = beta_n Delta_H R + delta_2,n R + 2 delta_1,n D`.

The original H vanishes above height 3, where every beta_n is still one.
Consequently `beta_n H=H` exactly for every n. Passing the complete pointwise
formula to actual L² representatives proves

`A V_n = e V_n + H − delta_2,n V − 2 delta_1,n D`.

Both error terms tend to zero in native norm. Hence `A V_n → Q=eV+H` in
native norm, independently of the already proved value convergence.

## Identification in the closed graph

For each admitted approximant, the actual inverse identity gives `B A V_n=V_n`.
Boundedness of B and uniqueness of limits now give `B Q=V`. The original
operator domain is the actual range of B, so this identifies V in domain(A).
The other exact inverse identity gives `A V=Q`. Subtracting eV proves the
retained forced equation; applying B yields the bounded resolvent equation.

This use of the constructed inverse is the graph-closedness argument in
explicit form. Smoothness and a pointwise equation alone were not promoted to
an operator-domain assertion.

## Exact entire forcing transport

The full native energy e is nonreal at every actual Xi copy: its absolute
imaginary part is the previously proved positive native residual floor.
The existing self-adjoint resolvent construction therefore supplies an actual
bounded operator `R_e=(A−e)^(-1)` with values in the original native domain,
exact inverse equation for every forcing, and bound

`||R_e f|| ≤ xiResidualFloor(q)^(-1) ||f||`.

Both R_e H and the original V now belong to that domain and solve the same
forced equation. Injectivity of the nonreal shifted operator proves `R_e H=V`.
This is the required identification of the original source with the response.

Let `K_q=(I−(2+mu)C)R_e`, a composition of actual bounded operators, with C the
already constructed continuous functional calculus of B and mu the full
transformed Xi target. Then the existing entire-domain source CV satisfies

`(T−mu)CV = G = K_q H`.

For the already constructed unit vector `U=CV/||CV||`, the exact residual is

`||(T−mu)U|| = ||C R_e H||^(-1) ||K_q H||`.

The denominator is positive by the original source's proved nonvanishing and
injectivity of C. No arbitrary response vector, scalar projection, or omitted
forcing term enters this identity. It is exact bounded operator transport;
a single scalar rational CFC representation is not asserted here.

## Lean modules and audit

All modules lie under `GaloisForLFunctions.RHTower` with matching short namespaces
under `RHTower`.

| Module | Public declarations | Sole-target final build |
| --- | ---: | ---: |
| SelbergScatteringSourceApproximation | 20 | 4.8s |
| SelbergScatteringSourceBounds | 10 | 4.8s |
| SelbergScatteringCutoffDerivatives | 7 | 3.7s |
| SelbergScatteringSourceGraph | 10 | 8.4s |
| SelbergScatteringForcingTransport | 11 | 6.4s |

Every complete scratch passed `lake env lean`. Each final `lake build MODULE`
compiled only its named module; every preflight and Built line was checked.
All 58 public axiom reports contain only the standard `propext`,
`Classical.choice`, and `Quot.sound` dependencies. All public declarations are
indexed, each umbrella import occurs once, and no new module has a lint error.
No numerical experiment, computed proof input, or proof placeholder was used.

Audit logs: `/tmp/sqb10_{approx,bounds,cutoff_deriv,graph,transport}_build.log`,
`/tmp/sqb10_{approx,aux,graph,transport}_axioms.log`, `/tmp/sqb10_index_audit.json`.
The final repository-wide lint invocation returned five unrelated missing
umbrella imports: `HTGeometry.FokasLenellsRawContourFifthTrace`,
`HTGeometry.FokasLenellsRawTwistEndpoints`,
`HTGeometry.FokasLenellsRawTwistKernels`,
`HTGeometry.FokasLenellsRawTwistPrimitives`,
`HTGeometry.FokasLenellsRawTwistScattering`.
Those other-task modules were left untouched. No new SQB module has a lint error.

## Remaining occurrence problem

The entire-domain vector is CV, where C is the actual continuous functional
calculus of B. Its exact residual is `G=V−(2+mu)CV`, with mu retaining the full
complex Xi parameter. The native graph bridge and exact bounded
forcing transport are closed. Proving zero-specific vanishing or a negligible
normalized transported forcing for a suitable full-source construction remains
an occurrence obligation. Nonzero H alone does not decide whether K_q H vanishes.
No RH endpoint is claimed.
