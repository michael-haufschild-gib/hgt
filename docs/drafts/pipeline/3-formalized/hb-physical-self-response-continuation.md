# HB: complete physical response continued to its own fundamental resonances

Status: formalized. RH remains unproved.

For every actual Xi copy, the original complete physical response with
that same source and target has a meromorphic continuation to both of its
fundamental QNM frequencies. The construction agrees with the original
Hilbert response and complete-source endpoint Green integral on the
original overlap. No angular noncollision or continuation assumption is
supplied. A nonzero principal part and the physical adjoint residue remain
open.

## Exact finite source reduction

Fix original source and target copies q,r. Put

```text
lambda = -(1/4 + physicalRadialFrequency(r)^2)
lambda_i = m_i (m_i-1),      m_i = [2 rho_q, 1, 2-2 rho_q]_i
delta_i = lambda_i-lambda,  D = product_i delta_i
E_i = product_(j != i) delta_j.
```

Let M be the original reduced radial coefficient, A the actual residual
angular period, C_i the three actual cutoff periods, and V_i the continued
original principal responses with amplitudes A_i. The complete projected
source is exactly

```text
F = M A + sum_i h V_i C_i,       h(t)=sech(t)^2.
```

Construct U(J) at the independent target angular frequency from the
existing native Green response with source coefficients
`J` and `(lambda/2-(s+1)(s+2))*J`, then subtract the original radial lift
times J. Its actual equation is `L_lambda U(J)=M J`, where
`L_lambda=w^2-d^2/dt^2-lambda h`. Its continuation is the same native
continued response minus the same continued lift. Original endpoint and
spatial bounds hold on the physical overlap.

The original principal equations give

```text
L_lambda V_i = M A_i + delta_i h V_i.
```

Define the finite assembly

```text
R = D U(A) + sum_i E_i C_i [V_i-U(A_i)].
```

The cofactor identity `E_i delta_i=D` is valid even at zero gaps.
Applying the actual radial operator gives `L_lambda R=D F`, with every
source coefficient retained. Both D P and R are bounded, have the
original zero outer trace, and have actual classical jets. Their
homogeneous difference has a bounded second derivative because its
potential and value are bounded. A backward unit-interval estimate bounds
its first derivative. Original mode/Wronskian uniqueness then proves

```text
D P = R
```

for every source-target pair on `3/2<Re(w)<2`, `Im(w)!=0`.
This identity supplies no recovery of P when D=0.

## Same-copy noncollision is derived

When r=q and rho is the original Xi zero, the actual physical eigenvalue
is `rho(rho-2)/4`. The three exact differences factor as

```text
delta_0 = 3 rho (5 rho-2)/4
delta_1 = rho (2-rho)/4
delta_2 = (3 rho-2)(5 rho-4)/4.
```

Every factor can vanish only at a real rho. The corpus's unconditional
`xi_divisor_support_im_ne_zero` therefore proves all three gaps, and D,
nonzero for every actual Xi copy. This uses no critical-line premise.

`continuedPhysicalSelfResponse=R/D` is consequently the actual same-copy
physical response on the overlap. Each U(J) and V_i is meromorphic for
`Re(w)>-2`, `Im(w)!=0`; finite assembly and the proved nonzero constant
denominator give the same meromorphic continuation for R/D. The existing
Xi-strip theorem puts both original fundamental QNMs in this band.

The capstones are `physicalCuspResponse_ae_continuedPhysicalSelfResponse`,
`completePhysicalGreenProfile_self_eq_continued`, and
`allXi_fundamental_physicalSelfResponse_meromorphic`.

## Scope

Meromorphy is proved at each fixed original interior radial point t<0.
Equality with the original Hilbert class is proved on the initial
overlap. No radial-L2-valued response continuation or operator-valued
continuation is asserted at the QNMs. The source and target coincide in
the recovered response; the cleared identity retains arbitrary pairs,
including their possible angular collisions.

A nonzero residue is not implied by meromorphy or by a nonzero auxiliary
gap product. Evaluation at a totalized pole is not a Laurent coefficient.
The physical adjoint residue, its complete source coefficient, pole
survival, spin-two/AIME reconstruction, and independently proved extinction
remain open. Cross-copy recovery at a zero angular gap requires a
confluent construction or another exact argument.

## Lean surface

Ten RHTower leaves, prefixed `ThetaCuspHawkingBM`:

- `ReducedGreenResponse`
- `ReducedGreenContinuation`
- `ReducedGreenBounds`
- `BoundedRadialUniqueness`
- `PhysicalResolventAssembly`
- `PhysicalSelfAngularGaps`
- `PhysicalResolventEquation`
- `PhysicalResolventBounds`
- `PhysicalResolventIdentification`
- `PhysicalSelfResponseContinuation`

The leaves contain 29 public theorems and 15 definitions in 583 lines.

Each passed `lake env lean <scratch-file>` and an individual final
`lake build <exact-module>` in an isolated cache-backed audit project.
All ten final builds were warning-free. A scratch-only axiom audit of
the 44 new public declarations reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. No added axiom or computational
certificate is used. All 30 installed source/olean/ilean artifacts
matched the audited artifacts by SHA-256. Ten unique umbrella imports
are wired; no umbrella or full build was run.

The index refresh and `scripts/formal_tools.py lint --check-generated`
passed, retaining 141 existing large-file warnings. The largest new leaf
has 72 lines. The frontier map's SHA-256 is unchanged.
