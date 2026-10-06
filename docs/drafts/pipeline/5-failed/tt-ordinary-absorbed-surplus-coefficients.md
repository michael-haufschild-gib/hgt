# TT — Ordinary absorbed-surplus coefficient certificate

- Stage: failed certificate; obstruction and positive survivor formalized.
- Route: TT, full nonlinear-cone third-slope source sign.
- Parent: `../1-in-progress/tt-surplus-even-coefficient-orientation.md`.
- Scope: ordinary nonnegative coefficients after eighth-to-seventh absorption.
  Full source positivity, Route TT and RH are not falsified.

## Exact killing theorem

Let Q_x(E) be the COMPLETE reduced third-slope polynomial after quadratic
reduction at the actual source coordinates (u(x)^2,k(x),J(x)/u(x)). It uses
Z²=(k-1-k(6k-7)(9-v)/72)/9+(2-k)Z/3-E/9, and reads the remainder at z.
For every complex mass M define

    Absorb(Q,M)=Q-Q.coeff(8)*E^8+Q.coeff(8)*M*E^7.

Unconditionally, for all sufficiently large actual x, EVERY M has
Re([E^6]Absorb(Q_x,M))<0. Therefore no real polynomial with all coefficients
nonnegative maps to that absorbed polynomial. This excludes the proposed
certificate even on the actual orbit, without asserting a negative source
VALUE.

Dependency-closed proof: universal quadratic reduction over the original
source polynomial ring makes Q6 a fixed polynomial observable. The complete
source homogenization and quadratic-generator rescaling give
G_z(h,e)=h^22 Q_k,z(e/h²), k=(1/h-1)/3, retaining every term. Variable swap
makes [e6]G polynomial in h, with constant coefficient
-(8192/3)*189994*12^18. Original-coordinate all-order flatness transfers this
limit from (9,k,1/3) to the actual source. With h(x)=(3k(x)+1)^(-1)>0,

    h(x)^10*Q6(actual(x)) -> -(8192/3)*189994*12^18.

Eventual negativity follows. Absorption never changes coefficient6.

Lean: `ThetaCuspRatioTerminalActualCoefficient`, especially
`actualAbsorbedSurplus_no_nonnegative_representation` and
`sixthSourceCoefficient_actual_normalized_tendsto`.

## Strongest positive survivor

The SAME absorption retains a positive principal VALUE on the entire
admissible interval, including the double-root endpoint. Put t=36e,
D=1-t and d_j=choose(15,2j+1)*7^(14-2j)+choose(15,2j)*7^(15-2j).
The principal reduced polynomial is a positive constant A times
p(t)=t*sum_(j=0..7)d_j D^j, with A=73728*12^18/(36*6^15).
Its top coefficient is -d7. Exact identity:

    Absorb(p,1)=t*(d0+(d1-d7)*D+sum_(j=2..7)d_j*D^j
                    +d7*D²*sum_(i=0..5)t^i).

It follows from 1-t^6=D*sum_(i=0..5)t^i. All displayed terms are
nonnegative on 0<t<=1, and d0>0; also d1>=d7. Rescaling proves
Absorb(principalReducedSurplusPolynomial,1/36)>0 on 0<e<=1/36,
while its sixth ordinary coefficient remains strictly negative.

This is the exact h=0 fiber of the COMPLETE graded absorbed family.
Its mass is (1-h)^2/36, since h²*9*(boundaryA(9,k)+boundaryB(k)^2/4)
equals (1-h)^2/36 for k=(1/h-1)/3. No discriminant inverse or
truncation of the source was used. The COMPLETE finite-clock absorbed
polynomial satisfies G_abs(h,e)=h^22*Absorb(Q_k,z,M_k)(e/h²), with
M_k=9*(a+b²/4), proved in TerminalAbsorbedTransport:
`complete_terminal_absorbed_source`. Thus the survivor belongs to exactly
the same construction before and after scaling.

Lean: `ThetaCuspRatioTerminalAbsorbedPrincipal`, especially
`absorbedDeficitShape_split`, `principalAbsorbedSurplus_pos`,
`gradedAbsorbedPrincipal_eq`, `gradedAbsorbedPrincipal_pos`,
`gradedAbsorbedPrincipal_coeff_six`, `terminalAbsorptionMass`.

## New insight and remaining hard target

Ordinary coefficient positivity fails despite positive values of the exact
absorbed principal source. Surplus and deficit must remain coupled in any
replacement certificate. Neither positivity of that principal fiber nor
the existing seam/tail signs proves the complete finite-clock interior
value. The remaining sign must retain all lower source terms and the speed
constraint; subsequent full source quadratic, fourth gap, join/all rank
and RH remain open.

## Validation

2026-10-06: all31 terminal production leaves passed direct serial
`lake --old env lean -o ... <module>` audits, wired into RHTower without
an umbrella/full build. The first52 imported capstones passed in
`/tmp/tt_terminal_graded_production_axioms.lean`; every axiom set is a subset
of propext, Classical.choice, Quot.sound. Four further imported transport
capstones passed in `/tmp/tt_terminal_absorbed_transport_production_axioms.lean`,
also standard3. Statements checked for accidental
source/sign parameters. Thirteen superseded scratch sources/caches cleaned;
logs retained. No raised limits, sampling, external coefficient calculation,
added axiom or source-sign premise. Latest global lint exits1 from four
unrelated umbrella omissions, not a globally passing gate.
