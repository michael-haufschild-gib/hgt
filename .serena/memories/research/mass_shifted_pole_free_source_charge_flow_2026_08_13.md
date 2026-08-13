# Pole-free completed source-charge flow (2026-08-13)

Formal modules:
- formal/GaloisForLFunctions/RHTower/XiShiftedArcsineVacuumCompletedSourceCharge.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedArcsineVacuumCompletedSourceChargeFlow.lean

For degree n and mass y define the completed source charge
C_n(y) = 2 S_n(y) - 32 V_n N_{n+1}(y), with V_n = n + 3/8.
At square mass it is exactly adaptive mixed completed arithmetic amplitude minus the arcsine-vacuum newborn norm counterterm.

Define native density rho_n = A_n - K_n + 32 V_n Phi_{n+1}, where A is next completed arithmetic source, K is inverse-Hankel connection source, and Phi is division-free norm flux. Lean proves C_n' = -rho_n.

Fixed degree recession follows without computation: N_{n+1}(y) -> 0 and C_n(y) -> 0 as y -> infinity.

At every occupied strict frontier y=tau_{n+1}, degree d=n+1 has C_d(y)>0. Endpoint continuity plus recession and MVT yield b>y and c in (y,b) with rho_d(c)>0 and
(b-y) rho_d(c) = C_d(y)-C_d(b)>0.

This is source-first, admission-sensitive, bilinear, completed rational-Gamma/von-Mangoldt, before reflection/reporting. Wall poles are quotient artifacts.

Remaining exact core: prove these positive density events cannot escape to increasing degrees/disjoint masses under false RH. Likely obstruction is degree nonproperness/admission effectivity. Need cross-degree coercivity or finite common action budget.