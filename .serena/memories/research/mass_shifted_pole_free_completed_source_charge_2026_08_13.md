# Pole-free arcsine-vacuum completed source charge (2026-08-13)

## New formal object

Module: `formal/GaloisForLFunctions/RHTower/XiShiftedArcsineVacuumCompletedSourceCharge.lean`.

Let `V_n=n+3/8`, `S_n(y)` be current canonical adaptive shear, and `N_(n+1)(y)` current newborn admitted norm. Define

`C_n(y)=2*S_n(y)-32*V_n*N_(n+1)(y)`.

At square mass:

`C_n(w^2)=xiShiftedAdaptiveMixedCompletedArithmeticSource w P_(n,w)-32*V_n*N_(n+1)(w^2)`.

This is source-first admission-sensitive completed rational-Gamma/von-Mangoldt formation, before reflection/degree reporting.

## Normalized Jacobi law

`J_n(s)=E_n(s)-16*V_n*beta_(n+1)(s)`.

It is current Christoffel scale times centered wall away from newborn zero; zero on every coordinate-dilated arcsine tower; fixed-degree shifted-Xi limit is zero.

Adjacent innovation:

`I_n=J_(n+1)-J_n`

`=(alpha_(n+1)-alpha_n)*sum_(j<n) alpha_j + alpha_n*alpha_(n+1) - n*alpha_n^2 +(n+2)*alpha_(n+1)^2 +(1-n)*beta_n +(16n+7)*beta_(n+1) -(15n+20)*beta_(n+2)`.

Finite transport telescopes without weights:

`J_(n+k)=J_n+sum_(j<k) I_(n+j)`.

Newest edge has negative coefficient, so full centered source is intrinsically signed; positive-action/positive-trace route fails.

## Strict frontier

At every occupied strict frontier `y=tau_(n+1)`, `N_(n+2)(y)=0` and `S_(n+1)(y)>0`, hence

`C_(n+1)(y)=2*S_(n+1)(y)>0`.

Charge is continuous and positive on a right germ. Divergent Christoffel wall is posterior quotient `C/(32N)`, so pole is reporter artifact, not source singularity.

## Verification

- direct `lake env lean` passed
- targeted module build passed
- umbrella `RHTower.lean` wired
- 8 axiom audits: only `propext`, `Classical.choice`, `Quot.sound`
- no forbidden declarations; diff check clean

Stage3 card: `docs/drafts/pipeline/3-formalized/mass-shifted-arcsine-vacuum-completed-source-charge.md`.
Report: equations 9.3.725--728.

## Exact residual

RH not proved. Remaining core: along false-RH cofinal strict-frontier schedule, prove cumulative mixed mass-degree innovations cannot sustain infinitely many positive boundary charges while normalized fixed-degree charges tend to zero. Fixed-mass admission transgression is exact endpoint cocycle and has zero curvature; needed estimate must couple mass evolution to degree renewal.