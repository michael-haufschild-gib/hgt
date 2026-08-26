# BM transfer collision rigidity (2026-08-26)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMTransferCollisionRigidity.lean`; imported by `RHTower.lean`.

Main theorem:
`d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff` proves actual Birmingham--Mokhtari reflected/conjugated second-harmonic boundary transfers collide iff `Re rho = 1/2`.

Consequences:
- `d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel_iff_re_eq_half`
- `d4BMXiFESchwarzHasDirectHelicityDarkKernel_iff_re_eq_half`

Core new argument: for `T(rho)=Gamma(-rho-1) Gamma(-1/2)/(Gamma(-(rho+4)/4) Gamma(-(3rho+2)/4))`, put `rho=1-4u`. Gauss 4/3 multiplication plus recurrence yields exact log slope
`log(256/27)+1/(u-5/4)+1/(u-5/12)+1/(u-1/12)-1/(u-1/2)+psi(u)+psi(u+1/2)-psi(u+7/12)-psi(u+11/12)`.
Its real part is positive on `0<Re u<1/4`, `|Im u|>13/8`; hence squared transfer modulus is strictly horizontally increasing. Low Xi heights are discharged by unconditional `RHVerifiedThrough (243/20)`; high heights lie in the monotonicity range.

Verification:
- targeted source compile passed with no warnings
- all 33 new declarations axiom-audited: only `propext`, `Classical.choice`, `Quot.sound`
- global lint still fails only on unrelated pre-existing umbrella-unreachable modules; new module is reachable
- no docs/route ledgers/git touched
- scratch files deleted

Remaining hard producer: prove nonlinear horizon dynamics forces occurrence/vanishing condition selecting folded dark kernel. Transfer collisions themselves can no longer occur accidentally off critical line.