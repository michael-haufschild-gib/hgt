# HB finite physical-clock-step covariance rigidity (2026-08-30)

Formalized `ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity.lean` and Stage-3 card `hb-finite-physical-clock-step-covariance-rigidity.md`.

Result: for centered BM physical evolution `U_t = exp(-i t H)` and literal anti-linear source-FE packet transport `T`, fibrewise unit-packet commutation is exactly `t = 0 ∨ Re(q)=1/2`. Globally, `T U_t = U_t T` on all finite Xi packets iff `t=0 ∨ RH`; for every fixed `t ≠ 0` it is iff RH. Closed theorem at `n=0,t=1`: `hbXiPeierlsUnitSourceFEUnitPhysicalClockStepCovariant_iff_rh`.

Mechanism: anti-linearity makes exponent discrepancy real: norms compare `exp(t Im λ)` and `exp(-t Im λ)`, and `Im λ=(1/2-Re q)/2`; real-exp injectivity removes every finite-time alias. This kills finite-clock sampling as an easier HB route and leaves strongest survivor: derive one finite source-predeclared nonzero physical-time FE/Schwarz covariance identity from literal Einstein–Teukolsky dynamics. No infinitesimal/all-time identity or small-time bound is required.

Conjecture loop: two-sided passivity failed because corpus already constructs positive antiunitary geometry with bright off-line cancellation; infinitesimal clock covariance was already an RH receiver. Finite physical time survived.

Audits: direct `lake env lean` PASS; targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity` PASS; theorem axioms only `propext`, `Classical.choice`, `Quot.sound`; module imported by RHTower umbrella. Global lint remains red only for unrelated pre-existing unreachable `HTGeometry.RatFuncChainRule` and `HTGeometry.RittTreeChannelMap`. Frontier map was not edited.