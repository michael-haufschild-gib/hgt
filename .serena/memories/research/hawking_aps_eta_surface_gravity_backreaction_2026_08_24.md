# Hawking APS eta / surface-gravity backreaction boundary

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingAPSEtaBackreactionBoundary.lean` and added it to `RHTower.lean`.

Exact new result:
- For thermal-circle shift `a`, positive/negative heat traces are
  `sum exp(-t(n+a))` and `sum exp(-t(n+1-a))`.
- Their right heat limit is the circle APS eta value `eta(a)=1-2a`.
- For d=4 topological BH with `x=r_+/l`, dimensionless mass `m=x(x^2-1)` and surface gravity `kappa=(3x^2-1)/(2x)`; at massless point `x=1`, both derivatives equal 2.
- Fixed-frequency ingoing exponent mass jet is therefore `decay/2`.
- For reflected real-pair BM frequencies, mass-jet defect is `(1-2 Re rho)/2 = eta(Re rho)/2`, independent of overtone, and vanishes iff critical line.
- Global sector-local vanishing is RH-equivalent.
- Reflection-pair eta and mass-jet defect cancel unconditionally. Therefore global APS index/anomaly cancellation is RH-blind; producer must impose sector-local Calderon admission or physically mix reflected tilted sectors.

Hostile scope:
- Effective shifted thermal-circle operator is not yet identified with actual nonlinear Teukolsky Calderon boundary operator.
- Full moving-pole exponent derivative has covariant form `-(i/(2 kappa)) (omega_M - (kappa_M/kappa) omega)`; unknown pole velocity/boundary transgression can cancel geometric term.
- Next open core: derive actual relative Evans/Darboux boundary multiplier and prove its Green primitive is sector-local or necessarily inter-sector mixing.

Verification:
- Targeted compile passed.
- 17 public theorems axiom-audited: only `propext`, `Classical.choice`, `Quot.sound`.
- Scratch files deleted.
- Lint recognizes new module; only remaining lint error is pre-existing unreachable `HTGeometry.SecondOrderConstraintDescent`.
- No git used.