# Theta-cusp Hawking/QEI RH route (2026-08-22)

Canonical endpoint inventory: `docs/reports/endpoints.md`.

Selected RH-native endpoint: `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` / source Bezoutian / two-channel Weil parity. Reason: literal positive theta source exists; scalar and two-real-node sectors are unconditional; only complex multi-mode cross-horizon coherence remains.

New active card: `docs/drafts/pipeline/1-in-progress/theta-cusp-hawking-qei-parity-transport.md`.

Exact bridge formalized: `formal/GaloisForLFunctions/RHTower/ThetaCuspReflectedHawkingFlux.lean`. For reflected action q, entropy S=-(c/6)q and flux F_C=2C(q'^2-q'') satisfy Bianchi-Smerlak; F'_C=2C(2q'q''-q''')>=0 for C,t>=0 by global theta Riccati theorem. Targeted module and RHTower umbrella imports added; module build passes; #print axioms only propext/Classical.choice/Quot.sound.

Horizon source representation (paper derivation): source Bezoutian quadratic form is 4∫_{s>0,u,t∈R} u k(u)^2 exp(-q_u(t)) Re(f(u+t-s)conj f(u-t-s)); splitting u at 0 gives H_out-H_in. Exact active claim H_in<=H_out is equivalent to tilt-flux positivity and RH.

First open core `THETA-HORIZON-WELD`: source-explicit phase-sensitive renormalized Bogoliubov/modular map whose wedge energy equals this form, with passivity/QEI proved before Xi/divisor specialization. Abstract PSD factorization is circular.

Killed: positive prime-channel completion (divergent mass), fixed finite KMS/moments, fixed two-light (phase leakage), raw natural aperture (defect -> -∞), positive Stokes supercarrier (mass/moment excess). Gamma phase is mandatory; intensity alone insufficient.
