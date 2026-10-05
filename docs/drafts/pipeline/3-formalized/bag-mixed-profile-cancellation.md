# BAG exact signed mixed-profile cancellation

Continuation01aq; formalized in
`formal/GaloisForLFunctions/RHTower/ChiRamanujanMixedProfileCancellation.lean`.
The actual compact Euler deformation defines P, E and F=exp(P). The entire
continuation G=F*(E-1)*dslope(E,0,.) equals F*(1-E)^2/u away from zero,
vanishes at zero, and has absolutely integrable zero signed integral along
every positive vertical line. Main theorem:
`RHTower.BAGTrace.criticalMixedProfile_vertical_integral_zero`.

Proof: P'=E; (uF)'=exp(u)F; actual integral bounds and reflected exponential
half-plane primitive control bound uF on each left half-plane. Consequently
G has inverse-square decay. Rectangular contour shifting to -X and a
Lorentz integral bound pi*C/X pay the improper contour passage.
No extra analytic, prime-source or RH assumption.

Validation: foreground scratch58685 and production13632 empty PASS, using
`lake --old env lean ... -o ...olean`; axiom52462 PASS, all11 public
declarations depend only on propext/Classical.choice/Quot.sound. Wired once;
index21794 PASS, API11. Lint15411 has unrelated unreachable-module errors
and existing warnings, none in this leaf. No umbrella/full build, computation,
heartbeat change, added axiom, sorry, commit or push.

Paper: P2 bag-mixed-profile-cancellation. Active actual-source work:
P1 bag-mixed-frequency-mellin-cancellation. M1 identification of G with the
actual mixed-frequency growing labelled source remains open, as do uniform
physical remainder/tail control, full signed axes saving, growing moments,
and deterministic common-height self-return. RH goal remains ACTIVE.
