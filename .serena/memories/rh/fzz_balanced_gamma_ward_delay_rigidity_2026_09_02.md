# FZZ balanced Gamma Ward-delay rigidity (2026-09-02)

- Corpus source: `fzzHJBalancedExternalGammaPhaseSlope_zero_le` plus replica-area passivity endpoint.
- New strict margin: after Gauss atoms n=0,1 cancel rational arctan losses, n=2 contributes `8 y^2 / (5*(25+4*y^2)) > 0` for y != 0.
- Thus local momentum Ward delay `4*sqrt(2)*slope(sqrt(2)*P)` has unique global vacuum minimum.
- Lean: `fzzHJBalancedExternalGammaWardDelay_eq_vacuum_iff_passive`.
- Endpoint: `fzzBalancedExternalGammaWardDelayDivisorSaturated_iff_riemannHypothesis`.
- Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityExternalBRSTBalancedGammaWardDelayRigidity.lean`; umbrella wired.
- Verification: direct Lean PASS; targeted build 13153/13153 PASS; axioms only propext/Classical.choice/Quot.sound; lint has unrelated pre-existing unreachable modules.
- Remaining FZZ source edge: derive vacuum-delay saturation on literal parity-Mellin divisor modes from integrated replica Ward dynamics. No phase unwrapping/history is required.