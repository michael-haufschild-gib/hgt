# HB physical-Jost biorthogonal-normalization no-go (2026-09-02)

- Killed route class: `exact Birmingham–Mokhtari Gamma/Jost coefficient → canonical left-QNM dual response → reflected Peierls-current cancellation → RH`.
- For connection columns `v_R=(a_R,b_R)`, `v_C=(a_C,b_C)`, `D=a_R*b_C-a_C*b_R≠0`, canonical inverse rows satisfy `ell_R(c_R v_R+c_C v_C)=c_R` and `ell_C(...)=c_C`.
- Specializing `b_R` to the literal BM decaying Gamma/Jost coefficient: matching dual response loses all Gamma/Jost phase/modulus and cross response is zero. Nonzero global input remains a receiver for the existing wall/RH condition, not its producer.
- Scope: canonical biorthogonal, coefficient-linear extraction only. Survivor must place divisor-sensitive data in source-dependent horizon coordinates before normalization, or use nonlinear/cross-channel/renormalized pairing.
- Lean theorem: `d4HBPhysicalJostBiorthogonalNormalizationRouteKilled` in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhysicalJostBiorthogonalNormalizationNoGo.lean`.
- Card: `docs/drafts/pipeline/3-formalized/hb-physical-jost-biorthogonal-normalization-no-go.md`.
- Audit: direct Lean PASS; targeted build `11916/11916` PASS; only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Lint recognizes module; remaining lint failures are unrelated pre-existing unreachable modules.