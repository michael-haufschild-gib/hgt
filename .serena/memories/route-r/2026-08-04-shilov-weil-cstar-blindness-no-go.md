# Shilov–Weil C*-blindness no-go (2026-08-04)

Requested source-pure bifiltered operator-system contraction is false as stated.

Exact obstructions:
- Rational-adelic Stokes regulator satisfies `R_p d0=0` and `R_p(eta_p)=1`; any `dh+hd=1` on cocycle `eta_p` makes it a boundary and forces regulator zero.
- Physical cofinal class is source-null exactly on critical line; global contraction is RH-equivalent, not an independent producer.
- Gamma Bockstein coefficient `Delta_t` tends to zero for all `|t|<1`, so its diagonal is compact throughout strip; absolute summability/trace class holds iff `t=0`.
- Any closed C*-ideal absorbing finite-rank diagonal ambiguity absorbs all compact `D_t`. Local C*-seminorm topology on fixed `c0` also keeps `c00` dense. Hence Shilov/local-C* closure cannot retain the RH-bearing trace-class wall.

Strongest survivor: horizontal finite-prime restrictions are genuine complete-order quotients, but vertical direction must be a non-C* trace-filtered/bornological/Rees-corona fracture. Detector-preserving identity is `dh+hd=1-iota R`, not `1`.

Formal module: `formal/GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinCStarShilovBlindness.lean`; direct Lean and targeted build pass; axiom audit only propext/Classical.choice/Quot.sound. Wired into `RHTower.lean`. Global lint blocked only by unrelated concurrently-added unwired modules.

Cards:
- failed route: `docs/drafts/pipeline/5-failed/shilov-correlation-rh-proof-architecture.md`
- paper-proved survivor: `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/cofinal-gamma-cstar-shilov-blindness.md`

New Rees-corona model audit confirms receiver/producer separation: resolved harmonic lift is unconditionally admitted; physical lift admitted iff critical line; global physical admission iff RH. Missing theorem remains independent pre-divisor source-to-physical lift identification.