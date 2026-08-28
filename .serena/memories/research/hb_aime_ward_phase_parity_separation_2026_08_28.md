# HC44 HB AIME/Ward phase-parity separation (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEWardPhaseParitySeparation`.
Card: `docs/drafts/pipeline/3-formalized/hb-aime-ward-phase-parity-separation.md`.

Corpus-led result: actual fundamental AIME numerator is cubic/odd under seed half-turn, while actual BM mixed-horizon optical Ward projection is quadratic/even. For `R_c(A,q)=AIME(A,xi(q))+c*BM(A,0,q)`, exact two-phase tomography gives half-sum `c*BM` and half-difference `AIME`. Nonzero seed makes simultaneous cancellation at `A` and `-A` impossible for every fixed quadratic normalization. If one phase cancels, opposite phase is exactly `-2*AIME` and nonzero. Calibrated even sample equals Deninger charge; its zero locus is `Re=1/2`; universal canonical even cancellation iff RH. Thus viable same-pole HB/AIME cancellation must contain genuinely cubic `++-` contribution.

Audit: direct `lake env lean` passed; target-only build passed 12,005 jobs; all ten public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; wired into RHTower umbrella; global lint has no HC44 error and remains red only on unrelated pre-existing unreachable modules. Bounded primary-source search found no exact match. Frontier map remained untouched.