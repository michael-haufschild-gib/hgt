# Static local complexity master goal

- Goal: unconditionally prove Brown–Susskind growth–plateau–recurrence law for ordinary time-independent fixed-local Hamiltonians, plus permanent non-Haar locality witness.
- Master card: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.
- Exact headline: No-Shortcut Law for Autonomous Time; Choi/state circuit complexity grows as `~Theta(min{Lambda(H)|t|, 2^n})`, then density-one plateau and doubly exponential low-complexity recurrence; exceptions must be explicitly classified.
- O2 generic full spectral rank and O3 plateau geometry have substantial paper/Lean progress. O4 robust state no-shortcuts is central open core.
- Important no-go (2026-08-01): circuitwise restricted min-entropy cannot pay `s log M`. Identity circuit captures an `O(1/t)` coefficient tube around normalized one-Pauli recurrence centers, so `Q_short >= c^m (epsilon/(tm))^m`; `-log Q_short=O(m log t)`. Retired card: `docs/drafts/pipeline/5-failed/static-circuitwise-temporal-min-entropy.md`.
- Lean analytic core compiled in `formal/GaloisForLFunctions/HTGeometry/FiniteHorizonCStarPerturbationLaw.lean`: `selfAdjoint_near_periodicCenter_unitaryEvolution_norm_sub_one_le` and error-budget corollary.
- Surviving O4 target is aggregate shortcut-locus bound `(O4.3)`, roughly `P{C_epsilon(Phi_H(t)) <= a Lambda t/poly(n)} <= (A t m/epsilon)^(-c m)`, proved globally without circuit-by-circuit union. Power-law tail is optimal up to constants because recurrence tubes exist, and still suffices for exponential-time nets.
- Conceptual mechanism under test: noncommutative dynamical relations. Spectral relations are abelian shadow controlling recurrence; short local-gate word relations control growth; finite matrix capacity forces plateau. Terminology is not novelty; only an unconditional aggregate word-escape theorem counts.
- Do not fall back to publishing O2/O3 as universal law if O4 fails. Do not claim black-hole/SYK transfer without model proof.
- User explicitly forbids subagents for this work.
