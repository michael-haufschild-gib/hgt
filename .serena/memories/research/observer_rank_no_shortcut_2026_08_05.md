# Observer-rank no-shortcut frontier (2026-08-05)

Master: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`, O4.

- Killed `autonomous-shortcut-free-energy-law.md` as an exact conjecture: certified-format/compiler/overlap/pre-capacity/o(m) data underdefined; broad class circular, narrow class nonuniversal; raw circuit entropy not fixed polynomial component entropy.
- Replacement active card: `docs/drafts/pipeline/1-in-progress/observer-rank-autonomous-no-shortcut-law.md`.
- Exact conjecture for full fixed-q>=2 Gaussian Pauli ensemble/product input: aggregate Hamiltonian-dependent shortcut probability has logarithmic time exponent `v_(n,q)=2 sum_(k<=q) binom(n,k)`, the projective QFI rank, with slack eta and lower threshold `t>=n^(C_eta)`. Only selector-aware upper bound is open.
- Matching forced lower side paper-proved via stationary kernel and v-dimensional Gaussian ball. Hostile audit fixed quantifier: small-ball factor `v^(-v/2)` forces `C_eta` dependence. Gaussian lower law works even for zero kernel via near-zero coefficients; only annular tube law needs v<m.
- Stage-2 theorem: `docs/drafts/pipeline/2-fully-proven/observer-visible-local-time-dimension-obstruction.md`.
- Lean module created/wired: `formal/GaloisForLFunctions/HTGeometry/ObserverVisibleLocalTimeDimension.lean`.
- Lean-proved exact surface: realification Gram formula, QFI = 4 A^T A, QFI rank = observer-action real rank, realification kernel = centered coefficient action kernel = assembled-Hamiltonian eigenvector condition. Stage-3 card: `docs/drafts/pipeline/3-formalized/observer-visible-qfi-rank-identity.md`.
- Verification: `lake env lean` file passes; `lake build GaloisForLFunctions.HTGeometry.ObserverVisibleLocalTimeDimension` passes; axioms only propext/Classical.choice/Quot.sound. Repository-wide `scripts/formal_tools.py lint` passes after the unrelated umbrella owner repaired `KleinGordonSwitchedClock`.
- Full Gaussian tube, product q-local rank count, and complexity escape theorem not yet Lean-proved. Never promote full Stage-2 card to Stage 3 yet.
- No Lean/lake processes left running.