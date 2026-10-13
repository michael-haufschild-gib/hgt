# Almost-periodic locks with weighted rational part force RH

- **ID:** almost-periodic-lock-closure
- **Stage:** 3-formalized
- **Type:** CONJECTURE (C1153), Lean programme
- **Source:** Opus loop row 1153; builds on MUST-1387 (`apLock_coefficients`) and MUST-1388 (`rationalLock_riemannHypothesis`)
- **Statement:** a Herglotz producer with lower-line lock `G(1−s) = (Σ_j c_j u_j^{−(s−½)})G(s)` forces RH under two conditions:
  - the `u_j > 0` are arbitrary reals with `Σ_j|c_j|max(1,u_j^{−1}) < ∞`;
  - on the rational `u_j`, `Σ|c_j|max(1,u_j^{−1})√den(u_j)8^{ω(den u_j)} < ∞`.

## Key lemma (irrational points carry no weight)
For irrational `y > 0`, `𝒫(y) = Σ_{n u_j = y} a(n)c_j√u_j = 0`.
- M1 gives `|a(n)| ≤ W₀`.
- The period law gives `𝒫(y+k) = 𝒫(y)`.
- An irrational `u_j` meets the orbit `y+ℤ` at most once: `(n−n')u_j ∈ ℤ` with `n ≠ n'` would make `u_j` rational. Rational `u_j` never meet it.
- So `|𝒫(y)| ≤ W₀√(y+k)·S_k`, where `S_k = Σ_{n u_j = y+k}|c_j|` and `Σ_k S_k ≤ Σ_j|c_j|`.
- Hence `Σ_k |𝒫(y)|/√(y+k) < ∞`, which forces `𝒫(y) = 0`.

## Gates
- [x] 0 → 1 paper proof above (row 1153)
- [x] 2 → 3 Lean: `RHTower.AbelianTwist.almostPeriodicLock_riemannHypothesis` (MUST-1391), module `RHTower/WeilAlmostPeriodicLockRH`; standard axioms

## Log
- 2026-10-13 — created.
- 2026-10-13 — formalized (MUST-1391). The key lemma is `lockPer_eq_zero_of_irrational`, with orbit injectivity in `lockPoint_orbit_inj`. Remaining U room: non-almost-periodic locks, and rational weights below `√den`.
