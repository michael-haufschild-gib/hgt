# BiScale WP6: node criticality and the blind-cone slack (100-contribution loop)

- **ID:** biscale-wp6-node-criticality-loop-2026-10-20
- **Stage:** 1-in-progress
- **Type:** research programme ledger
- **Statement:** exhibit a positivity argument that reads why `log 4` is indispensable and `log 6`
  redundant in the node set `{log n}`, and deliver the blind-cone slack the sign-changing gauges need
  (`docs/reports/work-packages.md`, WP6).
- **Significance criteria:** (1) a positivity statement that changes when `log 4` is deleted and not
  when `log 6` is, mechanism explicit; (2) exact slack of the blind cone on two multiplicatively
  independent integers, or the infimum of `𝒥/h(0)` on the blind polar class, as a constant used in
  WP1/WP3; (3) band energy at square-root precision beyond polynomial length equal to the height;
  (4) effective universal-probe criterion through finitely many primes.
- **Rules:** corpus search tool first; unconditional Lean, no RH hypotheses (equivalences/limits
  only); one foreground Lean process; `lake --old env lean` audits; wire into the umbrella, no
  umbrella builds; no numerical experiments; knowledge ledger `logs/biscale-wp6-node-criticality-facts.md`.

## Count: 2 / 100

## Ledger

| # | Contribution | Criterion | Module | Status |
|---|---|---|---|---|
| 1 | **Zero-pole node criticality: incidence, not density.** `ZeroPoleBlindPositiveOn 𝒩 ↔ RH ∧ PP ⊆ 𝒩` for every node set. Answers the README density-threshold question: the primes (density `e^X/X`) never suffice (prime squares missing, first `4`); deleting one prime power from any set fails unconditionally; deleting a non-prime-power (`6`) changes nothing; the pole constraint is invisible to node criticality (`↔ PrimeBlindPositiveOn 𝒩`). Mechanism: Farkas on node values in `𝒩` + pole coordinate → weight supported on `𝒩` Weil-positive at some pole weight → pole rigidity → cone uniqueness (`= Λ`). | 1 | `PrimePowerZeroPoleNodeCriticality` | Lean ✓, axioms standard, wired |
| 2 | **Exact deletion price `Λ(m)/√m`.** On combinations blind at every prime power except `m`: `A = W + Λ(m)L_m` and the tower Fejér bound `|L_m| ≤ ‖c‖²/√m` (powers `m^k`, `k ≥ 2`, are blind prime powers ⇒ one free phase coefficient ≤ half the mass); the exact range of `(A − W)/‖c‖²` is `[−Λ(m)/√m, Λ(m)/√m]`, both ends attained by narrow pairs `h ± h(·−log m)`. `log 4` costs `log 2/2`; composites cost `0` (`A = W` on the PP-blind cone). Criterion: RH ⟺ every deletion price is at most `Λ(m)/√m` in zero-pole slack. | 1 | `PrimePowerNodeDeletionPrice` | Lean ✓, axioms standard, wired |

## Conjecture log

- **C1 (proved).** Zero-pole positivity on a node set is decided by incidence. Searched: "node
  criticality log 4 log 6", "zero pole blind positive node set". Reused the Farkas template of
  `riemannHypothesis_iff_zeroPoleBlindPositive`, `logVectorOn`/`linearCombination_extendOn`,
  `eq_one_of_weilPositiveAt`, `eq_vonMangoldt_of_weilPositiveFull`.
- **C2 (proved).** Deletion price. Reused `two_mul_abs_cos_moment_le_of_cos_blind_off` (removal-law
  mechanism) with `q = m`, `d = 1`; narrow pair tests from `WeilFullConeOneSidedCriterion`.

## Log
- 2026-10-20 — created.
