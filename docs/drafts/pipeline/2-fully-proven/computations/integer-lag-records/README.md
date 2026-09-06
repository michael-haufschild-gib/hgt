# Integer lag records, `n ≤ 2·10^7`

Script `integer_lag_records.py` (runpod, 18 s): sieves `Λ(n)`, forms `ψ(n)`, `M(n) = Σ_{m≤n}Λ(m)/m`,
`S(n) = Σ_{k≥1} n^{−2k}/(2k(2k+1))`, and the integer lags
`a_n = [(n − ψ(n)) + n(M(n) − log n + γ) − log 2π + S(n)]/√n` (Lean `RHTower.integerLag_eq`).
Output `integer_lag_records_2e7.json`.

| quantity | value |
|---|---|
| ceiling `a_1 = 2+γ−log 4π` | 0.046191 |
| `max_{2≤n≤2·10^7} a_n` | 0.018674 at `n = 3100` (40 % of the ceiling) |
| `min_{2≤n≤2·10^7} a_n` | −0.022681 at `n = 319439` (49 % of the ceiling in absolute value) |
| `#{n : a_n > a_1}` | 0 (as RH requires: Lean `riemannHypothesis_iff_integerLag_le_one`) |
| `#{n : a_n ≥ 0.9 a_1}` | 0 |

Reading. The Lean theorem `exists_pow_integerLag_gt_of_riemannHypothesis` says the records approach the
ceiling along every geometric progression under RH, but the first return within `ε` is only guaranteed by
time `Q^{|F|}` with `Q ≈ 8π²a_1/ε` and `|F|` the number of zeros carrying all but `ε/4` of the weight
`Σ_ρ (¼+γ²)^{−1}`: the records are at 40 % of the ceiling by `2·10^7` and climb slowly (record sites
`6, 15, 34, 205–208, 3084–3100`). The powers of two oscillate in sign with `|a_{2^m}| ≤ 0.0173`.
No numerical statement here is used in any Lean proof.
