# The twin defect is a successor-disagreement shell

- **ID:** ssh-twin-disagreement-shells
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Let `ω` be completely multiplicative with `ω(n) = ±1` for `n > 0`, and `g` a
  continuous bump supported in `[0, w]`. Then
  `Σ_k ω(k)Λ_w(k)·lag_k(x) − Σ_k Λ_w(k)·lag_k(ωx) = Σ_{0<|h|≤H} twinSh_h(x)`, where
  `twinSh_h(x) = 2Σ_k ω(k)Λ_w(k) Σ_{n = km + h} (1 − ω(km)ω(n)) x_m x_n β(log k − log(n/m))`.
  A shift on which `ω(ℓ)ω(ℓ + h) = 1` for all relevant `ℓ` contributes nothing; with no shifts the
  twin's prime form equals `ζ`'s prime form of the gauged vector.

## Paper proof

The gauge defect identity weights every lag term by `ω(k) − ω(m)ω(n)` (corpus,
`twistedPrimeSum_sub_primeSum_gauge_eq_of_supp`); this factor is symmetric in `(m, n)`, so the two
orientations combine into `2Σ_{n≠km}`. Since `ω(k)² = 1` and `ω(km) = ω(k)ω(m)`,
`ω(k) − ω(m)ω(n) = ω(k)(1 − ω(km)ω(n))`. The shell decomposition of each prime power (shift bound
`|n − km| ≤ n(e^w − 1)`) and finiteness in `k` give the sum over shifts.

## Scope

`1 − ω(ℓ)ω(ℓ + h) ∈ {0, 2}` is twice the disagreement indicator of the successor sign at shift `h`:
the object of Signed Successor Arithmetic. A selective inequality separating `ζ` from a twin must
read the shells through these successor signs.

## Lean proof

`SuccessorShellArithmetic/TheTwinDefectIsASuccessorDisagreementShell.lean`:

- `gaugeFactor_eq_successor`
- `twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm`
- `twinShellForm_eq_zero_of_agree`
- `twistedPrimeSum_eq_of_shellRange_eq_zero`

`lake --old env lean` passes; axioms `propext`, `Classical.choice`, `Quot.sound`.
