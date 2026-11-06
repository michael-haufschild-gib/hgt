# Review-0611 §2.1 finite verification (A1–A9)

- **ID:** review-0611-finite-verification
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md)
- **Statement:** Each task A1–A9 gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A1 | in progress | `VerifiedHeightRungs/HadamardBudget/` |
| A2–A9 | open | |

## A1: the Hadamard budget replaces Turing's method

An off-line zero `ρ = ½+δ+iγ` and its reflection contribute `≥ 2/a` to the positive Hadamard sum
`Re ξ'/ξ(½+a+iγ)` for every `a > ½`, an on-line simple zero only `1/a`. So
`Re ξ'/ξ(½+a+it) < 2/a` on `t ≤ T` proves `RHVerifiedThrough T` with no zero computed at all.
Pairs of close zeros are the only obstruction: the first failure is at the pair near `t ≈ 295`.

Fejér smoothing in `t` replaces the Dirichlet series by a finite polynomial and keeps positivity:
with `Λ_L(u) = (1−|u|/L)₊`, `σ = ½+a`, an off-line zero at height `γ` forces

`2∫₀^L Λ_L(u) e^{−au} du ≤ Arch(γ) − Σ_{log n<L} Λ(n) n^{−σ} Λ_L(log n) cos(γ log n)`.

`Arch(γ) ≈ ½ log(γ/2π)`. The left side is `≈ 2/a` for large `L`. Numerics (uncertified):

| `a` | `L` | terms | first failure | margin at 100 |
|---|---|---|---|---|
| 0.6 | 5 | 47 | 150 | 0.33 |
| 0.6 | 6 | 98 | 185 | 0.47 |
| 0.55 | 8 | 465 | 295 | 0.74 |

Past `295`: subtract certified on-line zeros at the close pairs (`hardyZ` sign changes).

## Progress

- **A1:** `HadamardBudget/TheVerifiedHeightSixtySeven.lean`: `rhVerifiedThrough_sixtySeven`, by hand, no zero or value of `ζ` located. The worst-phase budget (Kronecker limit) cannot pass `T ≈ 80`. Past it, phase information is needed: that is a finite computation, excluded by the goal's rule.
- **A5:** `xi_centre_pfSeq_twoHundred` (`PF_200`), `xiSliceCoeff_nonneg_of_abs_le_band` (`|t| ≤ 133/2`), `re_xiLiPaired_nonneg_of_le` (`n ≤ 314`).
- **A4 (plan):** rank 10 from height 66. Cubic `D(N+1)³` is an artifact of factorial Hankel bounds. Replace by: parity reduces rank 10 to polynomials of degree `≤ 4` in `t = b²`; Legendre reproducing kernel on `t ∈ [1, 25]`; explicit tail `|current a b| ≤ C a e^{−(7/5)|b|}`; core floor on `1 ≤ |b| ≤ 5` from `poleSharpConstant` and `Ξ(b) ≥ Ξ(0) − (b²/2)∫Φx²`.
- **A8 (finding):** finite templates end at spread `27/5`, not `6`. Moves `q ↦ 81q/80` (`q < 16/15`), `q ↦ 15q/16` (`q ≥ 16/15`) stay in `[1, 27/25)`, are paths of ratio-2,3,5 edges inside `[1, 27/5)`, and lower `v₂` by 4 each. Stages accumulate at `27/5`, so stage-by-stage exact horizons cannot reach it.
