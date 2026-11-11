# The native half-plane: tasks A118a–d

- **ID:** native-half-plane-a118
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), in parts
- **Source:** docs/reports/review-1111/obstacles-summary.md §2.1 "The native half-plane (given `[X]`)"
- **Statement:** make the two-estimate route to `Θ ≤ 7/8` native: corrections `H_η` (A118b),
  comparison with cube indices (A118a), uniform saving (A118c), direct bound (A118d).

## Goal
Each task closed by an unconditional Lean theorem in the native graph, built from corpus blocks.
The external source `[X]` (text `logs/review-2410-current-audit/quasi-rh-seven-eighths.txt`) is a
mathematical guide only; no external code enters the corpus.

## Frame defect (found 2026-11-11)
The family step of `FamilyContinuationTheory` runs on `heckePoleCleared = (s−1)L(s,η)`. For a
nonprincipal `η` this has the value `0` at `s = 1` (`heckeThetaPoleCoefficient = 0`). Hence
for `β < 1` the zero-free premise of `hstep` is false, and at `β = 1` the required estimates
would continue `exp·H/((s−1)L)` across its pole at `1`: the premise of
`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`,
`heckeHalfPlane_of_family_height_estimates`, `heckeHalfPlane_of_family_common_signal`,
`heckeLFunction_ne_zero_of_family_common_signal_all` is unsatisfiable as soon as `K` has a
nonprincipal ray class character. Fix: kernel `exp((s−c)²) H(s)/L(s,η)` (the source's form),
zero-free premise on `L` off `1`, and the family step with `E ≠ 0` required only at zeros of
`L` (principal character: `L_native = (s−1)L`, `E = exp·H·(s−1)`).

## Status
| Task | Content | Lean |
|---|---|---|
| frame | family step on the zeros of `L`; kernels `exp·H/L` | `FamilyContinuationTheory/TheFamilyStepReadsTheZerosOfTheLFunctions`: `heckeHalfPlane_of_family_reciprocal_signal`, `…_reciprocal_height_estimates`, `zetaZeroAbscissa_le_of_two_reciprocal_estimates`, `heckePoleCleared_one_of_ne_one` |
| A118b | `H_η = ∏_{P∉S} h_P` at `w = 1, z = 1/6`; `h = (1−q²)(1 − q(R−D)/(1−D))/(1−R)`, `q = N(P)⁻¹`, `D = η(P)N(P)^{−s}`, `R = A_P N(P)^{3−6s}`, `‖A_P‖, ‖η(P)‖ ≤ 1`; converges on `Re s > 2/3` | `FamilyContinuationTheory/TheCorrectionOfThePrincipalRowIsAConvergentEulerProduct`: `norm_principalLocalFactor_sub_one_le` (`‖h−1‖ ≤ 14 N^{−e}`, `e = min(6σ−3,1+σ,2)`), `exists_principalCorrection_cutoff` (`‖H−1‖ ≤ ½` on `Re s > σ`, any `σ > 2/3`), `exists_fullPrincipalCorrection_cutoff`, endpoint `exists_cutoff_zetaZeroAbscissa_le_of_two_estimates` (only premise: the two estimates). Phases arbitrary of modulus `≤ 1`; the actual phase `A_P = conj(α(π))⁶η(P)⁶` enters with A118a |
| A118a | Poisson in `m`, scalar Euler identity (source Lemma 7.1), principal row = signal | open |
| A118c | uniform saving | open |
| A118d | reflection of the theta row, quadratic/sextic large sieves, detector | open |

## Log
- 2026-11-11 — created; frame defect found; closed form of the principal local factor checked
  against the source (Lemma 7.1 at `u = 1`) and the external `continuedCorrection`.
