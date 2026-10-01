# Hermite–Biehler count for ξ + λξ′

- **ID:** XI-HERMITE-BIEHLER-COUNT
- **Stage:** 3-formalized
- **Type:** THEOREM (unconditional, exact count at unshadowed heights)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 78
- **STATUS:** MUST-605

## Theorems [L]

Module `formal/GaloisForLFunctions/RHTower/XiHermiteBiehlerCount.lean` (wired, clean, standard axioms).

- `exists_hermiteBiehler_count_right`. For `λ > 0` and unshadowed `T₁ < T₂`, `ξ + λξ'` and
  `ξ` have exactly the same number of zeros, with multiplicity, in `½ < Re s < 2`,
  `T₁ < Im s < T₂`.
- `xiHermiteBiehler_ne_zero_right_of_re_zeros`. RH ⇒ `ξ + λξ' ≠ 0` on `Re s > ½`, for every
  `λ > 0`.
- `exists_xi_right_edge`. For `λ > 0` and small `δ`, `Re(1 + λξ'/ξ) > 0` on `Re s = ½ + δ`.
  The proof peels the on-line zeros; `Re h'/h = 0` on the line; compactness gives the rest.

## Meaning

- `ξ(½+it) = Ξ(t)` is real and `ξ'` is purely imaginary on the line, so `ξ + λξ'` restricted to
  the line is `Ξ − iλΞ'`, the Hermite–Biehler partner of `Ξ`.
- Classically, all real zeros of `Ξ` ⇒ all zeros of `Ξ − iλΞ'` lie in one half-plane.
- The theorem is the unconditional count behind this: right zeros of `ξ + λξ'` = right (off-line)
  zeros of `ξ`, exactly, between unshadowed heights.
- For `λ < 0` the roles of the half-planes swap, via `V_λ(1−s) = V_{−λ}(s)`.
- The ratio has no sign on the left for `λ > 0`. That left region is where Levinson's method
  operates.

## Addendum (cycle 79): exact Laguerre–Pólya inequality on the right [L]

`R:XiDerivRightCountLe`, `sum_order_deriv_xi_right_le`: for unshadowed `T₁ < T₂`, the zero count of `ξ'` in `½ < Re s < 2`, `T₁ < Im s < T₂` is at most that of `ξ`.

The proof is Hurwitz through the Hermite–Biehler family:
- small disjoint squares around the right zeros of `ξ'`;
- on their boundaries `|ξ/ξ'| ≤ M`;
- for `λ = |M| + 1` each square holds exactly `ord(ξ', w)` zeros of `ξ + λξ'`;
- sum and apply MUST-605.

This sharpens MUST-604's "+ excess + 4" to an exact inequality on each side. By `ξ'(1−s) = −ξ'(s)` and conjugation the left side is symmetric.

## Addendum (cycle 80): Levinson's detector, exact right count [L] — MUST-607

Module: `R:LevinsonDetectorRightCount`.

**`exists_levinsonG_count_right`.** Hypotheses: `λ > 0`, `λ(½ log(T₂/2π) + 1/20) < 1`, and unshadowed heights `100 ≤ T₁ < T₂`. Then `ζ + λζ'` (the corpus `levinsonG`) and `ξ` have exactly the same number of zeros, with multiplicity, in `½ < Re s < 2`, `T₁ < Im s < T₂`.

**Mechanism.**
- `G/ζ = 1 − λA + λξ'/ξ`, where `A = archFactor'/archFactor`.
- `Re A ≤ ½ log(t/2π) + 1/20` on `0 < Re s ≤ 2`, `t ≥ 100`.
- Right-edge lemma in the ε-form `exists_xi_right_edge_re_logDeriv_gt`: `Re ξ'/ξ > −ε` on `½ + δ`.
- Winding of `(s−1)²G` against `(s−1)²ζ`, which has the same orders as `ξ` on the window.

**`levinsonG_ne_zero_right_of_re_zeros`.** RH ⇒ `ζ + λζ' ≠ 0` on `½ < Re s ≤ 2`, `100 ≤ Im s ≤ T`.

**Reading.**
- For `0 < λ < 2/log(T/2π)` (roughly; this is the corpus `levinsonY > 0` range), the right zeros of Levinson's detector are exactly the off-line zeros of `ζ`.
- On the line, `G` vanishes exactly at the multiple zeros of `ξ` (order `m − 1`).
- So the corpus window inequality, which counts zeros of `G♯` in `[½, 4] × [T₁, T₂]`, counts exactly `N_right(ζ) + Σ_on (m_ρ − 1)` at good windows, since `G ≠ 0` for `Re s ≥ 2`.
- Levinson's method in this `λ`-range is therefore literally a joint bound for the off-line count and the multiplicity defect. There is no other content.
- Spawned zeros from on-line zeros go LEFT, at `s − ρ₀ ≈ −λ/(1 − λA)`. Their Littlewood mass in `(σ₀, ½)` is the inefficiency of the method.

## Addendum (cycle 81): Speiser confinement [L]

**Lemmas** (in `R:LevinsonDetectorRightCount`):
- `exists_xi_zero_disk_of_xiHermiteBiehler_eq_zero`;
- `exists_xi_zero_disk_of_levinsonG_eq_zero`;
- helper `exists_xi_zero_disk_of_re_logDeriv_nonpos`.

**Statements.**
- Every zero of `ξ + λξ'` (`λ > 0`) with `Re s > ½` lies in the closed Speiser disk of a zero of `ξ`.
- The same holds for `ζ + λζ'` in the Levinson range, for `½ < Re s ≤ 2` and `100 ≤ Im s ≤ T`.

**Consequence.** With the exact counts, the right zeros of every partner live in the same Speiser clusters as the off-line zeros, in equal number per unshadowed window.

## Addendum (cycle 84): Levinson's budget counts off-line zeros and the multiplicity defect [L] — MUST-609

`R:LevinsonDetectorDefectCount`, `two_pi_mul_offLine_add_multiplicityDefect_le_levinsonBoundary`.

**Hypotheses.** `λ > 0` with `λ(½ log(T₂/2π)+1/20) < 1`; unshadowed `100 ≤ T₁ < T₂`; any entire mollifier `Ψ`; `σ₀ < ½`; `d ≥ 4`; the edge conditions of the corpus mass lemma.

**Conclusion.**
`2π(½ − σ₀)·(N_right(ξ) + Σ_on (m_ρ − 1)) ≤ weightedLittlewoodBoundary(G♯Ψ; σ₀, d, T₁, T₂)`.

**Ingredients.**
- MUST-607 (exact right count).
- New `toNat_analyticOrderAt_xi_le_levinsonGEntire_add_one`: `ord_ρ G♯ ≥ ord_ρ ξ − 1` at every zero with `Re ρ > 0`. The proof writes `G♯ = aξ + bξ'` locally and uses `ord ξ' + 1 = ord ξ`.

**Reading.** The corpus budget (`exists_levinson_mollified_budget_le`) turns the boundary functional into the mollified mean square. Any mollified mean-square bound for the Levinson detector in this `λ`-range is therefore a direct upper bound for the off-line count plus the multiplicity defect. Simple on-line zeros cost nothing. This is the precise zero-side content of Levinson's method. The mean-square evaluation (the common terminus) is the only missing input.

## Addendum (cycle 85): mean-square form of MUST-609 [L]

`exists_offLine_add_multiplicityDefect_le_of_mollified_meanSquare` (`R:LevinsonDetectorDefectCount`) gives, with the corpus budget constants `C, K`,

`2π(½−σ₀)(N_right(ξ) + Σ_on(m_ρ − 1)) ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)`.

It holds for every Levinson mollifier `Ψ = Σ_{n≤N} b_n n^{−s}` (with `b_1 = 1`, `|b_n| ≤ 1`, real coefficients) and every `Msq ≥ ∫|(ζ+λζ')Ψ(σ₀+it)|²`. The parameter range is `0 < λ`, `λ(½log(T₂/2π)+1/20) < 1`, unshadowed `100 ≤ T₁ < T₂`, `¼ ≤ σ₀ < ½`, plus the corpus's edge conditions.

This feeds the common terminus (the Conrey mean-square evaluation) directly into an off-line count bound, with no Hardy-θ edge terms. Helper: `two_le_log_div_two_pi`.
