# Certified pinning v2: combined cubic + order-8 spline tests (2026-10-03)

## Theorem (computer-assisted, Arb at 400 bits)
Let `λ : ℕ_{≥2} → ℝ` have Weil form ≥ 0 (ζ's archimedean datum, pole weight 1, conductor 1; the same functional as `certified-producer-pinning.md`) on both the cubic (P = 4, m = 37) and the order-8 (P = 8, m = 33) B-spline spans over [−1, 1] (spacing 0.05, L = 2). Then `δ_n = λ(n) − Λ(n)` lies in:

| n | certified δ_n |
|---|---|
| 2 | [−2.1330e-15, 1.7415e-16] |
| 3 | [−5.5437e-14, 2.1052e-13] |
| 4 | [−4.8332e-11, 2.4067e-11] |
| 5 | [−2.2222e-8, 3.2930e-8] |
| 6 | [−1.8032e-4, 1.3115e-4] |
| 7 | [−2.2723, 2.8534] |

This improves the v1 certified box (cubic only, L = 2: n = 2 [−2.43e-9, 4.2e-10]) by 5–6 orders at n = 2, 3. It applies to every full-cone Weil-positive weight system, in particular to every real-rooted twin `Λ_F/k`: `|Λ_F(2) − 3 log 2| ≤ 6.4e-15` for F ∈ V₃. Integer-coefficient twins must have f₂..f₆ = d₃(n).

## Method
- **`certcomb_make.py`.**
  - Build both families in mpmath (80 digits): Gram, pole, archimedean (x-space digamma formula), and lag matrices.
  - Whiten by Q_Λ's eigenbasis. For each target n0 ∈ 2..7 and each sign, run a high-precision flint log-barrier on the block-diagonal LMI.
  - Take the central-path duals `X_b = M_b^{-1}/t`, map them to spline coordinates, and split into rank-1 parts (weights ≥ 0, 70-digit vectors). Each part is exactly PSD, so each certificate is a valid inequality.
- **`certcomb_verify.py`.**
  - Rebuild every matrix in Arb: order-2P cardinal B-spline pieces; archimedean term by piecewise `acb.integral` plus a closed-form tail and a head bound; radius ≈ 2e-39.
  - Evaluate each certificate inequality `Σ_n δ_n m_n ≤ q` rigorously.
  - Combine with double-precision LP multipliers (row and column scaled, slack on the non-target rows), rounded to rationals and re-evaluated in Arb.
  - Run the rigorous bootstrap (`M ≤ |Q|/(|C_{n0}| − Σ|C_n|)`) and per-coordinate refinement.
- Results are in `certs_L2.json` and `certverify` output (pod). Values match the barrier optimum (n = 2: 2.133e-15).

## Caveats
The theorem concerns the stated finite test spaces (a relaxation of full-cone positivity, so valid for every producer). Correctness rests on the code and on the convention audit of v1 (`gammaBracket` = Re ψ(¼+ir/2) − log π). Not yet formalized in Lean.
