# Littlewood stage (R): transfer mechanism acquired — Ford's detector (2026-08-05)

Doc: `docs/drafts/pipeline/1-in-progress/littlewood-l2-weyl-chain.md`, section (R).
Source: Ford, "Zero-free regions for the Riemann zeta function", arXiv:1910.08205v5 (2025
corrections); full text extracted (session scratchpad `zfr_paper.txt`).

**The engine (resolves the scale paradox that blocked memory reconstruction twice):** Ford
Lemma 2.2 / 4.1 — the vertical-line zero detector:
`−Re ζ'/ζ(s) ≤ −(cot sum over zeros in the window) + (1/2η)·log(growth at σ−η) − (1/4η)∫log|ζ(σ+η+·)|·cosh⁻²`.
The growth bound enters ONLY through its logarithm over the window η — never growth/width.
With Richert's `t^{B(1−σ)^{3/2}}` input this gives κ = 2/3 (his Thm 1); the region tier is
exactly the growth-exponent SHAPE.

**Our input:** the certified Weyl chain gives the rectangle bound
`ζ(σ+it) ≤ A·t^{φ(1−σ)}·polylog` with `φ(δ) ≈ δ/(2·log₂(c₀/δ))` — the k-schedule
`k ≈ log₂(1/δ)` puts `log(1/δ)` in the denominator. Ford's balance with this φ:
remainder ≈ `B'·log t/log(1/δ) + c·loglog t/δ` at window η ≍ δ; contradiction at scale 1/δ
closes for `δ ≤ log(1/δ)/(c₁ log t)` ⟹ **δ* ≈ c·loglog t/log t — Littlewood**.

Formalization notes: Ford's two-line detector is for sharp constants; any c > 0 suffices for
us, so the simpler circle detector (Heath-Brown Lemma 3.2 shape) is admissible; audit the
PNTPlus pipeline's own detector first — L6 may reuse it with the φ-input swapped.

**Next block:** the (R) numeric gate — implement the detector inequality end-to-end with the
certified φ and crude constants, verify a positive region constant. Then L3 (Lean
Kuzmin–Landau) begins.
