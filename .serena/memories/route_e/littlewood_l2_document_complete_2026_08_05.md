# Littlewood L2 document complete (2026-08-05)

`docs/drafts/pipeline/1-in-progress/littlewood-l2-weyl-chain.md` — dependency-closed paper
proof of the whole Weyl chain with crude explicit constants:

- (KL) Kuzmin–Landau: `|S| ≤ 1/δ + 1` (g' monotone, ‖g'‖ ≥ δ ≤ 1/2); proof via integer-band
  reduction, MVT β_n monotone, summation by parts, cot-variation ≤ 1/(πδ).
- (D2): `|S| ≤ 5hN√λ + 15/√λ` (λ ≤ 1), crossing-splitting with δ = √λ/2.
- (W) windowed Weyl–vdC: `|S|² ≤ 9N²/H + (6N/H)Σ_{h<H}S_h*` (subinterval maxima).
- (Dk): `|S| ≤ A_k(N(h²λ)^{e_k} + N^{1−2^{2−k}}λ^{−2^{1−k}})`, e_k = 1/(2^k−2), λ ≤ 1 ≤ h;
  **A_k ≤ 15√A_{k−1} + 4 ≤ 256 bounded**; induction via (W) with H = ⌈(h²λ)^{−e'/(1+e')}⌉ ∧ N,
  exponent identity e_k = (1/2)·e'/(1+e'); e'/2 ≤ 2^{1−k} closes the second term; h'λ > 1
  handled by the trivial branch; cap branch lands in the second term via k ≥ 3.
- Dyadic-block data for ζ: λ = (t/2π)(k−1)!(2N)^{−k}, h = 2^k, and (h²)^{e_k} ≤ 4 always.
- (Z): Abel 1/n per block + PNTPlus truncation; honest-shape numeric certification ratios to
  logt/loglogt: 2.09/1.56/1.33/1.19 at logt = 230/2303/23026/230259 (A = 200 model of the
  ≤ 256 bound). Lean acceptance tests = these tables.

Remaining in L2: stage-(R) region-transfer numeric gate (Titchmarsh 1-line → region, mirroring
PNTPlus Landau pipeline). Then L3 = `Sieve/KuzminLandau.lean` (mapping section in the doc).
