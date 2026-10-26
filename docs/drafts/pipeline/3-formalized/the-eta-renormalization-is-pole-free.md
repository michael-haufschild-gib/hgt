# The eta renormalization of the cofactor is pole-free

- **ID:** adr-eta-renormalization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `H_ε v(n) = Σ_{j≤n} (−1)^{j+1} j^{-ε} v(⌊n/j⌋)`. For `0 < ε < 1/2`:
  (a) `H_ε = S − 2^{1−ε} D₂ S`, `S v(n) = Σ_{j≤n} j^{-ε} v(⌊n/j⌋)`;
  (b) on the actual receiver `‖H_ε A‖_T ≤ B` for every horizon `T`, with no trace or domain;
  (c) for `0 < Re s < 1 − ε`, `H_ε Re(a n^s) − Re(a η_ε(s) n^s)` has bounded pronic energy, where
  `η_ε(s) = (1 − 2^{1−ε−s}) ζ(s + ε)`;
  (d) the tail `Σ_{2K<j≤n}` of `H_ε v` is bounded in pronic norm by
  `Σ_{K≤i<T} [(2i+1)^{-ε}‖D_{2i+1}v − D_{2i+2}v‖ + ((2i+1)^{-ε} − (2i+2)^{-ε})‖D_{2i+2}v‖]`;
  (e) for an escaping actual cofactor limit, if the normalized tail beyond `2K` is eventually `≤ τ`,
  the alternating packet `Σ_{j,k≤2K} a_j a_k K(j,k)`, `a_j = (−1)^{j+1}j^{-ε}`, is `≤ τ²`.

## Paper proof
(a) `(−1)^{j+1} = 1 − 2·[2|j]`; even `j = 2i` contribute `2·2^{-ε} i^{-ε} v(⌊⌊n/2⌋/i⌋)`.
(b) `S A = c_ε n^{1−ε} + R_ε` with `‖R_ε‖_T ≤ B_ε`. Then
`H_ε A = R_ε − 2^{1−ε}D₂R_ε + c_ε(n^{1−ε} − 2^{1−ε}⌊n/2⌋^{1−ε})`; the last bracket lies in `[0, 1]`
(concavity of `x^α`), contributing `≤ c_ε` to the pronic norm; `D₂` contracts by `√(2/2) = 1`.
(c) Apply (a) to the symbol law `S n^s = P(s) n^{1−ε} + ζ(s+ε) n^s + O(n^{(Re s−ε)/2})`; the pole terms
cancel up to `P(s)·[0,1]`, `2^{1−ε}(n/2)^s = 2^{1−ε−s} n^s`, and rounding `⌊n/2⌋^s` costs `≤ ‖s‖ + 1`.
(d) Extend the tail to `2T` (terms with `j > n` vanish since `v(0) = 0`), pair `j = 2i+1, 2i+2`, and
apply the triangle inequality.
(e) The packet row equals `H_ε A − tail`; normalize by `√E_T`, use (b), and pass to the limit.

## Lean
`ArithmeticDefectRigidity/TheEtaRenormalizationIsPoleFree.lean`: `etaCofactorSum_eq`,
`etaCofactorSum_actual_eq`, `exists_pronicNorm_etaCofactorSum_actual_le`,
`exists_pronicNorm_etaCofactorSum_powerRow_le`, `pronicNorm_etaCofactorTail_le`,
`alternatingPacket_le_of_tail`. Standard axioms only.

## Insight
The cofactor pole is exactly the 2-adic Euler factor's pole: `1 − 2^{1−ε}D₂` removes it with no
renormalization functional. The trace-free law `H_ε A = O(1)` holds for the actual receiver at every
horizon, and its symbol in the strip is `η(s + ε)`, whose zeros there are exactly the translated
zeros of `ζ`. What remains for the joint extraction is the tail, which is controlled by dilation
regularity alone.
