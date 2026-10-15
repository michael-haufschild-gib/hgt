# The archimedean-minus-prime form: one negative square, odd sector, half-line frame

- **ID:** WMHL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** 1-in-progress/route-tt-loop-2026-10-13.md rows 466–537
- **Statement:** RH holds iff the archimedean-minus-prime form `M = A − P` (Weil functional without its pole) has exactly one negative square; equivalently iff `M ≥ 0` on odd tests; equivalently iff `P(f) ≤ A(f) + Σ_{k≥0}(∫f e^{−(2k+½)x})² + Π(f)` for every real `C²` test `f` supported in `[ε, ∞)`.

## Goal
Make the user's target "the form has exactly one negative square" an exact Lean statement, locate its RH content, and record which parts are unconditional.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized (all modules below: standard axioms, `lake build --old` clean, wired into `RHTower.lean`)
- [ ] 3 → 4  not pursued (no stage 4 for receivers)

## Lean theorems
- `WeilMarkovOneBoundState`: `riemannHypothesis_iff_not_exists_negDef_markovPlane` (RH ⟺ no negative-definite 2-plane of `M`), `exists_markovEnergy_neg` (one negative direction unconditionally), `exists_even_poleFree_negative_of_not_riemannHypothesis`.
- `WeilMarkovOddPositivity`: `riemannHypothesis_iff_forall_odd_markovEnergy_nonneg` (RH ⟺ `M ≥ 0` on odd tests; witness by odd shifts averaged against Riemann's kernel `Φ`).
- `WeilMarkovPrimitiveHyperplane`, `WeilMarkovOnePoleHyperplane`: RH ⟺ `M ≥ 0` on `{∫F cosh(x/2) = 0}`, on `{∫F e^{−x/2} = 0}`, on `{∫F e^{x/2} = 0}` (Hodge-index form; `M(aΦ + bΦ′) = −a²/2 + b²/8`).
- `WeilMarkovOddSectorTrivialZeroSquares`: for `f` supported in `[ε,∞)`, `M(f − f̃) = 2M(f) + 2Σ_k(∫f e^{−(2k+½)x})² + 2Σ_nΛ(n)n^{−½}(f⋆f)(log n)` and `M(f + f̃) = 2M(f) − 2Σ_k(…)² − 2Π(f)`; Lévy form of `A`; `W_reflect_re_eq` (the holomorphic zero sum `Re Σ_ρ m F(ρ)²` is archimedean-free); own bilinear explicit formula.
- `WeilMarkovHalfLineTrivialZeroCriterion`: `riemannHypothesis_iff_forall_halfLine_trivialZeroSquare_nonneg`, `riemannHypothesis_iff_forall_halfLine_archForm_trivialZeroSquare_nonneg` (both directions; converse by odd shifts averaged against the translated kernel `Φ(h − h₀)`, `integral_W_oddShift_mul_weight`).
- Unconditional cones (¬ZL): `WeilMarkovFarOutNonnegativeOddPositivity` (`exists_farOut_nonneg_oddExt_markovEnergy_pos`, PNT window), `WeilMarkovThinNonnegativeOddPositivity` (`thin_nonneg_oddExt_markovEnergy_ge`, Lévy gain).
- No-go: `WeilMarkovArchimedeanWideTestNegativity` (`archForm_le`, `exists_wide_archForm_le`, `exists_wide_nonneg_markovEnergy_le`): the archimedean form is negative on every wide test, so no proof of the shape "positive archimedean part minus small prime part" exists.

## Paper laws (not formalized)
- Sector duality (row 537): `W(f ∓ f̃)/2 = W(f) ± (Π + T − L₋²)`, `T = Σ_{k≥1}(∫f e^{−(2k+½)x})²`, `L₋ = ∫f e^{x/2}`; RH ⟺ `|Π + T − L₋²| ≤ W(f)` on half-line tests; the elementary side is the one-sided (Riemann–von Mangoldt) explicit formula of `f⋆f`.
- Pole shielding (row 533): nonnegative half-line tests satisfy `M(f − f̃) ≥ 8S(½)²(1 − 2Σ_ρ m(β−½)²)`.
- Hilbert fragility (row 535): `M` depends only on `|F̂|²` on ℝ; the Hilbert transform of `Φ` is odd with `M = −½`, so odd positivity needs the decay `e^{|x|/2}` (odd autocorrelations have `k̂ = b²`, `b` odd entire).
- Odd mean-zero obstruction (row 536): odd autocorrelations have `∫k = 0`, so no odd test is pointwise positive and the 3-4-1 mechanism has no odd version without prime-blindness.

## Open core
`P(f) ≤ A(f) + Σ_k(∫f e^{−(2k+½)x})² + Π(f)` for sign-changing half-line tests with `∫f sinh(x/2) ≈ 0`. On prime-blind tests this is odd PBAP (`X + T ≥ L₋²`), whose RH-equivalence needs odd uniqueness (route OWU). Every mechanism tried in rows 466–537 ends at PBAP, at the √x remainder (wall 1), or at the missing surface (wall 5).

## No-go closure
Not a failed route: the frame is an exact receiver. Mechanisms killed (rows 472–536): signed Laplacian/PF, Barta with squared crossing terms, rearrangement, stoquastic gauge, Doob spectral gap via Bakry–Émery or intertwining, Selberg-cusp transfer, Stepanov, tensor-power trick, phase retrieval, Castelnuovo–Severi without a surface.

## Log
- 2026-10-15 — created in 3-formalized from route-tt rows 466–537.
