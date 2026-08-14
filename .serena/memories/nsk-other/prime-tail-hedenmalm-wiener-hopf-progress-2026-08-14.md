# prime-tail-hedenmalm-wiener-hopf-transgression — formalization state

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/prime-tail-hedenmalm-wiener-hopf-transgression.md`.
Theorems 1–4 plus a Corollary; the "Revised open core" is RH-equivalent and is flagged open on the
card itself (that is fine — it is not claimed as proved).

## DONE 2026-08-14 — Theorem 1
`formal/GaloisForLFunctions/RHTower/ThetaWienerHopfTransgression.lean` (wired into
`GaloisForLFunctions/RHTower.lean`, compiling, axiom-clean):
- `halfLineConvMinus k f x = ∫ L in Ioi 0, k (x - L) * f L` (`T₋`),
  `halfLineConvPlus` (`T₊`), `halfLineConvEven` (`C`), `halfLineConvOdd` (`S`);
- **`halfLineConvPlus_eq_halfLineConvMinus_neg`** — equation (3), for an even kernel;
- `halfLineConvEven_neg`, `halfLineConvOdd_neg` — `C f` even, `S f` odd;
- `zeroExtend`, `halfLineConvMinus_eq_lineConv`;
- **`lintegral_enorm_sq_halfLineConvMinus_le`** and **`lintegral_enorm_sq_halfLineConvPlus_le`** —
  the `L¹ ⋆ L² → L²` bound `‖T∓ f‖₂ ≤ ‖k‖₁ ‖f‖₂` in `ℝ≥0∞` form, from the corpus's
  `HTGeometry.lintegral_enorm_sq_le_of_convolution_bound` (`YoungConvolutionL2.lean`).
LEAN NOTES: `MeasureTheory.lintegral_sub_left_eq_self` and `lintegral_neg_eq_self` both need
`(μ := (volume : Measure ℝ))` and an explicit function argument, else the `IsNegInvariant` instance
search gets stuck on a metavariable.

## NEXT — Theorem 2 (equations (4)/(5))
`∂_x C f = S(f')`, `∂_x S f = k·f(0) + C(f')`.  Derivation (verified on paper):
`∂_x T₋ f = T₋(f') + k(x) f(0)` and `∂_x T₊ f = -T₊(f') - k(x) f(0)` by half-line integration by
parts (`∂_L k(x-L) = -k'(x-L)`, `∂_L k(x+L) = k'(x+L)`); the two endpoint traces cancel in `C` and
add in `S`.  Lean needs: differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with `k ∈ C¹`, `k' ∈ L¹`, and `f` smooth with
`f, f'` decaying, plus the endpoint limit `k(x-L) f(L) → 0` as `L → ∞`.

## THEN — Theorems 3 and 4
Theorem 3 (zero specialization = Hedenmalm's fold): the card's Lean status says the zero-specialized
folded equations (11)–(12), parity, and first-conormal nonannihilation are ALREADY formalized in
`RHTower/XiHedenmalmReflectionFoldedDirac.lean` — check exactly what is there before writing.
Theorem 4 (the exact `L²`/boundary wall) and the Corollary (elementary positive self-adjoint
consumer) still to be assessed.
