# Finite off-line von Koch law; Route 1 seam contraction near the line

- **ID:** FOZ-VONKOCH-SEAM-20261010
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Opus RH loop rows 755, 762; STATUS MUST-902, MUST-903
- **Statement:** (i) If a finite set `S` of zero copies contains every off-line copy, then `|ψ(x) − x + Re Σ_{q∈S}x^q/q| ≤ (200(A+2) + 4|S|)√x log²x` for `x ≥ 16`. (ii) For `0 < c ≤ ¼`, `0 < r < ½`, `½ + c ≤ σ₀ − r`, `σ₀ + r < 1`, at most `C(c)(X^{1−c/28} + (1+log X)²)` of the discs of radius `r` at `σ₀ + in`, `n ≤ X`, contain a zero of `ξ`; on all others Route 1's adjoint seam contracts.

## Goal
(i) is the exact decomposition every attempt to exclude a single isolated top quartet (ITQ, loop rows 734–761) must contradict. (ii) extends Route 1's partial producer from `σ₀ ≥ 7/10 + r` to the whole right half-strip.

## Gates
- [x] 2 → 3 formalized: `RHTower.abs_chebyshevPsi_sub_add_offLineWave_le`, `RHTower.exists_abs_chebyshevPsi_sub_add_offLineWave_le_of_finite` (`FiniteOffLineVonKoch`); `RHTower.exists_card_badUniformDiscs_le_nearLine` (`XiRightDiscSeamContractionNearLine`). Standard axioms, wired.

## No-go closure
- **Killing mechanism (ITQ):** every unconditional arithmetic input is an upper bound, a family average, an `o(1)` statement, a twisted sum or 1-line data (loop rows 734–769). The ITQ wave sits at the principal major arc.
- **Strongest positive survivor:** (i), in Lean. Its converse (wave bound ⇒ off-line copies ⊆ `S`) needs a finite-subtraction Landau lemma [P, open in Lean].
- **New insight:** a single off-line zero is a relative-`x^{β₀−1}` wave. Detecting it needs a single-scale relative power saving, i.e. wall 1.

## Log
- 2026-10-10: rows 755 and 762 formalized; card created in 3-formalized.

## Converse closed (2026-10-10)

The converse of (i) is now in Lean (MUST-906), so the open-in-Lean remark above no longer applies.
- `FiniteOffLineLandau.lean`:
  - `norm_lagPoleSeries_ge_disc`: the pole blow-up on a punctured disc.
  - `re_le_half_add_of_lagPoleSeries_sub_extension`: continuation of `G` up to a finite pole set, via a tilted ray.
  - `exists_differentiable_extension_of_le_exp`: Landau's theorem for any real function bounded on one side.
- `FiniteOffLineConverse.lean`:
  - `subtractedLag_log_mul_sqrt`: the wave moved through the Chebyshev tail.
  - `re_le_half_add_of_chebyshevPsi_sub_add_offLineWave_ge`: the one-sided converse.
  - `finite_offLine_iff_exists_offLineWave`: FOZ ⟺ a finite-wave law for ψ.
- Both modules are wired into `RHTower.lean` and use standard axioms only.
- The converse allows for multiplicities: zeros sharing a value with some `q ∈ S` are excluded only through the finite pole set `{ρ_q − ½, conj ρ_q − ½}`.
