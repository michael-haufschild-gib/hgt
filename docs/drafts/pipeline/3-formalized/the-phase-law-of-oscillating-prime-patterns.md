# The phase law of oscillating prime patterns

- **ID:** phase-law-oscillating-prime-patterns
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Trans-Horizon Incidence Mechanics (§5 "prime-density heuristics at half damping")
- **Statement:** For `|a| ≤ 1`, `t₀ ≠ 0`, `φ ∈ ℝ` and the completely multiplicative pattern
  `f(p) = a cos(t₀ log p + φ)`, the half-damped weight `f(d) d^{-1/2}` is paid iff
  `a cos φ < 1` or `ζ(1/2 + it₀) = 0`.

## Why it matters

`oscillating-prime-patterns-read-the-critical-zeros.md` settled the phase `φ = 0`. With a phase the
complex amplitude `b = a e^{iφ}` enters, and the receiver depends only on `Re b = a cos φ`. The
Hilbert-conjugate part `a sin φ` couples to `arg ζ`, and that coupling never obstructs. Example: for
`a = 1`, `φ = π/3` the prime values fill `[−1, 1]`, yet the weight is paid at every height. The
new tool: `arg ζ(1 + u + iτ)` is bounded uniformly in `0 < u ≤ 1` on compact `τ`-ranges, including
at the pole.

## Paper proof

1. **Euler logarithm of `ζ`** (`RHTower/ZetaEulerLogarithmOnBoxes`). `ℓ = Σ_p −log(1 − p^{-w})`,
   `Re ℓ = log|ζ|`, `ℓ' = ζ'/ζ`, `ℓ` real on the real axis. With `G = (w − 1)ζ`, entire and zero-free
   on `Re ≥ 1`, `h(s) = ℓ(1 + u + is) + log(u + is)` has `h' = i G'/G`. So
   `|Im ℓ(1 + u + iτ)| ≤ π/2 + |τ| max_box |G'/G|`. Compactness gives `m ≤ |ζ(v)| |v − 1| ≤ K` on
   boxes.
2. **Euler comparison.** `f(p)p^{-w} = b p^{-(w−it₀)} + b̄ p^{-(w+it₀)}` and `|Σ_p p^{-v} − ℓ(v)| ≤ S`
   give `|log|F(w)| − Re(bℓ(w − it₀) + b̄ℓ(w + it₀))| ≤ 2S`. Also
   `Re(bℓ) ≤ (a cos φ/2) log|ζ| + |Im ℓ|/2`, and `Re(bℓ) ≤ |ℓ|/2`.
3. **Small heights** (`t₀ > 0`, `0 < Im w ≤ 2t₀ + 18`). The arguments are bounded. Write
   `|ζ(w − it₀)||ζ(w + it₀)| = Y/|w − it₀ − 1|` with `Y` between two positive constants. Then
   `|F| ≤ A(|Im w − t₀|^{-(a cos φ)⁺/2} + 1)`.
4. **Large heights.** `|ℓ(σ + it)| ≤ 9 log log t + C` gives `|F| ≤ C (2 log Im w)^9 ≤ B₁ (Im w)^{1/4}`.
5. **Payment.** The singularity `|t − t₀|^{-(a cos φ)⁺}` is integrable when `a cos φ < 1`
   (`receiverBounded_pattern_half_of_bounds`, a generic criterion for patterns). `t₀ < 0` reduces to
   `t₀ > 0` with phase `−φ`.
6. **Boundary.** `a cos φ = 1` forces `|a| = 1` and `sin φ = 0`, so `f = cos(t₀ log p)`, which is
   paid iff `ζ(1/2 + it₀) = 0` (`receiverBounded_oscWeight_iff`).

## Lean

- `RHTower/ZetaEulerLogarithmOnBoxes.lean`: `zetaEulerLog`, `exp_zetaEulerLog`, `re_zetaEulerLog`,
  `hasDerivAt_zetaEulerLog`, `im_zetaEulerLog_ofReal`, `zetaResidueUnit_ne_zero_of_one_le_re`,
  `exists_norm_zeta_mul_sub_one_bounds`, `exists_abs_im_zetaEulerLog_le`,
  `exists_norm_zetaEulerLog_le_large`.
- `TransHorizonIncidenceMechanics/ThePhaseLawOfOscillatingPrimePatterns.lean`: `phasePattern`,
  `phaseWeight`, `phasePattern_eq_oscPattern_one`, `abs_log_norm_phaseSeries_sub_le`,
  `norm_phaseSeries_le`, `norm_phaseSeries_le_exp`, `exists_norm_phaseSeries_le_small`,
  `exists_norm_phaseSeries_le_large`, `receiverBounded_pattern_half_of_bounds`,
  `receiverBounded_phaseWeight_of_lt_one`, `receiverBounded_phaseWeight_iff` (axioms `propext`,
  `Classical.choice`, `Quot.sound`).

## Gates
- [x] 0 → 1  in-progress (corpus: phase `0` only; no bound on `arg ζ` near the pole)
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized

## Log
- 2026-10-23 — created, formalized, wired into the THIM and RHTower umbrellas.
