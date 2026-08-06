# The width-`1/log` Chebyshev contour is proved

`RHTower.Sieve.exists_norm_tsum_vonMangoldt_kappa_one_general`
(`RHTower/Sieve/ChebyshevKappaOneContour.lean`) is the five-term contour estimate at

    c(T) = 1 - (1/40000)/log T,   d(T) = 1 + 1/log T,   |Im s| ≤ T,

with every edge bounded by `C log²T` and cutoff-uniform constants.  Unconditional.

Card: `docs/drafts/pipeline/1-in-progress/chebyshev-exponent-one-half.md`.

## The point

Width `≍ 1/log T` is `w = 1`, so the saving exponent is `1/(w+1) = 1/2` — the classical
`exp(-c√(log x))`.  The Möbius contour is stuck at `1/3` because it needs `1/ζ`, which the corpus
can bound only on width `log^{-2}`.  **`ζ'/ζ` is bounded on the full-width region; `1/ζ` is not.**
That asymmetry is the whole reason ψ beats μ here.

## Supporting layer (also new)

`RHTower/Sieve/ZetaLogDerivRegUniform.lean`:
- `exists_bound_zetaLogDerivReg_box (d T) (hd : 1 ≤ d) (hT : 0 ≤ T)` — the compact-box bound at
  **arbitrary** height.  `exists_bound_zetaLogDerivReg_low_box` was hard-coded to `|Im| ≤ 9`
  although `exists_zero_free_rect` under it is general in `T`.
- `exists_zeta_uniform_kappa_one_zero_free`, `exists_bound_zetaLogDerivReg_uniform` — no height
  restriction, strip pinned to a parameter `K ≥ |Im s|`.  The pole is split off with
  `neg_logDeriv_riemannZeta_eq` and costs `≤ 1/4` since `‖s-1‖ ≥ |Im s| ≥ 4` on the region branch.

`RHTower/Sieve/ChebyshevKappaOneData.lean`: `chebLeftTwo`, `chebRightTwo`, and
`exists_cheb_kappa_one_data` — all five hypotheses of
`norm_tsum_vonMangoldt_sub_full_main_le_explicit` at once.

## Traps (new, not in the Möbius notes)

- **`8 ≤ Real.log T` does NOT give `T > 0`.**  Mathlib's `Real.log x = Real.log |x|`, so
  `T = -e^8` satisfies it.  Always carry `1 ≤ T` separately.
- `rw [hsplit]` with `hsplit : s = ↑s.re + ↑s.im * I` also rewrites `s` inside `|s.im|` on the RHS.
  Apply the lemma first, then `rwa [← hsplit] at h`.
- `smoothWeight` in `RHTower.Sieve` shadows `GaloisForLFunctions.HTGeometry.smoothWeight` once
  enough modules are imported; fully qualify it in statements.

## What is left

Height `chebHeightTwo x = exp(A√(log x))` (with `A` large enough to separate the two edges — the
same lesson as the Möbius parameter's factor `2`), a smoothing ratio `exp(√(log x)/c)`, the main
term (the corpus's `ChebyshevMainTerm*` modules handle it at κ=9), and the assembly.

Beats `PNTPlus.MediumPNT` (`ψ - id =O[atTop] x·exp(-c(log x)^{1/10})`) when finished.
