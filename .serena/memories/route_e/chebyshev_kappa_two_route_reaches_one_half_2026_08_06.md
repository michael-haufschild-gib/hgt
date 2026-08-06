# The ψ route reaches exponent 1/2 with the toolkit already built

**The asymmetry between `1/ζ` and `ζ'/ζ` is the whole story.**

- The Möbius contour integrand carries `1/ζ`.  The corpus can bound `1/ζ` polynomially in the
  logarithm only on a strip of width `≍ log^{-2}|γ|` (`exists_zeta_lower_strip`), because
  transporting the `σ = 1+log^{-2}` bound leftwards costs `‖ζ'/ζ‖ × length` and `ζ'/ζ ≪ log²`.
  Width `log^{-2}` ⟹ saving exponent `1/3`.  This is proved and is the terminus for μ by this route.

- The Chebyshev contour integrand carries `ζ'/ζ`, and the corpus **already** bounds it on the
  *full-width* exponent-one region:

      exists_logDeriv_zeta_bound_explicit  (RHTower/Sieve/ZetaLogDerivRegionBound.lean)
      ∃ C T, 0 < C ∧ 4 ≤ T ∧ ∀ σ γ, T ≤ |γ| → 1 - (1/40000)/log|γ| ≤ σ → σ ≤ 9/8 →
        ‖logDeriv riemannZeta (σ + iγ)‖ ≤ C · log²|γ|

  Width `≍ 1/log|γ|` is `w = 1`, so the saving exponent is `1/(w+1) = 1/2` — the classical
  `exp(-c√(log x))`.  No new analytic input is needed; only the contour has to be re-instantiated.

## Why this is worth doing

The vendored `PNTPlus.MediumPNT` proves `ψ - id =O[atTop] x·exp(-c(log x)^{1/10})` — exponent
`1/10`, κ=9-shaped.  The corpus's own `Chebyshev*` chain (36 modules) reaches only the qualitative
`ψ(N)/N → 1`.  A κ=1 Chebyshev contour would beat both and match the classical exponent.

## What to reuse and what to re-tune

Reuse: `norm_tsum_moebius_smoothWeight_le_sharp`-style parametric rectangle lemmas, the
`ZeroFreeRegionKappaOne` / `ZetaLogDerivRegionBound` toolkit, and the tuning lessons from
`mem:route_e/moebius_sharp_rate_exponent_one_third_2026_08_06`:

- the contour parameter needs a factor separating the two edges (at the exact balance point they
  cancel and nothing is saved);
- the smoothing width is a **fraction of the same power**, not a smaller power;
- `Λ(n) ≤ log n` makes the smooth-vs-sharp comparison cost `(H+1)·log(N+H)`, one logarithm more
  than the Möbius case (`ChebyshevSmoothVsSharp.lean` already states this).

At `w = 1` the parameter should be `⌈exp(2√(log x))⌉₊`-shaped and the smoothing ratio
`exp(√(log x)/c)` for a suitable `c`.
