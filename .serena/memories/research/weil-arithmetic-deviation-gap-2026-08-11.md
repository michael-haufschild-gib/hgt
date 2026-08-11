# Attempt 14: the Euler product enters the Weil form (Lean-proved)

Module: `formal/GaloisForLFunctions/RHTower/GaussHodgeWeilArithmeticDeviationGap.lean` (wired,
umbrella green 18908 jobs, all 6 theorems `[propext, Classical.choice, Quot.sound]`).

## Content
First connection of PNTPlus's formalized Euler-product positivity to the RHTower Weil lane:
- `zeta_zero_of_xi_zero` — xi zero ⇒ riemannZeta zero (corpus `xi_eq_zero_iff` + strip).
- `exists_xi_deviation_gap_high`: ∃ A ∈ (0,1/2], every xi zero with |γ| > 3 has
  (β−1/2)² ≤ 1/4 − A/(2·log⁹|γ|) — zero-free region applied on BOTH sides of the line via
  xi_one_sub (FE).
- `exists_xi_deviation_gap_low`: ∃ uniform δ > 0, |γ| ≤ 3 ⇒ (β−1/2)² ≤ 1/4 − δ (from
  ZetaNoZerosInBox 3, σ₂ := max σ₁ (3/4) trick).
- Divisor versions (`exists_xiSpectralPoint_deviation_gap_low/high`); new coordinate lemmas
  `xiSpectralPoint_re` (= γ), `xiSpectralPoint_im_sq` (= (β−1/2)²).
- **Producer fragment** `exists_arithmetic_gap_lowSupported`: tests with divided differences
  supported at height ≤ 3 satisfy Re W(F,F) ≥ Σ‖even‖² − (1/4 − δ)·Σ‖ΔF‖², δ > 0 arithmetic.
  First strict improvement of the strip constant 1/4 in the Weil form.

## Calibration (honest)
Zero-free regions (3-4-1 positivity) repel zeros from the strip WALLS ⇒ deviation weight
strictly < 1/4. The socket needs weight → 0 (zeros ON the line). The distance from 1/4 − δ to 0
is the lane's exact open problem — now with the two known positivity mechanisms formally on
opposite ends of the same inequality.

## PNTPlus assets discovered (reusable)
- `ZetaZeroFree : ∃ A ∈ Ioc 0 (1/2), ∀ σ t, 3 < |t| → σ ∈ Ico (1 − A/log⁹|t|) 1 → ζ(σ+tI) ≠ 0`
- `ZetaNoZerosInBox (T) : ∃ σ < 1, ∀ t, |t| ≤ T → ∀ σ' ≥ σ, ζ(σ'+tI) ≠ 0`
- `ZetaNoZerosOn1Line`, `LogDerivZetaHolcLargeT` (ζ'/ζ holomorphic on the region — potential
  future input for explicit-formula fragments).
- All top-level (no namespace); `import GaloisForLFunctions.PNTPlus.ZetaBounds`; RHTower already
  imports PNTPlus elsewhere (precedent: XiMassPrimeSquareBoundaryResidue, PrimeRpowAbelSummation,
  Sieve/PerronKernelResidue).

## Next candidates
- Extend the fragment to all heights with the log⁹ weight profile (weighted tsum bound).
- `LogDerivZetaHolcLargeT` as the germ of a formal explicit-formula fragment.
- Gaussian/Paley–Wiener test families with height-controlled divided differences.
