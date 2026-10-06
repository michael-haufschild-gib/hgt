# Cutoff transport law for the Liouville hyperbola decomposition

- **ID:** MC-C12.99-S3 (CANNOT-492)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), uniform strengthening of MC-C12.99-S2
- **Lean:** `formal/GaloisForLFunctions/RHTower/LiouvilleHyperbolaCutoffOscillation.lean`

## Statement (unconditional)

`P(x) = Σ_{m≤x} μ(m)W(x/m)` (`λ = μ ∗ 1_□`), `A_θ(x) = Σ_{m≤x^θ} μ(m)W(x/m)`. For every
`0 < θ ≤ ½`, `d ∈ ℝ`, `c ≠ 0`, `β < 1 − θ/2`, `C ≥ 0`: `dP + cA_θ > Cx^β` and `< −Cx^β` for arbitrarily
large `x`. Corollaries `cutoffHead_frequently` (`A_θ` alone) and `cutoffTail_frequently` (`P − A_θ`).

Under RH the exponent `1 − θ/2` is sharp (`A_θ ≈ Z x H₁(x^θ)`, `H₁(y) ≪ y^{−½+ε}`). So every split of the
hyperbola decomposition at a level `x^θ ≤ √x` leaves each piece with a forced excess `x^{(1−θ)/2}` over the
critical scale; only the complete sum can be critical.

## Proof

1. Contraction separation: if every zero `ρ` with `½ ≤ Re ρ < 1`, `Im ρ ≠ 0` had `ζ(1 + θ(ρ−1)) = 0`, the
   iterates `1 + θⁿ(ρ₀ − 1)` from a critical zero would be zeros converging to `1`, contradicting `U(1) = 1`.
2. Head transforms by the scaling `u = v/θ` and the Abel integral: `Z/((s−1)ζ((s−1)/θ+1))` and
   `−2/((s−½)ζ((s−½)/θ+½))`; remainder `|E_θ(x)| ≤ x^θ ≤ x^{1/2}` gives `R_θ` holomorphic on `Re s > ½`.
3. One-sided Landau engine (from MC-C12.99-S2) with `β₁ = max(β, 1 − 3θ/4)` (so `1 − θ < β₁ < 1 − θ/2`, all
   real arguments of the `U`-factors positive right of `β₁`).
4. Multiply by `D(z) = zU(z)(z−½)U(v(z))U(h(z))`; at `w = 1 + θ(ρ−1)`, `h(w) = ρ`, `Re v(w) ≥ 1/(2θ) ≥ 1`,
   `Im v(w) = Im ρ ≠ 0`: the identity gives `η·(cZ/θ)·wU(w)(w−½)U(v(w)) = 0`, impossible.

## Audit

`lake --old build` leaf exit 0; `lake --old env lean` leaf exit 0 without diagnostics; `#print axioms` for the
four public theorems: propext, Classical.choice, Quot.sound. Wired after `LiouvilleTriangularHeadOscillation` in
RHTower.lean. STATUS CANNOT-492.

## Limits

`θ ∈ (½, 2/3)` needs a second separation (the root head's argument can then have real part `< 1`) and the
remainder is only holomorphic on `Re s > θ`; not done. The law says nothing about the complete `P`.
- 2026-10-05 — Abscissa sharpening (Opus): `frequently_gt_and_frequently_lt_abscissa` — `dP + cA_θ` oscillates
  beyond `x^β` for every `β < 1 − θ(1 − Θ)`, `Θ = zetaZeroAbscissa`; zero chain from
  `exists_contracted_nonzero_gt` (start at a zero with `Re ρ > b`, contract until the image is not a zero).
  Consequence: `A_θ = O(x^{1−θ/2+ε})` for all `ε` forces `Θ = ½`. The converse upper half (Littlewood +
  Abel summation) is not formalized. Leaf build exit 0, `lake --old env lean` exit 0, axioms standard.
- 2026-10-05 — Extension to `0 < θ < 2/3` (Opus, CANNOT-493): `RHTower.LiouvilleHyperbolaCutoffWide`
  (`frequently_gt_and_frequently_lt_wide`). The zero is taken alone on its horizontal line
  (`exists_singleton_zero_contracted_nonzero`: injection of singleton fibres into off-line copies against the
  corpus densities ½ and ⅔), which keeps the root-head point `ρ + 1/(2θ) − ½` off the zero set; the remainder is
  holomorphic on `Re > θ`. `integral_cutHarmonicHead`/`integral_cutRootHead` hypotheses weakened to `θ < 1`.
  Leaf builds exit 0, both `lake --old env lean` audits exit 0, axioms standard, wired after the cutoff module.
- 2026-10-05 — Extension to `0 < θ < 3/4` (Opus, CANNOT-494): `RHTower.LiouvilleHyperbolaCutoffThreeQuarter`
  (`frequently_gt_and_frequently_lt_tq`). Square-lattice remainder `W(y) − Zy + 2√y = ½ + O(y^{−1/2})`
  (`abs_squareTriangle_remainder_sub_half_le`, telescoping `1/(q+½) − (1/9)/(q+½)³ ≤ Σ_{k>q}1/k² ≤ 1/(q+½)`), so
  `E_θ = ½M(x^θ) + O(x^{(3θ−1)/2})`; Mertens head transform `1/(2sζ(s/θ))`; its argument at the transported point
  `ρ + 1/θ − 1` is kept off the zero set by the singleton property. Barrier `θ < 3/4` = `(3θ−1)/2 < 1 − θ/2`; the
  next term of the lattice remainder is the oscillating `ψ`-sum `Σ_{k}` of `{√y}`-type, not a power. Leaf build
  exit 0, `lake --old env lean` exit 0, axioms standard, wired after the wide module.
- 2026-10-05 — Exact exponent (Opus, CANNOT-495): `RHTower.LiouvilleHyperbolaCutoffSharp`. `exists_omega_pm_exact`:
  `dP + cA_θ = Ω±(x^{1−θ/2})` for `0 < θ < 3/4`, `c ≠ 0`; `riemannHypothesis_of_eventually_le`: a one-sided bound at
  `x^{1−θ/2}` with any constant implies RH; `frequently_gt_and_frequently_lt_abscissa_tq`: exponent law (lower half)
  for `θ < 3/4`. New device: rightmost zeros of horizontal lines (finite strip fibres) replace singletons off the line.
  Boundary pole: Riesz-type local Landau estimate along `w + r`. Leaf build exit 0, `lake --old env lean` exit 0,
  axioms standard, wired after the three-quarter module. Upper half (RH ⇒ `O(x^{1−θ/2+ε})`) not formalized.
