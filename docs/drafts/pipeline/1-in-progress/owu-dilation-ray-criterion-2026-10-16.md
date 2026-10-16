# OWU: the dilation-ray criterion (obstacles 1 and 2 on a single ray of tests)

- **ID:** owu-dilation-ray-criterion
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean target) + conjecture ledger for the three open OWU obstacles
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU; successor of
  `3-formalized/owu-cut-is-even-mean-zero-deficit-2026-10-16.md`
- **Statement (target):** Let `φ` be the reference bump (`1` on `[−1,1]`, supported in `(−2,2)`,
  even, `0 ≤ φ ≤ 1`) and `φ_T(x) = φ(x/T)`. If `lam` is odd Weil-positive and
  `Re W_lam(φ_T ⋆ φ̃_T) ≥ 0` for every `T ≥ 1`, then `lam = Λ` and RH. Hence
  RH ⟺ some odd Weil-positive weight is Weil-positive on the dilation ray of one bump.

## Why this is structural

After the previous card the OWU Needs were (1) even mean-zero positivity (= cut removal),
(2) central nonnegativity of the extension, (3) an odd-positive source. The spectral weights of
the dilates `φ_T` (not mean-zero: `φ̂_T(0) = T∫φ`) are
`Θ = [(1+γ²)T²|φ̂(T√γ)|² − T²(∫φ)²]/γ` on critical ordinates (bounded by `T²C₁`, and
`≤ T²γ(∫φ)² − T⁴(∫φ)/6` near the centre), and
`Θ = T²[(∫φ)² − (1+γ²)E(Tr)²]/r² ≤ −4T²(T⁴r⁴/36 − 12)` on the cut, where `E(Tr) ≥ 2 + T²r²/6`.
So positivity on the ray forces: no cut mass (quartic beats quadratic), no central atom
(`Θ(−1) ≤ −T⁴(∫φ)/6`), and `∫_{γ≥δ} dν/γ ≤ δν(S¹) − c` for every `δ`, i.e. the extension satisfies
`(x−½)Ψ̃(x) = ∫(γz−1)/(z+γ) dν − c ≥ 0` on `(½,∞)`. Both remaining analytic obstacles are the single
one-parameter family of inequalities `W_lam(φ_T⋆φ̃_T) ≥ 0`, whose arithmetic content is the
scale-`T` excess of the `½`-weighted sum of `lam` over its archimedean prediction.

## Conjecture ledger (this loop)
1. Obstacle 3 (`PrimeBlindPositiveOddAt 1`): by odd Farkas it is `∃` odd-positive `lam`; by the
   Nevanlinna characterisation it is `∃` a real Dirichlet series `D` (abs. conv. on `Re s>1`) with
   `a(Ψ₀ − D)(½+a)` Nevanlinna off `(−∞,¼]`. On the critical line this reads
   `Re D(½+0+iτ) ≤ w(τ)` (archimedean density), with equality a.e. for `Λ` under RH, and the pole
   condition forces `Σ_{n≤x} lam(n) ∼ r x`, `r ≥ 1` (the corpus caps `r ≤ 1`). Absolutely convergent
   series on the line cannot carry the pole; `ζ(s) − 1`, `2Σ Λ(n)n^{−2s}`, Euler-product
   perturbations all violate the line condition. Unconditional provability of the source is
   `RH ∨ (existence of odd fakes)`: not reachable by construction. Recorded, not solved.
2. Short-support odd tests are automatically blind; the corpus's window programme proves
   `weilArchRe ≥ 0` for nonnegative tests up to window `4/9` and for signed tests up to `~1/36`
   (`half_window_signed_short_support_le_weilArchRe`). This covers `PrimeBlindPositiveOddAt 1` on
   tiny supports only; the long-support blind combinations are the RH-hard core.
3. Obstacle 2 is invisible to all mean-zero tests but visible to the dilation ray (this card).
4. Obstacle 1 was the even mean-zero deficit (previous card); on the dilation ray it is the
   quartic-versus-quadratic growth.

## Gates
- [x] 0 → 1  well-posed
- [ ] 1 → 2  paper proof above (to be checked against Lean)
- [ ] 2 → 3  Lean

## Log
- 2026-10-16 — created
