# Approximate joint eigenrows of two dilations are tied power rows

- **ID:** adr-two-dilation-eigenrows
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `w : ℕ → ℂ`, `w(0) = 0`, and call `w` an approximate eigenrow of `D_p` with
  exponent `s` when `w − p^s D_p w` has finite pronic energy. If `w` is one for `D₂` with exponent `s₂`
  and for `D₃` with exponent `s₃`, where `Re s₂ = Re s₃ ∈ (1/2, 1]`, then `w − c n^s` has finite pronic
  energy for some `c` and `s` with `Re s = Re s₂`, and if `c ≠ 0` the exponent is tied:
  `2^s = 2^{s₂}`, `3^s = 3^{s₃}`. If no exponent is tied to both, `w` has finite energy. For
  `s₂ = s₃ = s` this gives `w ∈ ℂ n^s + (finite energy)`, and conversely every such row passes the law
  of exponent `s` at every `p`.

## Paper proof
1. **Log scale.** `g(u) = e^{−u/2} w(⌊e^u⌋)`; the law at `p` with `s = κ + 1/2 + iγ` becomes
   `g − e^{(κ+iγ)log p} g(· − log p) ∈ L²` (exact, by `⌊⌊x⌋/p⌋ = ⌊x/p⌋`).
2. **Rotation.** `h = e^{−iγu} g` satisfies the real law `h − e^{κτ} h(· − τ) ∈ L²` in both real and
   imaginary parts. The real one-prime calculus gives `h = e^{κu}Π − S`, `Π` a.e. `τ`-periodic,
   `S ∈ L²`; so `g = e^{(κ+iγ)u}Π − e^{iγu}S`.
3. **Matching.** With `P = e^{iγ₂u}Π₂`, `Q = e^{iγ₃u}Π₃`: `e^{κu}(P − Q) ∈ L²`, `P(u + τ₂) = e^{iγ₂τ₂}P(u)`,
   `Q(u + τ₃) = e^{iγ₃τ₃}Q(u)`. Then `ψ = Q(· + τ₂) − e^{iγ₂τ₂}Q` equals `−(δ(· + τ₂) − e^{iγ₂τ₂}δ)`,
   `δ = P − Q`, so `∫_{u>0} |ψ|² < ∞`; `|ψ|` is `τ₃`-periodic, hence `ψ = 0`. So `Π₃` is an
   eigenfunction of the rotation by `τ₂` on `ℝ/τ₃ℤ` with eigenvalue `μ = e^{i(γ₂−γ₃)τ₂}`.
4. **Eigenfunctions of an irrational rotation.** `|Π₃|` is invariant under both shifts, so constant
   (ergodicity). If nonzero, Parseval on `(0, τ₃]` gives a nonzero Fourier coefficient `c_k`; shifting
   the integration window shows `μ c_k = e^{2πikτ₂/τ₃} c_k`, so `μ = e^{2πikτ₂/τ₃}`; then
   `Π₃ e^{−2πiku/τ₃}` has both periods and is constant.
5. **Conclusion.** `g = c e^{zu} − e^{iγ₃u}S₃` with `z = κ + i(γ₃ + 2πk/τ₃)`; `e^{zτ₃} = e^{(κ+iγ₃)τ₃}` and
   `e^{zτ₂} = e^{(κ+iγ₃)τ₂}μ = e^{(κ+iγ₂)τ₂}`. Rounding `(e^u)^s − ⌊e^u⌋^s = O(‖s‖)` costs `O(e^{−u/2})`.
6. **Same exponent.** `2^{s'} = 2^s`, `3^{s'} = 3^s` give `(s' − s)log 2 ∈ 2πiℤ`, `(s' − s)log 3 ∈ 2πiℤ`,
   so `m log 2 = n log 3`, forcing `s' = s`. **Converse:** `|n^s − (p⌊n/p⌋)^s| ≤ (‖s‖ + 1)p` and
   `D_p` contracts the pronic norm by `√(2/p)`.

## Lean
`ArithmeticDefectRigidity/TwistedOnePrimeLawsForceTiedExponents.lean`: `periodize_ae_eq`,
`integral_circleChar_mul_shift`, `eigenfunction_of_irrational_rotation`,
`ae_twisted_periodic_of_weighted_difference`, `eq_twisted_decomposition`,
`ae_periodic_twistedGhost`, `lintegral_sq_twistedTail_ne_top`,
`exists_lintegral_sub_const_mul_cexp_ne_top`.
`ArithmeticDefectRigidity/TwoDilationEigenrowsArePowerRows.lean`: `lintegral_cLogProfile_sq`,
`twistedDefect_cLogProfile`, `exists_cPronicEnergy_sub_cpow_ne_top`, `cPronicEnergy_ne_top_of_untied`,
`eq_of_two_three_cpow_eq`, `exists_cPronicEnergy_sub_cpow_ne_top_same`,
`cPronicEnergy_cEulerLaw_ne_top`. Standard axioms only.

## Insight
At the source level, tiedness is automatic: a row that behaves like a joint eigenvector of `D₂` and
`D₃` up to finite energy is a single power row, and its eigenvalue pair is `(2^{−s}, 3^{−s})` for one
exponent `s`. Kronecker-untied pairs, which the Gram laws of normalized limits allow, admit no
escaping row at all. The gap between "escape" and "power-like escape" is therefore exactly the gap
between normalized (`o(√E)`) and absolute (`O(1)`) eigen-errors.
