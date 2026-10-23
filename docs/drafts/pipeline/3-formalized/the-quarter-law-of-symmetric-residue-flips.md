# The quarter law of symmetric residue flips

- **ID:** quarter-law-symmetric-residue-flips
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Trans-Horizon Incidence Mechanics (§5 "the parity pair": the `1/4` law)
- **Statement:** Let `S ⊆ ZMod q` be closed under inversion on the units, `f_{q,S}` the completely
  multiplicative `±1` pattern flipping the primes with residue in `S`. The half-damped weight
  `f_{q,S}(d) d^{-1/2}` is paid iff `φ(q) < 4 #(S ∩ (ZMod q)ˣ)`.

## Why it matters

Necessity (`ρ ≤ 1/4` unpaid) held for every residue pattern; sufficiency was known only for subgroup
flips, where every character exponent is nonnegative. For a symmetric `S` the exponents of the
nonprincipal `L(·, χ)` have both signs, so the payment needs reciprocal bounds for Dirichlet
`L`-functions right of `Re s = 1`. With those bounds the flipped proportion `1/4` is the exact
threshold on the whole symmetric family: there the real-axis density decides the receiver, whereas
for oscillating patterns it does not.

## Paper proof

1. **Coefficients.** `s_χ = Σ_{u ∈ S unit} χ(u⁻¹)`; orthogonality `Σ_χ s_χ χ(b) = φ [b ∈ S unit]`;
   symmetry and `conj χ(u⁻¹) = χ(u)` make `s_χ` real; `|s_χ| ≤ φ`, `s_1 = #(S ∩ units)`.
2. **Prime decomposition.** `f(p) y = y − (2/φ) Σ_χ s_χ χ(p) y + (f(p) − 1)[p ∣ q] y`; the principal
   prime sum is `P − Σ_{p∣q} p^{-w}`.
3. **Euler bound.** The two-sided Euler logs of `ζ` and `L(·, χ)` give on `Re w > 1`
   `|F| ≤ e^B |ζ|^{1−2ρ} Π_{χ≠1} |L(·, χ)|^{e_χ}`, `e_χ = −2s_χ/φ ∈ [−2, 2]`, `ρ = s_1/φ`.
4. **Reciprocal `L` bounds** (`RHTower/DirichletLReciprocalRightOfTheOneLine`). Inside the logarithmic
   strip the corpus bound `1/|L| ≤ C log⁷|t|`; beyond it the 3-4-1 product with `|L(1+η, χ₀)| ≤ K/η`,
   `|L(1 + η + 2it, χ²)| ≤ 2K log|t|` and `η ≥ a/log⁹|t|` gives `|L|⁴ ≥ a³/(2K⁴ log²⁸|t|)`. On boxes
   `|Im s| ≤ T`, `L(·, χ)`, `χ ≠ 1`, is entire and zero-free on `Re s ≥ 1`, so `|L|^{±1}` is bounded.
5. **Size.** `X^e ≤ max(X, 1/X)²` for `|e| ≤ 2`. With `a₀ = max(1 − 2ρ, 0)`: on `0 < |t| ≤ 9`,
   `|F| ≤ A(|t|^{-a₀} + 1)` (pole bound `|ζ| ≤ K₀/|t|` if `ρ ≤ 1/2`, box bound for `1/|ζ|` otherwise);
   on `|t| ≥ 9`, `|F| ≤ C log^{10 + 14k}|t| ≤ C' |t|^{1/4}`.
6. **Payment.** `ρ > 1/4` gives `2a₀ < 1`, so the majorant `A'(|t|^{-2a₀} + 1)` is integrable on
   `(0, 9]`; `exists_lineEnergy_le_of_majorant` bounds the line energies and
   `weightPronicEnergy_le_of_lineEnergy_le` pays the receiver.
7. **Necessity** for `ρ ≤ 1/4`: `not_receiverBounded_residueFlip_half_of_le`.

## Lean

- `RHTower/DirichletLReciprocalRightOfTheOneLine.lean`: `exists_norm_inv_LFunction_le_log_pow`,
  `exists_norm_LFunction_le_box`.
- `TransHorizonIncidenceMechanics/TheEulerExponentsOfSymmetricResidueFlips.lean`: `setCoeff`,
  `sum_setCoeff_mul`, `setCoeff_one`, `UnitSymmetric`, `setCoeff_im_eq_zero`,
  `residueFlip_prime_mul_eq`, `abs_log_norm_LSeries_sub_re_le`, `exists_log_norm_residueFlip_le`.
- `TransHorizonIncidenceMechanics/TheQuarterLawOfSymmetricResidueFlips.lean`:
  `exists_norm_residueFlip_bounds`, `receiverBounded_residueFlip_half`,
  `receiverBounded_residueFlip_half_iff` (axioms `propext`, `Classical.choice`, `Quot.sound`).

## Gates
- [x] 0 → 1  in-progress (corpus: sufficiency only for subgroup flips; no reciprocal `L` bound right
  of the strip)
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized

## Log
- 2026-10-23 — created, formalized, wired into the THIM and RHTower umbrellas.
