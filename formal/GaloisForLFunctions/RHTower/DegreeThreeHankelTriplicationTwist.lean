import GaloisForLFunctions.HTGeometry.GammaMultiplication
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The triplication twist of the `Γ_ℝ(s)³` Hankel transform

Let `G(v) = Γ_ℝ(v)³ / Γ_ℝ(1 - v)³` be the Mellin multiplier of the Voronoi–Hankel transform
attached to the functional equation of `ζ(s)³`. In the cube-root chart `X = √3 x^{1/3}` this
transform has Mellin multiplier `3^{w - 1/2} G((w + 1)/3)`. The sine transform has multiplier
`Γ_ℝ(w + 1)/Γ_ℝ(2 - w)`. With `v = (w + 1)/3`, the quotient of the two multipliers is

`3^{w - 1/2} · [Γ_ℝ(v)³/Γ_ℝ(3v)] / [Γ_ℝ(1 - v)³/Γ_ℝ(3 - 3v)] = R(v)/R(1 - v)`,

with `R(v) = Γ(v/2)² / (Γ(v/2 + 1/3) Γ(v/2 + 2/3))` (`tripR`). The powers of `π` and `3` cancel.
The proof uses Gauss multiplication for `n = 3` (up to its constant, which cancels), in the form

`Γ(v/2)³ / Γ(3v/2) = C · 3^{-3v/2} · R(v)` (`gamma_cube_mul_inv_gamma_triple`).

So the `Γ_ℝ(s)³` transform is the sine transform composed with the Mellin multiplier
`R(v)/R(1 - v)`, which is unimodular on the critical line (`triplication_twist`).
-/

open Complex

namespace RHTower.DegreeThreeHankel

open GaloisForLFunctions

/-- `R(v) = Γ(v/2)² Γ(v/2 + 1/3)⁻¹ Γ(v/2 + 2/3)⁻¹`. -/
noncomputable def tripR (v : ℂ) : ℂ :=
  Gamma (v / 2) ^ 2 * (Gamma (v / 2 + 1 / 3))⁻¹ * (Gamma (v / 2 + 2 / 3))⁻¹

/-- Gauss triplication in the form `Γ(v/2)³ Γ(3v/2)⁻¹ = C · 3^{-3v/2} · R(v)`, valid whenever
`v/2` is not a pole of `Γ`. -/
theorem gamma_cube_mul_inv_gamma_triple (v : ℂ) (hv : ∀ m : ℕ, v / 2 ≠ -m) :
    Gamma (v / 2) ^ 3 * (Gamma (3 * v / 2))⁻¹
      = (multGammaProd 3 1 : ℂ) * (3 : ℂ) ^ (-(3 * v / 2)) * tripR v := by
  have hG := gauss_multiplication_complex (n := 3) (by norm_num) (3 * v / 2)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at hG
  have e0 : (3 * v / 2 + ((0 : ℕ) : ℂ)) / ((3 : ℕ) : ℂ) = v / 2 := by push_cast; ring
  have e1 : (3 * v / 2 + ((1 : ℕ) : ℂ)) / ((3 : ℕ) : ℂ) = v / 2 + 1 / 3 := by push_cast; ring
  have e2 : (3 * v / 2 + ((2 : ℕ) : ℂ)) / ((3 : ℕ) : ℂ) = v / 2 + 2 / 3 := by push_cast; ring
  rw [e0, e1, e2] at hG
  have hC : (multGammaProd 3 1 : ℂ) ≠ 0 := by
    exact_mod_cast (multGammaProd_pos (n := 3) (by norm_num) one_pos).ne'
  have h3 : ((3 : ℕ) : ℂ) ^ (3 * v / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push_cast; norm_num
  have hΓ : Gamma (v / 2) ≠ 0 := by
    intro h; rcases (Gamma_eq_zero_iff _).mp h with ⟨m, hm⟩; exact hv m hm
  have hinv : (Gamma (3 * v / 2))⁻¹
      = (multGammaProd 3 1 : ℂ) * ((3 : ℕ) : ℂ) ^ (-(3 * v / 2))
        * ((Gamma (v / 2))⁻¹ * (Gamma (v / 2 + 1 / 3))⁻¹ * (Gamma (v / 2 + 2 / 3))⁻¹) := by
    rw [hG, cpow_neg]
    field_simp
  rw [hinv, tripR]
  push_cast
  field_simp

/-- The same identity for `Γ_ℝ`: the powers of `π` cancel,
`Γ_ℝ(v)³ Γ_ℝ(3v)⁻¹ = C · 3^{-3v/2} · R(v)`. -/
theorem gammaR_cube_mul_inv_gammaR_triple (v : ℂ) (hv : ∀ m : ℕ, v / 2 ≠ -m) :
    Gammaℝ v ^ 3 * (Gammaℝ (3 * v))⁻¹
      = (multGammaProd 3 1 : ℂ) * (3 : ℂ) ^ (-(3 * v / 2)) * tripR v := by
  rw [← gamma_cube_mul_inv_gamma_triple v hv, Gammaℝ_def, Gammaℝ_def]
  have hπ : ((Real.pi : ℂ) ^ (-(3 * v) / 2)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => absurd h.1 (by exact_mod_cast Real.pi_ne_zero)
  have hcube : ((Real.pi : ℂ) ^ (-v / 2)) ^ 3 = (Real.pi : ℂ) ^ (-(3 * v) / 2) := by
    rw [← cpow_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, hcube, mul_inv]
  field_simp

/-- The constant of Gauss multiplication cancels between `v` and `1 - v`:
`Γ_ℝ(v)³Γ_ℝ(3v)⁻¹ · 3^{3v/2} · R(1 - v) = Γ_ℝ(1-v)³Γ_ℝ(3(1-v))⁻¹ · 3^{3(1-v)/2} · R(v)`. -/
theorem triplication_twist_symmetric (v : ℂ) (hv : ∀ m : ℕ, v / 2 ≠ -m)
    (hv' : ∀ m : ℕ, (1 - v) / 2 ≠ -m) :
    Gammaℝ v ^ 3 * (Gammaℝ (3 * v))⁻¹ * (3 : ℂ) ^ (3 * v / 2) * tripR (1 - v)
      = Gammaℝ (1 - v) ^ 3 * (Gammaℝ (3 * (1 - v)))⁻¹ * (3 : ℂ) ^ (3 * (1 - v) / 2)
          * tripR v := by
  rw [gammaR_cube_mul_inv_gammaR_triple v hv, gammaR_cube_mul_inv_gammaR_triple (1 - v) hv']
  have h1 : (3 : ℂ) ^ (-(3 * v / 2)) * (3 : ℂ) ^ (3 * v / 2) = 1 := by
    rw [← cpow_add _ _ (by norm_num)]; simp
  have h2 : (3 : ℂ) ^ (-(3 * (1 - v) / 2)) * (3 : ℂ) ^ (3 * (1 - v) / 2) = 1 := by
    rw [← cpow_add _ _ (by norm_num)]; simp
  linear_combination ((multGammaProd 3 1 : ℂ) * tripR v * tripR (1 - v)) * (h1 - h2)

/-- **Triplication twist.** With `w = 3v - 1`, the quotient of the Mellin multiplier
`3^{w - 1/2} Γ_ℝ(v)³/Γ_ℝ(1 - v)³` of the `Γ_ℝ(s)³` Hankel transform (cube-root chart) by the
sine-transform multiplier `Γ_ℝ(3v)/Γ_ℝ(3 - 3v)` is `R(v)/R(1 - v)`, in cleared form:
`3^{w - 1/2} · Γ_ℝ(v)³Γ_ℝ(3v)⁻¹ · R(1 - v) = Γ_ℝ(1-v)³Γ_ℝ(3(1-v))⁻¹ · R(v)`. -/
theorem triplication_twist (v : ℂ) (hv : ∀ m : ℕ, v / 2 ≠ -m)
    (hv' : ∀ m : ℕ, (1 - v) / 2 ≠ -m) :
    (3 : ℂ) ^ ((3 * v - 1) - 1 / 2) * (Gammaℝ v ^ 3 * (Gammaℝ (3 * v))⁻¹) * tripR (1 - v)
      = Gammaℝ (1 - v) ^ 3 * (Gammaℝ (3 * (1 - v)))⁻¹ * tripR v := by
  have h := triplication_twist_symmetric v hv hv'
  have e : (3 : ℂ) ^ ((3 * v - 1) - 1 / 2) * (3 : ℂ) ^ (3 * (1 - v) / 2)
      = (3 : ℂ) ^ (3 * v / 2) := by
    rw [← cpow_add _ _ (by norm_num)]; congr 1; ring
  have h3 : (3 : ℂ) ^ (3 * (1 - v) / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; norm_num
  apply mul_right_cancel₀ h3
  calc (3 : ℂ) ^ ((3 * v - 1) - 1 / 2) * (Gammaℝ v ^ 3 * (Gammaℝ (3 * v))⁻¹) * tripR (1 - v)
          * (3 : ℂ) ^ (3 * (1 - v) / 2)
        = Gammaℝ v ^ 3 * (Gammaℝ (3 * v))⁻¹ * ((3 : ℂ) ^ ((3 * v - 1) - 1 / 2)
            * (3 : ℂ) ^ (3 * (1 - v) / 2)) * tripR (1 - v) := by ring
    _ = Gammaℝ v ^ 3 * (Gammaℝ (3 * v))⁻¹ * (3 : ℂ) ^ (3 * v / 2) * tripR (1 - v) := by rw [e]
    _ = _ := by rw [h]; ring

end RHTower.DegreeThreeHankel
