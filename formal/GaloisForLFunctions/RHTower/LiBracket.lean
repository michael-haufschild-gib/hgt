import GaloisForLFunctions.RHTower.LiTermBound
noncomputable section

/-!
# The generating function of one paired Li summand

Summing `liTerm w n = 2 - wⁿ - w⁻ⁿ` against `zⁿ` gives the rational function

`Σ_n (2 - wⁿ - w⁻ⁿ) zⁿ = 2/(1-z) - 1/(1-wz) - 1/(1-z/w) = z(z+1)(w-1)² / ((z-1)(z-w)(wz-1))`,

whose poles are `z = 1`, `z = w` and `z = 1/w` and whose numerator carries the factor `(w-1)²`.
That factor is what makes the sum over the Xi zeros converge: `w_ρ - 1 = -1/ρ`.

The residue at `z = w` is `w`, and (by the symmetry `w ↦ w⁻¹` of `liTerm`) the residue at `z = 1/w`
is `1/w`.  Both are nonzero, and they never cancel between different zeros, which is why a zero off
the critical line produces a genuine singularity strictly inside the unit disc.
-/

open Complex
namespace RHTower

/-- The closed form of the generating function of one paired Li summand:
`Σ_n (2 - wⁿ - w⁻ⁿ) zⁿ = z(z+1)(w-1)² / ((z-1)(z-w)(wz-1))`. -/
def liBracket (w z : ℂ) : ℂ := z * (z + 1) * (w - 1) ^ (2 : ℕ) / ((z - 1) * (z - w) * (w * z - 1))

theorem hasSum_liTerm_mul_pow {w z : ℂ} (hw : w ≠ 0) (hz : ‖z‖ < 1)
    (h1 : ‖w * z‖ < 1) (h2 : ‖z / w‖ < 1) :
    HasSum (fun n => liTerm w n * z ^ n) (liBracket w z) := by
  have g0 : HasSum (fun n : ℕ => z ^ n) (1 - z)⁻¹ := hasSum_geometric_of_norm_lt_one hz
  have g1 : HasSum (fun n : ℕ => (w * z) ^ n) (1 - w * z)⁻¹ := hasSum_geometric_of_norm_lt_one h1
  have g2 : HasSum (fun n : ℕ => (z / w) ^ n) (1 - z / w)⁻¹ := hasSum_geometric_of_norm_lt_one h2
  have hcomb : HasSum (fun n : ℕ => 2 * z ^ n - (w * z) ^ n - (z / w) ^ n)
      (2 * (1 - z)⁻¹ - (1 - w * z)⁻¹ - (1 - z / w)⁻¹) :=
    ((g0.mul_left 2).sub g1).sub g2
  have hfun : ∀ n : ℕ, 2 * z ^ n - (w * z) ^ n - (z / w) ^ n = liTerm w n * z ^ n := by
    intro n
    have hpow : z ^ n / w ^ n = (w⁻¹) ^ n * z ^ n := by
      rw [inv_pow, div_eq_mul_inv]
      ring
    rw [liTerm, mul_pow, div_pow, sub_mul, sub_mul, hpow]
  have hval : 2 * (1 - z)⁻¹ - (1 - w * z)⁻¹ - (1 - z / w)⁻¹ = liBracket w z := by
    have hz1 : (1 : ℂ) - z ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [← h] at hz
      simp at hz
    have hwz : (1 : ℂ) - w * z ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [← h] at h1
      simp at h1
    have hzw : (1 : ℂ) - z / w ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [← h] at h2
      simp at h2
    have hzw' : z - w ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      exact hzw (by rw [h, div_self hw, sub_self])
    have hwz' : w * z - 1 ≠ 0 := fun h => hwz (by rw [sub_eq_zero] at h ⊢; exact h.symm)
    have hz1' : z - 1 ≠ 0 := fun h => hz1 (by rw [sub_eq_zero] at h ⊢; exact h.symm)
    have hwmz : w - z ≠ 0 := fun h => hzw' (by rw [sub_eq_zero] at h ⊢; exact h.symm)
    have hD : (z - 1) * (z - w) * (w * z - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hz1' hzw') hwz'
    have k1 : (1 - z)⁻¹ * (z - 1) = -1 := by
      rw [show z - 1 = -(1 - z) by ring, mul_neg, inv_mul_cancel₀ hz1]
    have k2 : (1 - w * z)⁻¹ * (w * z - 1) = -1 := by
      rw [show w * z - 1 = -(1 - w * z) by ring, mul_neg, inv_mul_cancel₀ hwz]
    have k3 : (1 - z / w)⁻¹ * (z - w) = -w := by
      have hrw : (1 : ℂ) - z / w = (w - z) / w := by field_simp
      rw [hrw, inv_div, show z - w = -(w - z) by ring, mul_neg, div_mul_cancel₀ _ hwmz]
    rw [liBracket, eq_div_iff hD]
    have hAD : (2 * (1 - z)⁻¹ - (1 - w * z)⁻¹ - (1 - z / w)⁻¹) *
          ((z - 1) * (z - w) * (w * z - 1))
        = 2 * ((1 - z)⁻¹ * (z - 1)) * ((z - w) * (w * z - 1))
          - ((1 - w * z)⁻¹ * (w * z - 1)) * ((z - 1) * (z - w))
          - ((1 - z / w)⁻¹ * (z - w)) * ((z - 1) * (w * z - 1)) := by ring
    rw [hAD, k1, k2, k3]
    ring
  rw [← hval]
  exact hcomb.congr_fun fun n => (hfun n).symm

end RHTower
