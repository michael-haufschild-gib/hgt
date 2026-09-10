import GaloisForLFunctions.HTGeometry.PrincipalSquareRootDeriv

/-! Principal complex roots rotated into the left half-plane, for every order at least two. -/
open Complex Set
namespace RHTower.FokasLenells
noncomputable section

private theorem principal_root_re (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (z ^ (((m : ℝ)⁻¹ : ℝ) : ℂ)).re =
      Real.exp (Real.log ‖z‖ / m) * Real.cos (z.arg / m) := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add, Complex.log_re, Complex.log_im, div_eq_mul_inv]

private theorem principal_root_re_nonneg (m : ℕ) (hm : 2 ≤ m) (z : ℂ) :
    0 ≤ (z ^ (((m : ℝ)⁻¹ : ℝ) : ℂ)).re := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  by_cases hz : z = 0
  · subst z
    have he : (((m : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (inv_pos.mpr hm0))
    simp only [Complex.zero_cpow he, Complex.zero_re, le_refl]
  · rw [principal_root_re m z hz]
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · apply (le_div_iff₀ hm0).mpr
      nlinarith only [Complex.neg_pi_lt_arg z, Real.pi_pos, hmR]
    · apply (div_le_iff₀ hm0).mpr
      nlinarith only [Complex.arg_le_pi z, Real.pi_pos, hmR]

private theorem principal_root_re_pos (m : ℕ) (hm : 3 ≤ m) (z : ℂ) (hz : z ≠ 0) :
    0 < (z ^ (((m : ℝ)⁻¹ : ℝ) : ℂ)).re := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  rw [principal_root_re m z hz]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · apply (lt_div_iff₀ hm0).mpr
    nlinarith only [Complex.neg_pi_lt_arg z, Real.pi_pos, hmR]
  · apply (div_lt_iff₀ hm0).mpr
    nlinarith only [Complex.arg_le_pi z, Real.pi_pos, hmR]

/-- A parity-adjusted negative principal root, of order `n+2`. -/
def causalLeftPowerRoot (n : ℕ) (z : ℂ) : ℂ :=
  - (((-1 : ℂ)^(n+2) * z) ^ (((((n+2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ))

/-- Every complex number has this explicit left root of every order at least two. -/
theorem causalLeftPowerRoot_pow (n : ℕ) (z : ℂ) :
    (causalLeftPowerRoot n z)^(n+2) = z := by
  have hp : (((-1 : ℂ)^(n+2) * z) ^ (((((n+2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ))^(n+2) =
      (-1 : ℂ)^(n+2) * z := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      Complex.cpow_nat_inv_pow ((-1 : ℂ)^(n+2) * z) (by omega : n+2 ≠ 0)
  change (-_)^(n+2) = z
  rw [neg_pow, hp, ← mul_assoc, ← mul_pow]
  simp

/-- The selected root always lies in the closed left half-plane. -/
theorem causalLeftPowerRoot_re_nonpos (n : ℕ) (z : ℂ) :
    (causalLeftPowerRoot n z).re ≤ 0 :=
  neg_nonpos.mpr (principal_root_re_nonneg (n+2) (by omega) _)

/-- At every order at least three, a nonzero argument gives a strictly left root. -/
theorem causalLeftPowerRoot_re_neg (n : ℕ) (z : ℂˣ) :
    (causalLeftPowerRoot (n+1) z).re < 0 := by
  apply neg_neg_of_pos
  apply principal_root_re_pos (n+1+2) (by omega)
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) z.ne_zero

/-- The root's modulus satisfies the exact power identity. -/
theorem norm_causalLeftPowerRoot_pow (n : ℕ) (z : ℂ) :
    ‖causalLeftPowerRoot n z‖^(n+2) = ‖z‖ :=
  (norm_pow _ _).symm.trans (congrArg (fun w : ℂ => ‖w‖) (causalLeftPowerRoot_pow n z))

/-- The root vanishes exactly at zero. -/
theorem causalLeftPowerRoot_eq_zero_iff (n : ℕ) (z : ℂ) :
    causalLeftPowerRoot n z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hp := causalLeftPowerRoot_pow n z
    simpa only [h, zero_pow (by omega : n+2 ≠ 0)] using hp.symm
  · intro h
    subst z
    apply (pow_eq_zero_iff (by omega : n+2 ≠ 0)).mp
    exact causalLeftPowerRoot_pow n 0

/-- Every point of the unit disk has its explicit left root inside the same disk. -/
theorem norm_causalLeftPowerRoot_unitDisk (n : ℕ) (z : {z : ℂ // ‖z‖ ≤ 1}) :
    ‖causalLeftPowerRoot n z‖ ≤ 1 := by
  by_contra h
  have hp : 1 < ‖causalLeftPowerRoot n z‖^(n+2) :=
    one_lt_pow₀ (lt_of_not_ge h) (by omega)
  rw [norm_causalLeftPowerRoot_pow] at hp
  exact (not_lt_of_ge z.property) hp

end
end RHTower.FokasLenells
