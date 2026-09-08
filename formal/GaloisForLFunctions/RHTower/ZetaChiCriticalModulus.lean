import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# `χ` has modulus one on the critical line

For `s = 1/2 + iy`, `1 − s = conj s`, so `χ(1 − s) = conj χ(s)` and the identity `χ(s) χ(1 − s) = 1`
on the open strip gives `|χ(s)|² = 1`.
-/

open Complex

namespace RHTower

/-- `‖χ(1/2 + iy)‖ = 1`. -/
theorem norm_zetaChi_critical (y : ℝ) : ‖zetaChi ((1 / 2 : ℂ) + (y : ℂ) * I)‖ = 1 := by
  set s : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hconj : (1 : ℂ) - s = (starRingEnd ℂ) s := by
    apply Complex.ext
    · simp [hs]; norm_num
    · simp [hs]
  have hprod := zetaChi_mul_one_sub_of_mem_strip (s := s) (by rw [hre]; norm_num)
    (by rw [hre]; norm_num)
  rw [hconj, zetaChi_conj, Complex.mul_conj] at hprod
  have h1 : Complex.normSq (zetaChi s) = 1 := by exact_mod_cast hprod
  rw [Complex.normSq_eq_norm_sq] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h1

end RHTower
