import GaloisForLFunctions.goldbach.LiLiu.ArithmeticKernel
import GaloisForLFunctions.goldbach.LiLiu.MellinWeight
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.RHTower.WeilLagFunctionInteger

/-! # The character contour under local GRH

On a fixed closed substrip to the right of zero the separated-zero estimate
bounds every nonprincipal logarithmic derivative by a constant times
(1+|t|)¹ᐟ⁴. Three powers of Mellin decay permit the shift from abscissa one.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex _root_.RHTower Set MeasureTheory MetaplecticMobiusDescent.CubicEisenstein
noncomputable section

/-- The bound is simultaneous for all nonprincipal characters of the given modulus. -/
theorem characterFeature_strip_bound {n : ℕ} (h : modulusGRH (n+1)) {a : ℝ} (ha : 0 < a) :
    ∃ A : ℝ, 0 < A ∧ ∀ χ : DirichletCharacter ℂ (n+1), χ ≠ 1 →
      ∀ s : ℂ, a ≤ s.re → s.re ≤ 1 →
        ‖characterFeature χ s‖ ≤ A * (1 + |s.im|) ^ (1/4 : ℝ) := by
  let q : ℝ := (n+1 : ℕ)
  let B := pfConst * (4 * (3*q) ^ (1/4 : ℝ))
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (by omega : 1 ≤ n+1)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hB : 0 < B := mul_pos pfConst_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _))
  refine ⟨B + 4 * (8+B)/a, by positivity, ?_⟩
  intro χ hχ s hs hs'
  let R := (1 + |s.im|) ^ (1/4 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow (by linarith only [abs_nonneg s.im]) (by norm_num)
  let L := pfConst * Real.log (q * (|s.im|+3))
  have hL : L ≤ B*R := by
    have hx : q*(|s.im|+3) ≤ (3*q)*(1+|s.im|) := by
      linarith only [mul_nonneg hq0.le (abs_nonneg s.im)]
    have hv := log_le_four_rpow_quarter (mul_nonneg hq0.le (by positivity : 0 ≤ |s.im|+3))
    have hw := Real.rpow_le_rpow (mul_nonneg hq0.le (by positivity)) hx (by norm_num : (0:ℝ) ≤ 1/4)
    rw [Real.mul_rpow (by positivity) (by positivity)] at hw
    dsimp [L, B, R]
    calc
      _ ≤ pfConst * (4 * (q * (|s.im| + 3)) ^ (1/4 : ℝ)) := mul_le_mul_of_nonneg_left hv pfConst_pos.le
      _ ≤ pfConst * (4 * ((3*q) ^ (1/4 : ℝ) * (1+|s.im|) ^ (1/4 : ℝ))) := by gcongr
      _ = _ := by ring
  have hpos : 1 / 2 < (1 / 2 + s : ℂ).re := by norm_num; linarith only [ha, hs]
  have htop : (1 / 2 + s : ℂ).re ≤ 2 := by norm_num; linarith only [hs']
  have he := h.norm_logDeriv_le hχ hpos htop
  norm_num only [Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, zero_div, zero_add, add_sub_cancel_left] at he
  change ‖characterFeature χ s‖ ≤ L + 4 * (8+L) / s.re at he
  have hnum : 4 * (8+L) ≤ 4*(8+B)*R := by linarith only [hL, hR]
  have hfrac : 4*(8+L)/s.re ≤ 4*(8+B)*R/a :=
    div_le_div₀ (by positivity) hnum ha hs
  exact he.trans (by linarith only [hL, hfrac])

def characterIntegrand {N : ℕ} [NeZero N] (φ : TestWeight) (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ s * mellin (companion φ) s * characterFeature χ s

/-- The absolutely convergent character contour can be moved to any positive line ≤ 1. -/
theorem character_contour_shift {n : ℕ} (φ : TestWeight) (h : modulusGRH (n+1))
    {χ : DirichletCharacter ℂ (n+1)} (hχ : χ ≠ 1) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    (∫ t : ℝ, characterIntegrand φ χ ((a : ℂ) + t * I)) =
      ∫ t : ℝ, characterIntegrand φ χ (1 + t * I) := by
  obtain ⟨A, hA, hbound⟩ := characterFeature_strip_bound h ha
  obtain ⟨D, hD, hdec⟩ := compact_source_mellin_strip_decay _ _ _ (by norm_num)
    (companion_support φ) (companion_smooth φ) a 1 3
  let q : ℝ := ((n+1 : ℕ) : ℝ)
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (by omega : 1 ≤ n+1)
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  apply HTGeometry.integral_vertical_line_shift_of_decay (c₂ := (1 : ℝ)) (C := q*A*D)
  · intro s hs
    rw [uIcc_of_le ha'] at hs
    exact (((differentiableAt_id.const_cpow (Or.inl hn)).mul
      (mellin_companion_differentiable φ s)).mul
      (characterFeature_analyticAt h hχ (ha.trans_le hs.1)).differentiableAt)
  · intro s hs
    rw [uIcc_of_le ha'] at hs
    let r := 1 + |s.im|
    have hr : 1 ≤ r := by dsimp [r]; linarith only [abs_nonneg s.im]
    have hsq : 1 + s.im ^ 2 ≤ r ^ 2 := by dsimp [r]; nlinarith only [sq_abs s.im, abs_nonneg s.im]
    have hg := hbound χ hχ s hs.1 hs.2
    have hgr : ‖characterFeature χ s‖ ≤ A*r :=
      hg.trans (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1/4:ℝ) ≤ 1)).trans_eq
          (Real.rpow_one r)) hA.le)
    have hp : ‖((n+1 : ℕ) : ℂ) ^ s‖ ≤ q := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
      exact (Real.rpow_le_rpow_of_exponent_le hq hs.2).trans_eq (Real.rpow_one q)
    have hm : r^3 * ‖mellin (companion φ) s‖ ≤ D := by
      simpa only [Complex.re_add_im] using hdec s.re hs s.im
    rw [le_div_iff₀ (by positivity), characterIntegrand, norm_mul, norm_mul]
    calc
      _ ≤ q * ‖mellin (companion φ) s‖ * (A*r) * r^2 := by gcongr
      _ = q*A*(r^3 * ‖mellin (companion φ) s‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (mul_nonneg (zero_le_one.trans hq) hA.le)

#print axioms character_contour_shift
end
end GaloisForLFunctions.Goldbach.LiLiu
