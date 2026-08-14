import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquareFunctionalReflection
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.GammaVerticalUniformDecay

/-!
# Gamma decay on Ingham's fixed left contour

Line `Re z=-3/4` is shifted once to positive line `Re=1/4`; bounded-width Gamma comparison moves
that to exactly solvable half-line.  This yields explicit exponential decay needed for horizontal
and vertical contour domination.
-/

noncomputable section

open Complex

namespace RHTower.Sieve

/-- Gamma modulus on a real vertical line depends only on absolute ordinate. -/
theorem norm_Gamma_real_add_im_eq_abs (sigma t : ℝ) :
    ‖Complex.Gamma ((sigma : ℂ) + (t : ℂ) * I)‖ =
      ‖Complex.Gamma ((sigma : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have htneg : t < 0 := lt_of_not_ge ht
    have hconj :
        ((sigma : ℂ) + ((|t| : ℝ) : ℂ) * I) =
          (starRingEnd ℂ) ((sigma : ℂ) + (t : ℂ) * I) := by
      apply Complex.ext <;> simp [abs_of_neg htneg]
    rw [hconj, Complex.Gamma_conj, Complex.norm_conj]

/-- Explicit exponential bound on Gamma along fixed line `Re z=-3/4`. -/
theorem norm_Gamma_left_threeQuarter_le_exp {t : ℝ} (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((-3 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp 2 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(Real.pi * |t| / 2)) := by
  let y : ℝ := |t|
  have hy : 1 ≤ y := ht
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hz0 : ((-3 / 4 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hrec := Complex.Gamma_add_one ((-3 / 4 : ℂ) + (y : ℂ) * I) hz0
  have harg : ((-3 / 4 : ℂ) + (y : ℂ) * I) + 1 =
      (1 / 4 : ℂ) + (y : ℂ) * I := by ring
  have hrecNorm :
      ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖ =
        ‖(-3 / 4 : ℂ) + (y : ℂ) * I‖ *
          ‖Complex.Gamma ((-3 / 4 : ℂ) + (y : ℂ) * I)‖ := by
    rw [← harg, hrec, norm_mul]
  have hden : 1 ≤ ‖(-3 / 4 : ℂ) + (y : ℂ) * I‖ := by
    calc
      1 ≤ y := hy
      _ = |(((-3 / 4 : ℂ) + (y : ℂ) * I).im)| := by simp [abs_of_pos hy0]
      _ ≤ ‖(-3 / 4 : ℂ) + (y : ℂ) * I‖ := Complex.abs_im_le_norm _
  have hquarter_le :
      ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖ ≤
        Real.exp 2 * ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by
    have hratio := RHTower.norm_Gamma_vertical_ratio_le_exp_two
      (a := (1 : ℝ) / 4) (b := (1 : ℝ) / 2) (y := y)
      (by norm_num) (by norm_num) (by norm_num) hy
    have hhalf0 : 0 < ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := by
      apply norm_pos_iff.mpr
      apply Complex.Gamma_ne_zero
      intro m hm
      have him := congrArg Complex.im hm
      simp at him
      linarith
    exact (div_le_iff₀ hhalf0).mp (by simpa using hratio)
  have hhalf :=
    (GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_bounds y).2
  rw [show (-3 / 4 : ℂ) = (((-3 / 4 : ℝ) : ℂ)) by norm_num]
  rw [norm_Gamma_real_add_im_eq_abs (-3 / 4) t]
  calc
    ‖Complex.Gamma (((-3 / 4 : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ =
        ‖Complex.Gamma ((-3 / 4 : ℂ) + (y : ℂ) * I)‖ := by
      congr 2
      dsimp only [y]
      norm_num
    _ ≤
        ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖ := by
      rw [hrecNorm]
      exact le_mul_of_one_le_left (norm_nonneg _) hden
    _ ≤ Real.exp 2 * ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ := hquarter_le
    _ ≤ Real.exp 2 *
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * y / 2))) := by
      rw [abs_of_nonneg (abs_nonneg t)] at hhalf
      gcongr
    _ = Real.exp 2 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(Real.pi * |t| / 2)) := by
      dsimp only [y]
      ring

/-- Arbitrary-power Gamma decay, uniform across full Ingham rectangle strip `[-3/4,2]`. -/
theorem exists_uniform_bound_norm_Gamma_ingham_strip (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u T : ℝ, -3 / 4 ≤ u → u ≤ 2 → 1 ≤ |T| →
      ‖Complex.Gamma ((u : ℂ) + (T : ℂ) * I)‖ ≤ C / |T| ^ k := by
  obtain ⟨C, hC, hbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_uniform_bound_norm_Gamma_vertical
      (M := (3 : ℝ)) (by norm_num) k
  refine ⟨C, hC, ?_⟩
  intro u T huLow huHigh hT
  let y : ℝ := |T|
  have hy : 1 ≤ y := hT
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hupos : 0 < u + 1 := by linarith
  have huM : u + 1 ≤ 3 := by linarith
  have hshiftBound :
      ‖Complex.Gamma (((u + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C / y ^ k :=
    hbound (u + 1) y hupos huM hy
  have hz0 : (u : ℂ) + (T : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    rw [him] at hT
    norm_num at hT
  have hrec := Complex.Gamma_add_one ((u : ℂ) + (T : ℂ) * I) hz0
  have harg : ((u : ℂ) + (T : ℂ) * I) + 1 =
      ((u + 1 : ℝ) : ℂ) + (T : ℂ) * I := by
    push_cast
    ring
  have hrecNorm :
      ‖Complex.Gamma (((u + 1 : ℝ) : ℂ) + (T : ℂ) * I)‖ =
        ‖(u : ℂ) + (T : ℂ) * I‖ *
          ‖Complex.Gamma ((u : ℂ) + (T : ℂ) * I)‖ := by
    rw [← harg, hrec, norm_mul]
  have hden : 1 ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := by
    calc
      1 ≤ |T| := hT
      _ = |(((u : ℂ) + (T : ℂ) * I).im)| := by simp
      _ ≤ ‖(u : ℂ) + (T : ℂ) * I‖ := Complex.abs_im_le_norm _
  calc
    ‖Complex.Gamma ((u : ℂ) + (T : ℂ) * I)‖ ≤
        ‖Complex.Gamma (((u + 1 : ℝ) : ℂ) + (T : ℂ) * I)‖ := by
      rw [hrecNorm]
      exact le_mul_of_one_le_left (norm_nonneg _) hden
    _ = ‖Complex.Gamma (((u + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
      norm_Gamma_real_add_im_eq_abs (u + 1) T
    _ ≤ C / y ^ k := hshiftBound
    _ = C / |T| ^ k := rfl

end RHTower.Sieve
