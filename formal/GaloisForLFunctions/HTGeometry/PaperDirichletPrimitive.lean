import GaloisForLFunctions.HTGeometry.PaperDirichletTail

/-! # Uniformly bounded primitives of the exact Fourier kernels

Splitting at the inverse frequency separates a short interval controlled by
the kernel height from an oscillatory tail. The resulting bound is independent
of the Fourier cutoff.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Period

theorem dirichlet_even (N : ℕ) (t : ℝ) : dirichlet N (-t) = dirichlet N t := by
  induction N with
  | zero => simp [dirichlet, phase]
  | succ N ih =>
    rw [dirichlet_succ, dirichlet_succ, ih]
    simp only [ang, mul_neg, Real.cos_neg]

theorem dirichlet_periodic (N : ℕ) : Function.Periodic (dirichlet N) 1 := by
  intro t
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro k _
  exact phase_periodic k t

/-- The primitive starts at the seam and uses the literal symmetric kernel. -/
def dirichletPrimitive (N : ℕ) (t : ℝ) : ℂ := ∫ x in (0 : ℝ)..t, dirichlet N x

theorem dirichletPrimitive_zero (N : ℕ) : dirichletPrimitive N 0 = 0 := by
  simp [dirichletPrimitive]

theorem dirichletPrimitive_odd (N : ℕ) (t : ℝ) :
    dirichletPrimitive N (-t) = -dirichletPrimitive N t := by
  unfold dirichletPrimitive
  have h := intervalIntegral.integral_comp_neg (dirichlet N) (a := 0) (b := t)
  simp only [dirichlet_even, neg_zero] at h
  rw [intervalIntegral.integral_symm (a := -t) (b := 0), ← h]

/-- A single frequency-independent bound on the closed positive half-period. -/
theorem norm_dirichletPrimitive_half_le (N : ℕ) (t : Icc (0 : ℝ) (1 / 2)) :
    ‖dirichletPrimitive N t.val‖ ≤ 2 := by
  let M : ℝ := 2 * (N : ℝ) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbasic (x : Icc (0 : ℝ) (1 / 2)) : ‖dirichletPrimitive N x.val‖ ≤ M * x.val := by
    simpa only [dirichletPrimitive, sub_zero, abs_of_nonneg x.property.1] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := x.val) (fun y _ => dirichlet_bound N y))
  by_cases hN : N = 0
  · have h := hbasic t
    subst N
    simp only [M, Nat.cast_zero, mul_zero, zero_add, one_mul] at h
    linarith [t.property.2]
  have hNpos : 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  let a : ℝ := 1 / M
  have ha0 : 0 < a := one_div_pos.mpr hM
  have ha2 : a ≤ 1 / 2 := by
    apply (div_le_iff₀ hM).mpr
    dsimp [M]
    linarith
  have hMa : M * a = 1 := by dsimp [a]; field_simp
  by_cases hta : t.val ≤ a
  · calc
      ‖dirichletPrimitive N t.val‖ ≤ M * t.val := hbasic t
      _ ≤ M * a := mul_le_mul_of_nonneg_left hta hM.le
      _ ≤ 2 := by rw [hMa]; norm_num
  have hat : a ≤ t.val := (lt_of_not_ge hta).le
  have hsinpos : 0 < Real.sin (π * a) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha0) (by nlinarith [Real.pi_pos])
  have hsin : a ≤ Real.sin (π * a) := by
    have hs := sin_posabs (q := π * a) (by
      rw [abs_of_pos (mul_pos Real.pi_pos ha0)]
      nlinarith [Real.pi_pos])
    rw [abs_of_pos (mul_pos Real.pi_pos ha0), abs_of_pos hsinpos] at hs
    nlinarith [mul_le_mul_of_nonneg_right Real.two_le_pi ha0.le]
  have hden : 2 ≤ (M * π) * Real.sin (π * a) := by
    calc
      2 = (M * 2) * a := by nlinarith [hMa]
      _ ≤ (M * π) * Real.sin (π * a) := by gcongr; exact Real.two_le_pi
  have htail : ‖∫ x in a..t.val, dirichlet N x‖ ≤ 1 := by
    apply (norm_dirichlet_tail_le N ⟨a, ha0, ha2⟩ ⟨t.val, hat, t.property.2⟩).trans
    apply (div_le_one (by positivity : 0 < (M * π) * Real.sin (π * a))).mpr
    exact hden
  have hsplit : dirichletPrimitive N t.val =
      dirichletPrimitive N a + ∫ x in a..t.val, dirichlet N x := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((dirichlet_cont N).intervalIntegrable _ _)
      ((dirichlet_cont N).intervalIntegrable _ _)).symm
  rw [hsplit]
  have hnear := hbasic ⟨a, ha0.le, ha2⟩
  change ‖dirichletPrimitive N a‖ ≤ M * a at hnear
  rw [hMa] at hnear
  exact (norm_add_le _ _).trans (by linarith)

/-- The same bound holds on both sides of the seam. -/
theorem norm_dirichletPrimitive_center_le (N : ℕ) (t : Icc (-1 / 2 : ℝ) (1 / 2)) :
    ‖dirichletPrimitive N t.val‖ ≤ 2 := by
  by_cases ht : 0 ≤ t.val
  · exact norm_dirichletPrimitive_half_le N ⟨t.val, ht, t.property.2⟩
  · have h := norm_dirichletPrimitive_half_le N ⟨-t.val, by constructor <;> linarith [t.property.1]⟩
    simpa only [dirichletPrimitive_odd, norm_neg] using h

end GaloisForLFunctions.HTGeometry.FourierLLogL.Period
