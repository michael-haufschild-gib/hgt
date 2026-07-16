import GaloisForLFunctions.RHTower.BernsteinEllipseRigidity

/-!
# Strict mixed-mode gap on a Bernstein ellipse

Two nonreal affine Bernstein modes of the same amplitude can jointly attain the squared maximal
amplitude only if their unique maximizing phases agree.  Distinct phases therefore give a
uniform strict gap on the unit circle.
-/

open Complex MeasureTheory
open scoped Interval Real

namespace RHTower

noncomputable section

/-- The reflected product appearing in a Gutzmer cross term. -/
def reflectedBernsteinProduct (u v w : ℂ) : ℂ :=
  (1 - u + u * w) * (1 - star v + star v * star w)

lemma norm_reflectedBernsteinProduct {u v w : ℂ} :
    ‖reflectedBernsteinProduct u v w‖ =
      ‖1 - u + u * w‖ * ‖1 - v + v * w‖ := by
  rw [reflectedBernsteinProduct, norm_mul]
  congr 1
  calc
    ‖1 - star v + star v * star w‖ = ‖star (1 - v + v * w)‖ := by
      congr 1
      simp
    _ = ‖1 - v + v * w‖ := norm_star _

lemma norm_affineBernsteinBase_le_amplitude
    (u w : ℂ) (hw : ‖w‖ = 1) :
    ‖1 - u + u * w‖ ≤ ‖u‖ + ‖1 - u‖ := by
  calc
    ‖1 - u + u * w‖ ≤ ‖1 - u‖ + ‖u * w‖ := norm_add_le _ _
    _ = ‖u‖ + ‖1 - u‖ := by rw [norm_mul, hw, mul_one, add_comm]

/-- Distinct maximizing phases force every reflected mixed product strictly below `B^2`. -/
theorem norm_reflectedBernsteinProduct_lt_sq_of_phase_ne
    {u v w : ℂ} {B : ℝ}
    (huim : u.im ≠ 0) (hvim : v.im ≠ 0)
    (huB : ‖u‖ + ‖1 - u‖ = B)
    (hvB : ‖v‖ + ‖1 - v‖ = B)
    (hphase : bernsteinEllipsePhase u ≠ bernsteinEllipsePhase v)
    (hw : ‖w‖ = 1) :
    ‖reflectedBernsteinProduct u v w‖ < B ^ 2 := by
  have hB : 0 < B := by
    rw [← huB]
    exact add_pos (norm_pos_iff.mpr (by
      intro hu
      rw [hu] at huim
      exact huim rfl)) (norm_pos_iff.mpr (by
        intro hsub
        have hu1 : u = 1 := (sub_eq_zero.mp hsub).symm
        rw [hu1] at huim
        exact huim rfl))
  let x : ℝ := ‖1 - u + u * w‖
  let y : ℝ := ‖1 - v + v * w‖
  have hx : x ≤ B := by
    dsimp only [x]
    rw [← huB]
    exact norm_affineBernsteinBase_le_amplitude u w hw
  have hy : y ≤ B := by
    dsimp only [y]
    rw [← hvB]
    exact norm_affineBernsteinBase_le_amplitude v w hw
  have hxy : ‖reflectedBernsteinProduct u v w‖ = x * y := by
    simpa only [x, y] using norm_reflectedBernsteinProduct (u := u) (v := v) (w := w)
  rw [hxy]
  apply lt_of_le_of_ne
  · nlinarith [norm_nonneg (1 - u + u * w), norm_nonneg (1 - v + v * w)]
  · intro heq
    have hxeq : x = B := by
      nlinarith [norm_nonneg (1 - u + u * w), norm_nonneg (1 - v + v * w)]
    have hyeq : y = B := by
      nlinarith [norm_nonneg (1 - u + u * w), norm_nonneg (1 - v + v * w)]
    have hwu : w = bernsteinEllipsePhase u :=
      bernsteinEllipsePhase_eq_of_norm_affine_eq_amplitude huim hw (by
        calc
          ‖1 - u + u * w‖ = x := rfl
          _ = B := hxeq
          _ = ‖u‖ + ‖1 - u‖ := huB.symm
          _ = ‖1 - u‖ + ‖u‖ := add_comm _ _)
    have hwv : w = bernsteinEllipsePhase v :=
      bernsteinEllipsePhase_eq_of_norm_affine_eq_amplitude hvim hw (by
        calc
          ‖1 - v + v * w‖ = y := rfl
          _ = B := hyeq
          _ = ‖v‖ + ‖1 - v‖ := hvB.symm
          _ = ‖1 - v‖ + ‖v‖ := add_comm _ _)
    exact hphase (hwu.symm.trans hwv)

/-- Compactness upgrades the pointwise strict mixed-mode inequality to a uniform gap. -/
theorem exists_uniform_reflectedBernsteinProduct_gap_of_phase_ne
    {u v : ℂ} {B : ℝ}
    (huim : u.im ≠ 0) (hvim : v.im ≠ 0)
    (huB : ‖u‖ + ‖1 - u‖ = B)
    (hvB : ‖v‖ + ‖1 - v‖ = B)
    (hphase : bernsteinEllipsePhase u ≠ bernsteinEllipsePhase v) :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ 2 ∧
      ∀ w : ℂ, ‖w‖ = 1 → ‖reflectedBernsteinProduct u v w‖ ≤ gamma := by
  let g : ℂ → ℝ := fun w => ‖reflectedBernsteinProduct u v w‖
  have hg : Continuous g := by
    dsimp only [g, reflectedBernsteinProduct]
    fun_prop
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  obtain ⟨w0, hw0, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    hne hg.continuousOn
  have hw0norm : ‖w0‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hw0
  refine ⟨g w0, norm_nonneg _,
    norm_reflectedBernsteinProduct_lt_sq_of_phase_ne
      huim hvim huB hvB hphase hw0norm, ?_⟩
  intro w hw
  exact hmax (by simpa only [Metric.mem_sphere, dist_zero_right] using hw)

/-- The normalized circle coefficient of the `n`-th reflected Bernstein cross power. -/
def reflectedBernsteinCrossMoment (u v : ℂ) (n : ℕ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ theta in (0 : ℝ)..2 * Real.pi,
      reflectedBernsteinProduct u v (circleMap 0 1 theta) ^ n

/-- A uniform circle bound passes unchanged to the normalized cross moment. -/
theorem norm_reflectedBernsteinCrossMoment_le_pow
    {u v : ℂ} {gamma : ℝ}
    (hgap : ∀ w : ℂ, ‖w‖ = 1 →
      ‖reflectedBernsteinProduct u v w‖ ≤ gamma) (n : ℕ) :
    ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n := by
  have hpoint : ∀ theta ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      ‖reflectedBernsteinProduct u v (circleMap 0 1 theta) ^ n‖ ≤ gamma ^ n := by
    intro theta _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hgap _ (by rw [norm_circleMap_zero (1 : ℝ) theta]; norm_num)) n
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [reflectedBernsteinCrossMoment, norm_mul]
  calc
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
          ‖∫ theta in (0 : ℝ)..2 * Real.pi,
            reflectedBernsteinProduct u v (circleMap 0 1 theta) ^ n‖
        ≤ ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
            (gamma ^ n * |2 * Real.pi - 0|) := by gcongr
    _ = gamma ^ n := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), sub_zero,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      field_simp [Real.pi_ne_zero]

end


end RHTower
