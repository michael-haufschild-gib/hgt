import GaloisForLFunctions.HTGeometry.StrelitzMaximumModulusPoint

/-!
# Closed maximum-modulus locus

The Strelitz maximum locus consists of all points at which the function attains its maximum on the
centered circle through that point.  It is closed for every continuous function and meets every
positive circle for an entire coefficient sum.  On its nonzero, nonvanishing part the Euler
logarithmic derivative is real.
-/

open Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- Points maximizing `|f|` on their centered circle. -/
def circleMaximumSet (f : ℂ → ℂ) : Set ℂ :=
  {z | ∀ w : ℂ, ‖w‖ = ‖z‖ → ‖f w‖ ≤ ‖f z‖}

/-- The centered-circle maximum locus of a continuous function is closed. -/
theorem isClosed_circleMaximumSet {f : ℂ → ℂ} (hf : Continuous f) :
    IsClosed (circleMaximumSet f) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  change ¬ (∀ w : ℂ, ‖w‖ = ‖z‖ → ‖f w‖ ≤ ‖f z‖) at hz
  push Not at hz
  obtain ⟨w, hw, hlt⟩ := hz
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    have hw0 : w = 0 := norm_eq_zero.mp (by simpa using hw)
    subst w
    exact (lt_irrefl ‖f 0‖) hlt
  have hznorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let scale : ℂ → ℂ := fun y => ((‖y‖ / ‖z‖ : ℝ) : ℂ) * w
  have hscale : Continuous scale := by
    dsimp [scale]
    fun_prop
  have hscalez : scale z = w := by
    simp [scale, hznorm]
  have hleft : ContinuousAt (fun y => ‖f y‖) z := hf.norm.continuousAt
  have hright : ContinuousAt (fun y => ‖f (scale y)‖) z :=
    (hf.comp hscale).norm.continuousAt
  have hevent : ∀ᶠ y : ℂ in nhds z, ‖f y‖ < ‖f (scale y)‖ := by
    exact hleft.eventually_lt hright (by simpa [hscalez] using hlt)
  filter_upwards [hevent] with y hy
  change ¬ (∀ v : ℂ, ‖v‖ = ‖y‖ → ‖f v‖ ≤ ‖f y‖)
  intro hmax
  have hscalenorm : ‖scale y‖ = ‖y‖ := by
    change ‖(((‖y‖ / ‖z‖ : ℝ) : ℂ) * w)‖ = ‖y‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), hw]
    exact div_mul_cancel₀ ‖y‖ hznorm
  exact (not_le_of_gt hy) (hmax (scale y) hscalenorm)

/-- The maximum locus of an entire coefficient sum meets every positive centered circle. -/
theorem exists_mem_circleMaximumSet_of_pos
    (ha : EntireCoeffs a) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ circleMaximumSet (coeffFun a), ‖z‖ = r := by
  obtain ⟨z, hz, hmax⟩ := exists_max_on_circle ha hr
  refine ⟨z, ?_, hz⟩
  intro w hw
  let θ : ℝ := Complex.arg w
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    linarith
  have hwr : ‖w‖ = r := hw.trans hz
  have hcircle : circleMap 0 r θ = w := by
    rw [circleMap, zero_add, ← hwr]
    simpa [θ, mul_comm] using Complex.norm_mul_exp_arg_mul_I w
  rw [← hcircle]
  exact hmax θ

/-- A point in the maximum locus dominates the maximum term on its circle. -/
theorem maxTerm_le_norm_of_mem_circleMaximumSet
    (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖)
    (hmax : z ∈ circleMaximumSet (coeffFun a)) :
    maxTerm a ‖z‖ ≤ ‖coeffFun a z‖ := by
  apply maxTerm_le_norm_of_max_on_circle ha hz rfl
  intro θ
  apply hmax
  rw [norm_circleMap_zero, abs_of_pos hz]

/-- Euler logarithmic derivative is real on the nonzero, nonvanishing maximum locus. -/
theorem eulerLogDeriv_im_eq_zero_of_mem_circleMaximumSet
    (ha : EntireCoeffs a) {z : ℂ} (hz : z ≠ 0) (hfz : coeffFun a z ≠ 0)
    (hmax : z ∈ circleMaximumSet (coeffFun a)) :
    (eulerLogDeriv (coeffFun a) z).im = 0 := by
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  apply im_mul_deriv_div_eq_zero_of_max_on_circle ha hznorm rfl hfz
  intro θ
  apply hmax
  rw [norm_circleMap_zero, abs_of_pos hznorm]

end

end GaloisForLFunctions.HTGeometry
