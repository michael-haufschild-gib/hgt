import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUnramifiedSquareFactorsThroughTheUntwistedSeries

/-!
# Absolute convergence of the untwisted squarefree theta series

Its coefficient is the signed theta-square weight on squarefree ideals prime
to three, and zero elsewhere. The coefficient has norm at most one. Absolute
ideal-zeta convergence supplies a uniform majorant on every smaller right
half-plane, proving holomorphy of the actual arithmetic series on `Re w>1`.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicJacobi

/-- The signed theta coefficient supported on squarefree ideals prime to `3`. -/
def untwistedSquarefreeCoefficient (A : Ideal O) : ℂ :=
  if Squarefree A ∧ primaryIdealGenerator A ≠ 0 then thetaSquareWeight A else 0

theorem norm_untwistedSquarefreeCoefficient_le (A : Ideal O) :
    ‖untwistedSquarefreeCoefficient A‖ ≤ 1 := by
  unfold untwistedSquarefreeCoefficient
  split_ifs with h
  · rw [norm_thetaSquareWeight A h.2 h.1]
  · simp only [norm_zero, zero_le_one]

theorem untwistedSquarefreeCoefficient_of_bad (A : Ideal O)
    (hA : primaryIdealGenerator A = 0) : untwistedSquarefreeCoefficient A = 0 := by
  simp only [untwistedSquarefreeCoefficient, hA, ne_eq, not_true_eq_false, and_false, if_false]

theorem twistedSquarefreeSeries_one_eq (w : ℂ) :
    twistedSquarefreeSeries 1 w = ∑' A : Ideal O,
      unramifiedNormWeight w A * untwistedSquarefreeCoefficient A := by
  unfold twistedSquarefreeSeries
  apply tsum_congr
  intro A
  by_cases hsq : Squarefree A
  · rw [if_pos hsq]
    by_cases hA : primaryIdealGenerator A = 0
    · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, zero_mul]
    · rw [symbol_one_numerator _ (primaryIdealGenerator_spec A hA).2, map_one,
        one_pow, one_mul, untwistedSquarefreeCoefficient, if_pos ⟨hsq, hA⟩]
  · simp only [hsq, if_false, untwistedSquarefreeCoefficient, false_and, mul_zero]

theorem untwistedSquarefreeSeries_summable_norm (w : ℂ) (hw : 1 < w.re) :
    Summable (fun A : Ideal O =>
      ‖unramifiedNormWeight w A * untwistedSquarefreeCoefficient A‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun A => ?_)
    (unramifiedNormWeight_summable_norm w hw)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_untwistedSquarefreeCoefficient_le A)

/-- The actual untwisted arithmetic series is holomorphic in its absolute half-plane. -/
theorem twistedSquarefreeSeries_one_differentiableAt (w : ℂ) (hw : 1 < w.re) :
    DifferentiableAt ℂ (twistedSquarefreeSeries 1) w := by
  let a : ℝ := (1 + w.re) / 2
  have ha : 1 < a := by dsimp only [a]; linarith
  have haw : a < w.re := by dsimp only [a]; linarith
  have hopen : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsum := unramifiedNormWeight_summable_norm (a : ℂ) (by simpa using ha)
  have hd : DifferentiableOn ℂ (fun z => ∑' A : Ideal O,
      unramifiedNormWeight z A * untwistedSquarefreeCoefficient A) {z : ℂ | a < z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun A => ((unramifiedNormWeight_differentiable A).mul_const _).differentiableOn) hopen
    intro A z hz
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_untwistedSquarefreeCoefficient_le A)).trans
      (unramifiedNormWeight_norm_mono a z hz.le A)
  have heq : twistedSquarefreeSeries 1 = fun z => ∑' A : Ideal O,
      unramifiedNormWeight z A * untwistedSquarefreeCoefficient A :=
    funext twistedSquarefreeSeries_one_eq
  rw [heq]
  exact (hd w haw).differentiableAt (hopen.mem_nhds haw)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
