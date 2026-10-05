import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquarePerron
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullTwoTail

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
namespace RHTower.BAGTrace

/-- Arbitrary-order decay of the actual original contour line, uniform in damping. -/
theorem exists_dampedSquareContour_original_line_decay (j : ℕ) :
    ∃ C > 0, ∀ {ε b X : ℝ}, 0 < ε → ε < 1/16 →
      0 < b → b ≤ 1 → 0 < X → ∀ t : ℝ,
      ‖dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)‖ ≤
        C*X^(1+b)/b^3/(1+|t|)^j := by
  obtain ⟨A,hA,hM⟩ := exists_dampedSquareWindowMellin_rapidDecay j 1
  refine ⟨24*A,by positivity,?_⟩
  intro ε b X hε hε1 hb hb1 hX t
  have hm : ‖dampedSquareWindowMellin ((1+b : ℝ)+t*I)‖ ≤ A/(1+|t|)^j := by
    simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero,add_sub_cancel_left,abs_of_pos hb,add_im,mul_im,zero_add,
      mul_one] using hM ((1+b : ℝ)+t*I) (by simpa [abs_of_pos hb] using hb1)
  have hp : ‖(X : ℂ)^((1+b : ℝ)+t*I)‖ = X^(1+b) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX ((1+b : ℝ)+t*I)
  unfold dampedSquareContourIntegrand
  rw [← dampedSquareDirichlet_eq_continuation hε.le hε1 (by simp; linarith),
    norm_mul,norm_mul,hp]
  calc _ ≤ (24/b^3)*(A/(1+|t|)^j)*X^(1+b) := by
        gcongr
        exact norm_dampedSquareDirichlet_normalized_le hε hb hb1 t
    _ = _ := by ring

/-- Both infinite original-line tails are retained and controlled together. -/
theorem exists_dampedSquareContour_two_tail_bound (j : ℕ) (hj : 2 ≤ j) :
    ∃ C > 0, ∀ {ε b X T : ℝ}, 0 < ε → ε < 1/16 →
      0 < b → b ≤ 1 → 0 < X → 0 < T →
      ‖(∫ t : ℝ,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)) -
        ∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)‖ ≤
        C*X^(1+b)/b^3 * (T^(1-(j : ℝ))/((j : ℝ)-1)) := by
  obtain ⟨A,hA,hbound⟩ := exists_dampedSquareContour_original_line_decay j
  refine ⟨2*A,by positivity,?_⟩
  intro ε b X T hε hε1 hb hb1 hX hT
  have hint := integrable_dampedSquareContour_original_line hε.le hε1 hX
    (show 1 < 1+b by linarith)
  have hjR : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hpoint : ∀ t : ℝ, T ≤ |t| →
      ‖dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)‖ ≤
        (A*X^(1+b)/b^3)*|t|^(-(j : ℝ)) := by
    intro t ht
    have ht0 : 0 < |t| := hT.trans_le ht
    calc _ ≤ A*X^(1+b)/b^3/(1+|t|)^j := hbound hε hε1 hb hb1 hX t
      _ ≤ A*X^(1+b)/b^3/|t|^j := by gcongr; linarith
      _ = _ := by rw [Real.rpow_neg (abs_nonneg t),Real.rpow_natCast,div_eq_mul_inv]
  have h := RHTower.Sieve.norm_integral_sub_interval_le_powerTail hint
    (show 0 ≤ A*X^(1+b)/b^3 by positivity) hjR hT hpoint
  convert h using 1
  ring

end RHTower.BAGTrace
