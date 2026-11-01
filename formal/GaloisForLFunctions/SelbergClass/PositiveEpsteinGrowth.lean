import GaloisForLFunctions.LatticeSectionTheory.TheRectangularLatticeCount
import GaloisForLFunctions.RHTower.MellinOrderOneEnvelope

/-!
# Growth of rectangular Epstein completions

Exponential decay of both theta kernels bounds the entire part of the completed
Epstein function by an order-one envelope. The compact initial interval is
absorbed explicitly using monotonicity of the theta count.
-/

noncomputable section

open Complex Real
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.PositiveEpstein

private theorem rectTheta_le_at_one {y t : ℝ} (hy : y ≠ 0) (ht : 1 ≤ t) :
    rectTheta y t ≤ rectTheta y 1 := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  unfold rectTheta
  apply mul_le_mul (thetaSum_antitone zero_lt_one ht)
    (thetaSum_antitone (by simpa only [mul_one] using hy2)
      (mul_le_mul_of_nonneg_left ht hy2.le))
  · exact (one_le_thetaSum (mul_pos hy2 ht0)).trans' zero_le_one
  · exact (one_le_thetaSum zero_lt_one).trans' zero_le_one

/-- The theta tail has an exponential bound on the whole ray starting at one. -/
theorem rectTheta_exponential_bound {y : ℝ} (hy : y ≠ 0) :
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(rectTheta y t : ℂ) - 1‖ ≤ C * Real.exp (-(b * t)) := by
  obtain ⟨b, C, hb, htail⟩ := rectTheta_sub_one_le hy
  let T : ℝ := max 1 (1 / y ^ 2)
  let A : ℝ := rectTheta y 1
  let C' : ℝ := max (max C 0) (A * Real.exp (b * T))
  have hA : 0 ≤ A := (one_le_rectTheta hy zero_lt_one).trans' zero_le_one
  have hC' : 0 ≤ C' := (le_max_right C 0).trans (le_max_left _ _)
  refine ⟨C', b, hC', hb, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn : 0 ≤ rectTheta y t - 1 := sub_nonneg.mpr (one_le_rectTheta hy ht0)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hn]
  by_cases hT : T ≤ t
  · exact (htail t hT).2.trans (mul_le_mul_of_nonneg_right
      ((le_max_left C 0).trans (le_max_left _ _)) (Real.exp_pos _).le)
  · have htT : t ≤ T := (lt_of_not_ge hT).le
    have hmono : rectTheta y t - 1 ≤ A := by
      have h := rectTheta_le_at_one hy ht
      dsimp [A]
      linarith only [h]
    have he : 1 ≤ Real.exp (b * T - b * t) :=
      Real.one_le_exp (by nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr htT)])
    calc rectTheta y t - 1 ≤ A := hmono
      _ ≤ A * Real.exp (b * T - b * t) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he hA
      _ = (A * Real.exp (b * T)) * Real.exp (-(b * t)) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ C' * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- The entire part of every rectangular Epstein completion has order at most one. -/
theorem orderOneEnvelope_epsteinLambda_zero {y : ℝ} (hy : 0 < y) :
    OrderOneEnvelope (rectFEPair y hy).Λ₀ := by
  obtain ⟨C₁, b₁, hC₁, hb₁, h₁⟩ := rectTheta_exponential_bound hy.ne'
  obtain ⟨C₂, b₂, hC₂, hb₂, h₂⟩ :=
    rectTheta_exponential_bound (one_div_pos.mpr hy).ne'
  let C := max C₁ C₂
  let b := min b₁ b₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  have hb : 0 < b := lt_min hb₁ hb₂
  have hfirst (t : ℝ) (ht : 1 ≤ t) :
      ‖(rectFEPair y hy).f t - (rectFEPair y hy).f₀‖ ≤ C * Real.exp (-(b * t)) := by
    refine (h₁ t ht).trans (mul_le_mul (le_max_left _ _) ?_ (Real.exp_pos _).le hC)
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith only [ht]))
  have hsecond (t : ℝ) (ht : 1 ≤ t) :
      ‖(rectFEPair y hy).g t - (rectFEPair y hy).g₀‖ ≤ C * Real.exp (-(b * t)) := by
    refine (h₂ t ht).trans (mul_le_mul (le_max_right _ _) ?_ (Real.exp_pos _).le hC)
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith only [ht]))
  obtain ⟨C₀, q, hC₀, hq, htop, hhead⟩ :=
    RHTower.weakFEPair_f_modif_decay (rectFEPair y hy) hC hb
      (by norm_num [rectFEPair]) hfirst hsecond
  exact RHTower.mellin_orderOneEnvelope_of_decay _ hq hC₀ htop hhead

end GaloisForLFunctions.SelbergClass.PositiveEpstein
