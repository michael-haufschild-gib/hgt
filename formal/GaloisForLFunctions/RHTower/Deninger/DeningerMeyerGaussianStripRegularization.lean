import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerMellinReconstruction
import GaloisForLFunctions.RHTower.Deninger.DeningerCollarExchange

/-!+# Gaussian regularization of entire strip data

The admissible growth is exponential only in height, separately on each
closed strip. No bound in the horizontal direction is required. Gaussian
regularization converts precisely this class into actual Meyer sources.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

def DeningerVerticalExponential (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ C * Real.exp (B * |s.im|)

def deningerGaussianMellinRegularization (ε : ℝ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((ε : ℂ) * s^2) * F s

private theorem gaussian_polynomial_bound {ε : ℝ} (hε : 0 < ε) (B : ℝ) (K : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ,
      (1+y^2)^K * Real.exp (B*|y| - ε*y^2) ≤ D := by
  let d : ℝ := 1 + 2/ε
  refine ⟨d^K * (Nat.factorial K : ℝ) * Real.exp (1+B^2/(2*ε)), by positivity, ?_⟩
  intro y
  have hlin : B*|y| - ε/2*y^2 ≤ B^2/(2*ε) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*ε)).mpr
    have hq := sq_nonneg (ε*|y|-B)
    rw [sub_sq, mul_pow, sq_abs] at hq
    nlinarith
  have hmajor : 1+y^2 ≤ d*(1+ε/2*y^2) := by
    dsimp [d]
    have he : ε ≠ 0 := hε.ne'
    field_simp
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg y)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+y^2) hmajor K
  rw [mul_pow] at hp
  have hf := deningerPow_le_factorial_mul_exp K (1+ε/2*y^2)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1+ε/2*y^2)] at hf
  calc (1+y^2)^K * Real.exp (B*|y|-ε*y^2)
      ≤ (d^K * ((Nat.factorial K : ℝ) * Real.exp (1+ε/2*y^2))) *
          Real.exp (B*|y|-ε*y^2) := by
        gcongr
        exact hp.trans (mul_le_mul_of_nonneg_left hf (by positivity))
    _ = (d^K * (Nat.factorial K : ℝ)) *
        Real.exp ((1+ε/2*y^2)+(B*|y|-ε*y^2)) := by
      rw [Real.exp_add (1+ε/2*y^2) (B*|y|-ε*y^2)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith

theorem deningerGaussianMellinRegularization_entireRegular
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hg : DeningerVerticalExponential F) {ε : ℝ} (hε : 0 < ε) :
    DeningerEntireMellinRegular (deningerGaussianMellinRegularization ε F) := by
  intro α β
  refine ⟨fun s _ _ => ?_, fun a b _ _ K => ?_⟩
  · exact (((differentiableAt_id.pow 2).const_mul (ε : ℂ)).cexp).mul (hF s)
  · obtain ⟨C, B, hC, hB, hb⟩ := hg a b
    obtain ⟨D, hD, hd⟩ := gaussian_polynomial_bound hε B K
    let A := |a| + |b|
    refine ⟨C * Real.exp (ε*A^2) * D, fun s ha hb' => ?_⟩
    have hre : |s.re| ≤ A := by
      dsimp [A]
      rw [abs_le]
      constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b,
        neg_le_abs b, abs_nonneg a, abs_nonneg b]
    have hsq : s.re^2 ≤ A^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg s.re) hre 2
    have hn : ‖deningerGaussianMellinRegularization ε F s‖ ≤
        (C * Real.exp (ε*A^2)) * Real.exp (B*|s.im|-ε*s.im^2) := by
      rw [deningerGaussianMellinRegularization, norm_mul, Complex.norm_exp]
      have hex : ((ε : ℂ)*s^2).re = ε*(s.re^2-s.im^2) := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
      rw [hex]
      calc Real.exp (ε*(s.re^2-s.im^2)) * ‖F s‖
          ≤ Real.exp (ε*(A^2-s.im^2)) * (C*Real.exp (B*|s.im|)) := by
            gcongr
            exact hb s ha hb'
        _ = _ := by
          rw [mul_left_comm _ C, ← mul_assoc, mul_assoc C, ← Real.exp_add,
            mul_assoc C, ← Real.exp_add]
          congr 2
          ring
    apply (le_div_iff₀ (by positivity : 0 < (1+s.im^2)^K)).mpr
    calc ‖deningerGaussianMellinRegularization ε F s‖ * (1+s.im^2)^K
        ≤ (C*Real.exp (ε*A^2)) *
            ((1+s.im^2)^K * Real.exp (B*|s.im|-ε*s.im^2)) := by
          nlinarith [mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (1+s.im^2)^K)]
      _ ≤ (C*Real.exp (ε*A^2))*D :=
        mul_le_mul_of_nonneg_left (hd s.im) (by positivity)

end
end RHTower
