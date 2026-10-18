import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailReadoutDecay
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailMass
import Zeta23.Taper.Decay

/-! The actual smoothed tails have primitive energy of order `N⁻³`,
uniformly in the smoothing parameter. -/

open MeasureTheory Set Filter
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.Zeta23
noncomputable section
set_option autoImplicit false

def factorialMuntzTailPrimitiveBudget : ℝ := 32*(360*Real.exp 1)^2*Real.pi

theorem factorialMuntzTailPrimitiveBudget_pos : 0 < factorialMuntzTailPrimitiveBudget := by
  unfold factorialMuntzTailPrimitiveBudget
  positivity

private theorem primitive_weight_bound (τ : ℝ) :
    (1+|τ|)^2/(τ^2+1/4)^2 ≤ 32*(1+τ^2)⁻¹ := by
  have hd : 0 < (τ^2+1/4)^2 := by positivity
  have hn : (1+|τ|)^2 ≤ 2*(1+τ^2) := by
    nlinarith [sq_nonneg (|τ|-1), sq_abs τ]
  have hden : (1+τ^2)^2 ≤ 16*(τ^2+1/4)^2 := by
    nlinarith [sq_nonneg τ, sq_nonneg (τ^2)]
  calc
    _ ≤ (2*(1+τ^2))/(τ^2+1/4)^2 := div_le_div_of_nonneg_right hn hd.le
    _ ≤ 32/(1+τ^2) := (div_le_div_iff₀ hd (by positivity)).2 (by nlinarith)
    _ = _ := by rw [div_eq_mul_inv]

private theorem primitive_density_bound (n k : ℕ) (τ : ℝ) :
    ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (τ : ℂ)‖^2/(τ^2+1/4)^2 ≤
      32*(360*Real.exp 1/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ)))^2*
        (1+τ^2)⁻¹ := by
  let C := 360*Real.exp 1/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (τ : ℂ)‖ ≤
      C*(1+|τ|) := by
    convert factorialMuntzSmoothedTail_paperFT_decay n k τ using 1
    dsimp [C]
    ring
  calc
    _ ≤ (C*(1+|τ|))^2/(τ^2+1/4)^2 := by gcongr
    _ = C^2*((1+|τ|)^2/(τ^2+1/4)^2) := by ring
    _ ≤ C^2*(32*(1+τ^2)⁻¹) :=
      mul_le_mul_of_nonneg_left (primitive_weight_bound τ) (sq_nonneg C)
    _ = _ := by dsimp [C]; ring

private theorem primitive_density_continuous (n k : ℕ) :
    Continuous (fun τ : ℝ =>
      ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (τ : ℂ)‖^2/(τ^2+1/4)^2) := by
  have hi : Integrable (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) := by
    simpa only [sub_self, zero_mul, Complex.exp_zero, one_mul] using
      (factorialMuntzSmoothedTail_readout n k (1/2 : ℂ) (by norm_num)).1
  have hc := _root_.Zeta23.Taper.continuous_paperFT_ofReal hi
  apply Continuous.div (hc.norm.pow 2) (by fun_prop)
  intro τ
  positivity

theorem factorialMuntzSmoothedTail_primitive_integrable (n k : ℕ) :
    Integrable (fun τ : ℝ =>
      ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (τ : ℂ)‖^2/(τ^2+1/4)^2) := by
  refine (integrable_inv_one_add_sq.const_mul
    (32*(360*Real.exp 1/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ)))^2)).mono'
    (primitive_density_continuous n k).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro τ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact primitive_density_bound n k τ

theorem factorialMuntzSmoothedTail_primitive_mass_bound (n k : ℕ) :
    (∫ τ : ℝ, ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (τ : ℂ)‖^2/
      (τ^2+1/4)^2) ≤ factorialMuntzTailPrimitiveBudget/((n+1 : ℕ) : ℝ)^3 := by
  let C := 360*Real.exp 1/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ))
  calc
    _ ≤ ∫ τ : ℝ, 32*C^2*(1+τ^2)⁻¹ :=
      integral_mono_ae (factorialMuntzSmoothedTail_primitive_integrable n k)
        (integrable_inv_one_add_sq.const_mul (32*C^2))
        (Eventually.of_forall (primitive_density_bound n k))
    _ = 32*C^2*Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
    _ = _ := by
      dsimp [C, factorialMuntzTailPrimitiveBudget]
      simp only [div_pow, mul_pow,
        Real.sq_sqrt (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)]
      field_simp

/-- Relative primitive energy decays by two powers, for the actual smoothing
sequence whose nonzero physical mass was proved from exact phase cells. -/
theorem factorialMuntzSmoothedTail_primitive_mass_relative (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (∫ τ : ℝ, ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (τ : ℂ)‖^2/
        (τ^2+1/4)^2) ≤
      (512*factorialMuntzTailPrimitiveBudget/((n+1 : ℕ) : ℝ)^2)*
        ∫ x : ℝ, factorialMuntzSmoothedTail n k x^2 := by
  filter_upwards [factorialMuntzSmoothedTail_sq_integral_eventually_lower n] with k hk
  calc
    _ ≤ factorialMuntzTailPrimitiveBudget/((n+1 : ℕ) : ℝ)^3 :=
      factorialMuntzSmoothedTail_primitive_mass_bound n k
    _ = (512*factorialMuntzTailPrimitiveBudget/((n+1 : ℕ) : ℝ)^2)*
        (1/(512*((n+1 : ℕ) : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (by
      have := factorialMuntzTailPrimitiveBudget_pos
      positivity)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
