import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalPrimeChannelScaleWindows
import GaloisForLFunctions.RHTower.FactorialCriticalWindowAffineEnergy

/-! Support-independent harmonic bounds for the complete critical weight.
The smooth collar, endpoint jump and endpoint remainder retain their separate
operator estimates before the harmonic series is truncated. -/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- Constant controlling each critical harmonic bilinear form. -/
def criticalWindowHarmonicBound : ℝ := windowCollarUniform + windowEndpointUniform

theorem criticalWindowHarmonicBound_nonneg : 0 ≤ criticalWindowHarmonicBound :=
  add_nonneg windowCollarUniform_nonneg windowEndpointUniform_nonneg

theorem criticalWindowWeight_cosine_split :
    weightCosineTransform criticalWindowWeight = fun f =>
      weightCosineTransform criticalCollarWeight f +
        (dyadicJumpKernel f + criticalEndpointRemainder f) := by
  funext f
  have hc : IntegrableOn (fun v => criticalCollarWeight v *
      Real.cos (2 * Real.pi * f * v)) (Ioi 1) :=
    integrableOn_criticalCollarWeight.mul_bdd (by fun_prop)
      (Eventually.of_forall fun v => by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * f * v))
  have he : IntegrableOn (fun v => criticalEndpointWeight v *
      Real.cos (2 * Real.pi * f * v)) (Ioi 1) :=
    integrableOn_criticalEndpointWeight.mul_bdd (by fun_prop)
      (Eventually.of_forall fun v => by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * f * v))
  have hsplit : weightCosineTransform criticalWindowWeight f =
      weightCosineTransform criticalCollarWeight f +
        weightCosineTransform criticalEndpointWeight f := by
    unfold weightCosineTransform
    rw [← integral_add hc he]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [← add_mul, criticalCollarWeight_add_criticalEndpointWeight
      (zero_lt_one.trans hv)]
    rfl
  rw [hsplit]
  unfold criticalEndpointRemainder
  ring

/-- Every complete critical harmonic kernel has an operator bound independent
of the number, location and diameter of the source scales. -/
theorem abs_bilinear_criticalWindowKernel_le (S : Finset ℕ) (b : ℕ → ℝ)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    |∑ n ∈ S, ∑ m ∈ S, b n * b m *
      dyadicCrossKernel (weightCosineTransform criticalWindowWeight) p q n m| ≤
      criticalWindowHarmonicBound * ∑ n ∈ S, b n ^ 2 := by
  have hc := abs_bilinear_dyadicCrossKernel_le_uniform
    abs_weightCosineTransform_criticalCollarWeight_le
    (fun f hf => abs_weightCosineTransform_criticalCollarWeight_le_div_sq hf)
    criticalCollarCurvature_nonneg S hp hq b
  have hj := abs_bilinear_dyadicCrossKernel_jump_le_uniform S hp hq b
  have he := abs_bilinear_dyadicCrossKernel_le_uniform abs_criticalEndpointRemainder_le
    (fun f hf => abs_criticalEndpointRemainder_le_div_sq hf)
    criticalEndpointCurvature_nonneg S hp hq b
  rw [criticalWindowWeight_cosine_split]
  simp_rw [dyadicCrossKernel_add, mul_add, Finset.sum_add_distrib]
  refine (abs_add_le _ _).trans ((add_le_add hc
    ((abs_add_le _ _).trans (add_le_add hj he))).trans_eq ?_)
  unfold criticalWindowHarmonicBound windowCollarUniform windowEndpointUniform
  ring

/-- Uniform control of one pair of harmonics, including an arbitrary integer dilation. -/
theorem abs_integral_criticalWindowWeight_harmonics_le (S : Finset ℕ) (b : ℕ → ℝ)
    {k l r : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hr : 1 ≤ r) :
    |∫ v in Ioi 1, criticalWindowWeight v *
      (realHarmonicLayer S b k v * realHarmonicLayer S b l (r * v))| ≤
      criticalWindowHarmonicBound * ∑ n ∈ S, b n ^ 2 := by
  rw [integral_mul_realHarmonicLayer_mul_dilate integrableOn_criticalWindowWeight]
  exact abs_bilinear_criticalWindowKernel_le S b (by exact_mod_cast hk)
    (by exact_mod_cast Nat.mul_le_mul hl hr)

/-- Critical square mass of every harmonic is bounded by the same coefficient norm. -/
theorem integral_criticalWindowWeight_harmonic_sq_le (S : Finset ℕ) (b : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    (∫ v in Ioi 1, criticalWindowWeight v * realHarmonicLayer S b k v ^ 2) ≤
      criticalWindowHarmonicBound * ∑ n ∈ S, b n ^ 2 := by
  have h := abs_integral_criticalWindowWeight_harmonics_le S b hk hk (r := 1) le_rfl
  simp only [Nat.cast_one, one_mul, ← pow_two] at h
  exact (le_abs_self _).trans h

/-- Decay coefficient for the complete critical cosine transform. -/
def criticalWindowCosineDecay : ℝ :=
  criticalCollarCurvature + criticalEndpointCurvature + 1 / (2 * Real.pi)

theorem criticalWindowCosineDecay_nonneg : 0 ≤ criticalWindowCosineDecay := by
  unfold criticalWindowCosineDecay
  exact add_nonneg (add_nonneg criticalCollarCurvature_nonneg
    criticalEndpointCurvature_nonneg) (by positivity)

/-- Away from zero, the endpoint jump determines the slowest cosine-transform decay. -/
theorem abs_criticalWindowWeight_cosine_le_inv {f : ℝ} (hf : 1 ≤ |f|) :
    |weightCosineTransform criticalWindowWeight f| ≤ criticalWindowCosineDecay / |f| := by
  have hf0 : 0 < |f| := lt_of_lt_of_le zero_lt_one hf
  have hfn : f ≠ 0 := abs_pos.mp hf0
  have hsq : |f| ≤ f ^ 2 := by nlinarith [sq_abs f]
  have hc := (abs_weightCosineTransform_criticalCollarWeight_le_div_sq hfn).trans
    (div_le_div_of_nonneg_left criticalCollarCurvature_nonneg hf0 hsq)
  have he := (abs_criticalEndpointRemainder_le_div_sq hfn).trans
    (div_le_div_of_nonneg_left criticalEndpointCurvature_nonneg hf0 hsq)
  have hj := abs_dyadicJumpKernel_le_inv hfn
  rw [criticalWindowWeight_cosine_split]
  refine (abs_add_le _ _).trans ((add_le_add hc
    ((abs_add_le _ _).trans (add_le_add hj he))).trans_eq ?_)
  unfold criticalWindowCosineDecay
  field_simp
  ring

end GaloisForLFunctions.ArithmeticPositivityTheory
