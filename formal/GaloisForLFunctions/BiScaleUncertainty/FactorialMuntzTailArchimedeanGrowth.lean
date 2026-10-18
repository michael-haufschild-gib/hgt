import GaloisForLFunctions.BiScaleUncertainty.ExpDecayFourierMass
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPrimitiveEnergy
import GaloisForLFunctions.RHTower.WeilPoleWeightAtMostOne

/-! Logarithmic archimedean growth of the actual noncompact corrected tails. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23
noncomputable section
set_option autoImplicit false

def factorialMuntzTailArchEnergy (n k : ℕ) : ℝ :=
  1/(2*Real.pi)*(∫ r : ℝ,
    ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2*EF.gammaBracket r)

def factorialMuntzTailArchLoss : ℝ :=
  ExposingRayPrimitive.coercivityConst+64*factorialMuntzTailPrimitiveBudget/Real.pi

theorem factorialMuntzSmoothedTail_fourier_mass_eq (n k : ℕ) :
    (∫ r : ℝ, ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2) =
      2*Real.pi*(∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) :=
  expDecayTest_fourier_mass_eq (factorialMuntzSmoothedTail_expDecayTest n k)

theorem factorialMuntzSmoothedTail_arch_integrable (n k : ℕ) :
    Integrable (fun r : ℝ =>
      ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2*EF.gammaBracket r) :=
  expDecayTest_fourier_sq_gamma_integrable (factorialMuntzSmoothedTail_expDecayTest n k)

/-- The scalar quarter estimate applies to the actual noncompact source,
with Fourier, primitive, and archimedean integrability all discharged. -/
theorem factorialMuntzSmoothedTail_arch_quarter (n k : ℕ) (b : ℝ) :
    (b-ExposingRayPrimitive.coercivityConst+1/4)*
        (∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) ≤
      factorialMuntzTailArchEnergy n k+Real.exp b^4/(8*Real.pi)*
        (∫ r : ℝ, ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2/
          (r^2+1/4)^2) := by
  have hiM := expDecayTest_fourier_sq_integrable (factorialMuntzSmoothedTail_expDecayTest n k)
  have hiP := factorialMuntzSmoothedTail_primitive_integrable n k
  have hiA := factorialMuntzSmoothedTail_arch_integrable n k
  have hb (r : ℝ) : (b-ExposingRayPrimitive.coercivityConst+1/4)*
      ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2 ≤
      ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2*EF.gammaBracket r+
        Real.exp b^4/4*(‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2/
          (r^2+1/4)^2) := by
    have hd : (r^2+(1 : ℝ)/4)^2 ≠ 0 := by positivity
    have h := mul_le_mul_of_nonneg_right
      (exposing_archimedean_scalar_quarter (Real.exp_pos b) r)
      (div_nonneg (sq_nonneg ‖paperFT (fun x =>
        (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖) (sq_nonneg (r^2+1/4)))
    rw [Real.log_exp, ← WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol] at h
    dsimp [ExposingRayPrimitive.coercivityConst]
    convert h using 1 <;> first | rfl | field_simp [hd]
  have h := integral_mono (hiM.const_mul _) (hiA.add (hiP.const_mul _)) hb
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hiA (hiP.const_mul _), integral_const_mul,
    factorialMuntzSmoothedTail_fourier_mass_eq] at h
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < 2*Real.pi by positivity)).mp
  dsimp [factorialMuntzTailArchEnergy]
  convert h using 1 <;> first | rfl | field_simp [Real.pi_ne_zero]
  all_goals ring_nf

private theorem exp_log_half_pow_four {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x/2)^4 = x^2 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 4*(Real.log x/2) = Real.log (x^2) by rw [Real.log_pow]; norm_num; ring,
    Real.exp_log (by positivity)]

/-- The explicit lattice cancellation forces logarithmic archimedean growth
relative to the actual source mass. The smoothing threshold may depend on n. -/
theorem factorialMuntzSmoothedTail_arch_log_lower (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (Real.log ((n+1 : ℕ) : ℝ)/2-factorialMuntzTailArchLoss)*
        (∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) ≤ factorialMuntzTailArchEnergy n k := by
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hC := factorialMuntzTailPrimitiveBudget_pos
  filter_upwards [factorialMuntzSmoothedTail_sq_integral_eventually_lower n] with k hk
  have hq := factorialMuntzSmoothedTail_arch_quarter n k (Real.log ((n+1 : ℕ) : ℝ)/2)
  rw [exp_log_half_pow_four hN] at hq
  have hp : (((n+1 : ℕ) : ℝ)^2/(8*Real.pi))*
      (∫ r : ℝ, ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (r : ℂ)‖^2/
        (r^2+1/4)^2) ≤ factorialMuntzTailPrimitiveBudget/(8*Real.pi*((n+1 : ℕ) : ℝ)) := by
    calc
      _ ≤ (((n+1 : ℕ) : ℝ)^2/(8*Real.pi))*
          (factorialMuntzTailPrimitiveBudget/((n+1 : ℕ) : ℝ)^3) :=
        mul_le_mul_of_nonneg_left (factorialMuntzSmoothedTail_primitive_mass_bound n k) (by positivity)
      _ = _ := by field_simp
  have hm : factorialMuntzTailPrimitiveBudget/(8*Real.pi*((n+1 : ℕ) : ℝ)) ≤
      (64*factorialMuntzTailPrimitiveBudget/Real.pi)*
        (∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) := by
    calc
      _ = (64*factorialMuntzTailPrimitiveBudget/Real.pi)*(1/(512*((n+1 : ℕ) : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)
  have hm0 : 0 ≤ ∫ x : ℝ, factorialMuntzSmoothedTail n k x^2 :=
    integral_nonneg fun x => sq_nonneg _
  unfold factorialMuntzTailArchLoss
  nlinarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
